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
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_noption_get(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_NumApps_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_NumApps_visit___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v_val_43_; size_t v___x_44_; size_t v___x_45_; uint8_t v___x_46_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v___x_44_ = lean_ptr_addr(v_val_43_);
v___x_45_ = lean_ptr_addr(v_query_2_);
v___x_46_ = lean_usize_dec_eq(v___x_44_, v___x_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
lean_dec(v_val_43_);
v___x_47_ = lean_array_get_size(v_keyArray_17_);
v___x_48_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_49_ = lean_nat_dec_lt(v___x_48_, v___x_47_);
if (v___x_49_ == 0)
{
lean_dec(v___x_48_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_48_;
goto _start;
}
}
else
{
lean_object* v_val_52_; lean_object* v___x_53_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
lean_inc(v___x_41_);
v_val_52_ = lean_noption_get(v___x_41_);
v___x_53_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_53_, 0, v_x_5_);
lean_ctor_set(v___x_53_, 1, v_val_43_);
lean_ctor_set(v___x_53_, 2, v_val_52_);
return v___x_53_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4___redArg___boxed(lean_object* v_m_54_, lean_object* v_query_55_, lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4___redArg(v_m_54_, v_query_55_, v_x_56_, v_x_57_, v_x_58_);
lean_dec_ref(v_query_55_);
lean_dec_ref(v_m_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___redArg(lean_object* v_m_60_, lean_object* v_query_61_){
_start:
{
lean_object* v_keyArray_62_; lean_object* v___x_63_; size_t v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v_fold_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_keyArray_62_ = lean_ctor_get(v_m_60_, 1);
v___x_63_ = lean_array_get_size(v_keyArray_62_);
v___x_64_ = lean_ptr_addr(v_query_61_);
v___x_65_ = lean_usize_to_uint64(v___x_64_);
v___x_66_ = 11ULL;
v___x_67_ = lean_uint64_mix_hash(v___x_65_, v___x_66_);
v___x_68_ = 32ULL;
v___x_69_ = lean_uint64_shift_right(v___x_67_, v___x_68_);
v_fold_70_ = lean_uint64_xor(v___x_67_, v___x_69_);
v___x_71_ = 16ULL;
v___x_72_ = lean_uint64_shift_right(v_fold_70_, v___x_71_);
v___x_73_ = lean_uint64_xor(v_fold_70_, v___x_72_);
v___x_74_ = lean_uint64_to_usize(v___x_73_);
v___x_75_ = lean_usize_of_nat(v___x_63_);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_sub(v___x_75_, v___x_76_);
v___x_78_ = lean_usize_land(v___x_74_, v___x_77_);
v___x_79_ = lean_usize_to_nat(v___x_78_);
v___x_80_ = lean_box(0);
v___x_81_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4___redArg(v_m_60_, v_query_61_, v___x_80_, v___x_63_, v___x_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___redArg___boxed(lean_object* v_m_82_, lean_object* v_query_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___redArg(v_m_82_, v_query_83_);
lean_dec_ref(v_query_83_);
lean_dec_ref(v_m_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7___redArg(lean_object* v_b_85_, lean_object* v_acc_86_, lean_object* v_i_87_){
_start:
{
lean_object* v___y_89_; lean_object* v_keyArray_97_; lean_object* v_valueArray_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_keyArray_97_ = lean_ctor_get(v_b_85_, 1);
v_valueArray_98_ = lean_ctor_get(v_b_85_, 2);
v___x_99_ = lean_array_get_size(v_keyArray_97_);
v___x_100_ = lean_nat_dec_lt(v_i_87_, v___x_99_);
if (v___x_100_ == 0)
{
lean_dec(v_i_87_);
return v_acc_86_;
}
else
{
lean_object* v___x_101_; uint8_t v_isSome_102_; 
v___x_101_ = lean_array_fget_borrowed(v_keyArray_97_, v_i_87_);
v_isSome_102_ = lean_noption_is_some(v___x_101_);
if (v_isSome_102_ == 0)
{
goto v___jp_93_;
}
else
{
lean_object* v___x_103_; uint8_t v_isSome_104_; 
v___x_103_ = lean_array_fget_borrowed(v_valueArray_98_, v_i_87_);
v_isSome_104_ = lean_noption_is_some(v___x_103_);
if (v_isSome_104_ == 0)
{
goto v___jp_93_;
}
else
{
lean_object* v_val_105_; lean_object* v_val_106_; lean_object* v_i_108_; lean_object* v___x_113_; 
lean_inc(v___x_101_);
v_val_105_ = lean_noption_get(v___x_101_);
lean_inc(v___x_103_);
v_val_106_ = lean_noption_get(v___x_103_);
v___x_113_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___redArg(v_acc_86_, v_val_105_);
switch(lean_obj_tag(v___x_113_))
{
case 0:
{
lean_object* v_index_114_; lean_object* v_size_115_; lean_object* v___x_116_; 
v_index_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_index_114_);
lean_dec_ref_known(v___x_113_, 3);
v_size_115_ = lean_ctor_get(v_acc_86_, 0);
lean_inc(v_size_115_);
v___x_116_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_86_, v_size_115_, v_index_114_, v_val_105_, v_val_106_);
lean_dec(v_index_114_);
v___y_89_ = v___x_116_;
goto v___jp_88_;
}
case 1:
{
lean_object* v_index_117_; 
v_index_117_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_index_117_);
lean_dec_ref_known(v___x_113_, 1);
v_i_108_ = v_index_117_;
goto v___jp_107_;
}
default: 
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_86_, v___x_118_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_index_120_; 
v_index_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_index_120_);
lean_dec_ref_known(v___x_119_, 1);
v_i_108_ = v_index_120_;
goto v___jp_107_;
}
else
{
lean_dec(v_val_106_);
lean_dec(v_val_105_);
v___y_89_ = v_acc_86_;
goto v___jp_88_;
}
}
}
v___jp_107_:
{
lean_object* v_size_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_size_109_ = lean_ctor_get(v_acc_86_, 0);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_add(v_size_109_, v___x_110_);
v___x_112_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_86_, v___x_111_, v_i_108_, v_val_105_, v_val_106_);
lean_dec(v_i_108_);
v___y_89_ = v___x_112_;
goto v___jp_88_;
}
}
}
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_add(v_i_87_, v___x_90_);
lean_dec(v_i_87_);
v_acc_86_ = v___y_89_;
v_i_87_ = v___x_91_;
goto _start;
}
v___jp_93_:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_nat_add(v_i_87_, v___x_94_);
lean_dec(v_i_87_);
v_i_87_ = v___x_95_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_b_121_, lean_object* v_acc_122_, lean_object* v_i_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7___redArg(v_b_121_, v_acc_122_, v_i_123_);
lean_dec_ref(v_b_121_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6___redArg(lean_object* v_init_125_, lean_object* v_b_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7___redArg(v_b_126_, v_init_125_, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6___redArg___boxed(lean_object* v_init_129_, lean_object* v_b_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6___redArg(v_init_129_, v_b_130_);
lean_dec_ref(v_b_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4___redArg(lean_object* v_m_132_){
_start:
{
lean_object* v_keyArray_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_cellCount_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_target_140_; lean_object* v___x_141_; 
v_keyArray_133_ = lean_ctor_get(v_m_132_, 1);
v___x_134_ = lean_array_get_size(v_keyArray_133_);
v___x_135_ = lean_unsigned_to_nat(2u);
v_cellCount_136_ = lean_nat_mul(v___x_134_, v___x_135_);
v___x_137_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_136_);
v___x_138_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_136_);
v___x_139_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_136_);
v_target_140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_140_, 0, v___x_137_);
lean_ctor_set(v_target_140_, 1, v___x_138_);
lean_ctor_set(v_target_140_, 2, v___x_139_);
v___x_141_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6___redArg(v_target_140_, v_m_132_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4___redArg___boxed(lean_object* v_m_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4___redArg(v_m_142_);
lean_dec_ref(v_m_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(lean_object* v_m_144_, lean_object* v_query_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___redArg(v_m_144_, v_query_145_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_index_147_; lean_object* v_key_148_; lean_object* v_value_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_index_147_ = lean_ctor_get(v___x_146_, 0);
v_key_148_ = lean_ctor_get(v___x_146_, 1);
v_value_149_ = lean_ctor_get(v___x_146_, 2);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_146_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_value_149_);
lean_inc(v_key_148_);
lean_inc(v_index_147_);
lean_dec(v___x_146_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_index_147_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_key_148_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_value_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_object* v___x_157_; 
lean_dec(v___x_146_);
v___x_157_ = lean_box(1);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg___boxed(lean_object* v_m_158_, lean_object* v_query_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_m_158_, v_query_159_);
lean_dec_ref(v_query_159_);
lean_dec_ref(v_m_158_);
return v_res_160_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(lean_object* v_m_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_m_161_, v_a_162_);
if (lean_obj_tag(v___x_163_) == 0)
{
uint8_t v___x_164_; 
lean_dec_ref_known(v___x_163_, 3);
v___x_164_ = 1;
return v___x_164_;
}
else
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg___boxed(lean_object* v_m_166_, lean_object* v_a_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_166_, v_a_167_);
lean_dec_ref(v_a_167_);
lean_dec_ref(v_m_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_visit___closed__0(void){
_start:
{
lean_object* v___x_170_; lean_object* v_dummy_171_; 
v___x_170_ = lean_box(0);
v_dummy_171_ = l_Lean_Expr_sort___override(v___x_170_);
return v_dummy_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__2(lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___y_177_; 
if (lean_obj_tag(v_x_172_) == 5)
{
lean_object* v_fn_202_; lean_object* v_arg_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_fn_202_ = lean_ctor_get(v_x_172_, 0);
lean_inc_ref(v_fn_202_);
v_arg_203_ = lean_ctor_get(v_x_172_, 1);
lean_inc_ref(v_arg_203_);
lean_dec_ref_known(v_x_172_, 2);
v___x_204_ = lean_array_set(v_x_173_, v_x_174_, v_arg_203_);
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_sub(v_x_174_, v___x_205_);
lean_dec(v_x_174_);
v_x_172_ = v_fn_202_;
v_x_173_ = v___x_204_;
v_x_174_ = v___x_206_;
goto _start;
}
else
{
lean_dec(v_x_174_);
if (lean_obj_tag(v_x_172_) == 4)
{
lean_object* v_declName_208_; lean_object* v_visited_209_; lean_object* v_counters_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_225_; 
v_declName_208_ = lean_ctor_get(v_x_172_, 0);
v_visited_209_ = lean_ctor_get(v___y_175_, 0);
v_counters_210_ = lean_ctor_get(v___y_175_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v___y_175_);
if (v_isSharedCheck_225_ == 0)
{
v___x_212_ = v___y_175_;
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_counters_210_);
lean_inc(v_visited_209_);
lean_dec(v___y_175_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___y_215_; lean_object* v___x_222_; 
v___x_222_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_counters_210_, v_declName_208_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v___y_215_ = v___x_223_;
goto v___jp_214_;
}
else
{
lean_object* v_val_224_; 
v_val_224_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_222_, 1);
v___y_215_ = v_val_224_;
goto v___jp_214_;
}
v___jp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_add(v___y_215_, v___x_216_);
lean_dec(v___y_215_);
lean_inc(v_declName_208_);
v___x_218_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_208_, v___x_217_, v_counters_210_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___x_218_);
v___x_220_ = v___x_212_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_visited_209_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
v___y_177_ = v___x_220_;
goto v___jp_176_;
}
}
}
}
else
{
v___y_177_ = v___y_175_;
goto v___jp_176_;
}
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v_snd_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_200_; 
v___x_178_ = l_Lean_Expr_NumApps_visit(v_x_172_, v___y_177_);
v_snd_179_ = lean_ctor_get(v___x_178_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v___x_178_, 0);
lean_dec(v_unused_201_);
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_200_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_snd_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_200_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_array_get_size(v_x_173_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_nat_dec_lt(v___x_183_, v___x_184_);
if (v___x_186_ == 0)
{
lean_object* v___x_188_; 
lean_dec_ref(v_x_173_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_185_);
v___x_188_ = v___x_181_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_snd_179_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
else
{
uint8_t v___x_190_; 
v___x_190_ = lean_nat_dec_le(v___x_184_, v___x_184_);
if (v___x_190_ == 0)
{
if (v___x_186_ == 0)
{
lean_object* v___x_192_; 
lean_dec_ref(v_x_173_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_185_);
v___x_192_ = v___x_181_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_snd_179_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
else
{
size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; 
lean_del_object(v___x_181_);
v___x_194_ = ((size_t)0ULL);
v___x_195_ = lean_usize_of_nat(v___x_184_);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_x_173_, v___x_194_, v___x_195_, v___x_185_, v_snd_179_);
lean_dec_ref(v_x_173_);
return v___x_196_;
}
}
else
{
size_t v___x_197_; size_t v___x_198_; lean_object* v___x_199_; 
lean_del_object(v___x_181_);
v___x_197_ = ((size_t)0ULL);
v___x_198_ = lean_usize_of_nat(v___x_184_);
v___x_199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_x_173_, v___x_197_, v___x_198_, v___x_185_, v_snd_179_);
lean_dec_ref(v_x_173_);
return v___x_199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_visit(lean_object* v_e_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_d_229_; lean_object* v_b_230_; lean_object* v___y_231_; lean_object* v_visited_235_; lean_object* v_counters_236_; lean_object* v___y_238_; uint8_t v___x_264_; 
v_visited_235_ = lean_ctor_get(v_a_227_, 0);
v_counters_236_ = lean_ctor_get(v_a_227_, 1);
v___x_264_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_visited_235_, v_e_226_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___y_267_; lean_object* v_i_268_; lean_object* v___y_274_; lean_object* v___y_284_; lean_object* v_i_285_; lean_object* v___x_300_; 
lean_inc(v_counters_236_);
lean_inc_ref(v_visited_235_);
lean_dec_ref(v_a_227_);
v___x_265_ = lean_box(0);
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___redArg(v_visited_235_, v_e_226_);
switch(lean_obj_tag(v___x_300_))
{
case 0:
{
lean_dec_ref_known(v___x_300_, 3);
v___y_238_ = v_visited_235_;
goto v___jp_237_;
}
case 1:
{
lean_object* v_index_301_; lean_object* v_size_302_; lean_object* v_keyArray_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_index_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_index_301_);
lean_dec_ref_known(v___x_300_, 1);
v_size_302_ = lean_ctor_get(v_visited_235_, 0);
v_keyArray_303_ = lean_ctor_get(v_visited_235_, 1);
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_add(v_size_302_, v___x_304_);
v___x_306_ = lean_array_get_size(v_keyArray_303_);
v___x_307_ = lean_nat_dec_lt(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_dec(v___x_305_);
lean_dec(v_index_301_);
goto v___jp_290_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_308_ = lean_unsigned_to_nat(4u);
v___x_309_ = lean_nat_mul(v___x_305_, v___x_308_);
v___x_310_ = lean_unsigned_to_nat(3u);
v___x_311_ = lean_nat_mul(v___x_306_, v___x_310_);
v___x_312_ = lean_nat_dec_le(v___x_309_, v___x_311_);
lean_dec(v___x_311_);
lean_dec(v___x_309_);
if (v___x_312_ == 0)
{
lean_dec(v___x_305_);
lean_dec(v_index_301_);
goto v___jp_290_;
}
else
{
lean_object* v___x_313_; 
lean_inc_ref(v_e_226_);
v___x_313_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visited_235_, v___x_305_, v_index_301_, v_e_226_, v___x_265_);
lean_dec(v_index_301_);
v___y_238_ = v___x_313_;
goto v___jp_237_;
}
}
}
default: 
{
lean_object* v_size_314_; lean_object* v_keyArray_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v_size_314_ = lean_ctor_get(v_visited_235_, 0);
v_keyArray_315_ = lean_ctor_get(v_visited_235_, 1);
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_add(v_size_314_, v___x_316_);
v___x_318_ = lean_array_get_size(v_keyArray_315_);
v___x_319_ = lean_nat_dec_lt(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_dec(v___x_317_);
v___x_320_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4___redArg(v_visited_235_);
lean_dec_ref(v_visited_235_);
v___y_274_ = v___x_320_;
goto v___jp_273_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_321_ = lean_unsigned_to_nat(4u);
v___x_322_ = lean_nat_mul(v___x_317_, v___x_321_);
lean_dec(v___x_317_);
v___x_323_ = lean_unsigned_to_nat(3u);
v___x_324_ = lean_nat_mul(v___x_318_, v___x_323_);
v___x_325_ = lean_nat_dec_le(v___x_322_, v___x_324_);
lean_dec(v___x_324_);
lean_dec(v___x_322_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4___redArg(v_visited_235_);
lean_dec_ref(v_visited_235_);
v___y_274_ = v___x_326_;
goto v___jp_273_;
}
else
{
v___y_274_ = v_visited_235_;
goto v___jp_273_;
}
}
}
}
v___jp_266_:
{
lean_object* v_size_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_size_269_ = lean_ctor_get(v___y_267_, 0);
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_size_269_, v___x_270_);
lean_inc_ref(v_e_226_);
v___x_272_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_267_, v___x_271_, v_i_268_, v_e_226_, v___x_265_);
lean_dec(v_i_268_);
v___y_238_ = v___x_272_;
goto v___jp_237_;
}
v___jp_273_:
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___redArg(v___y_274_, v_e_226_);
switch(lean_obj_tag(v___x_275_))
{
case 0:
{
lean_object* v_index_276_; lean_object* v_size_277_; lean_object* v___x_278_; 
v_index_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_index_276_);
lean_dec_ref_known(v___x_275_, 3);
v_size_277_ = lean_ctor_get(v___y_274_, 0);
lean_inc(v_size_277_);
lean_inc_ref(v_e_226_);
v___x_278_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_274_, v_size_277_, v_index_276_, v_e_226_, v___x_265_);
lean_dec(v_index_276_);
v___y_238_ = v___x_278_;
goto v___jp_237_;
}
case 1:
{
lean_object* v_index_279_; 
v_index_279_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_index_279_);
lean_dec_ref_known(v___x_275_, 1);
v___y_267_ = v___y_274_;
v_i_268_ = v_index_279_;
goto v___jp_266_;
}
default: 
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_274_, v___x_280_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_index_282_; 
v_index_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_index_282_);
lean_dec_ref_known(v___x_281_, 1);
v___y_267_ = v___y_274_;
v_i_268_ = v_index_282_;
goto v___jp_266_;
}
else
{
v___y_238_ = v___y_274_;
goto v___jp_237_;
}
}
}
}
v___jp_283_:
{
lean_object* v_size_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_size_286_ = lean_ctor_get(v___y_284_, 0);
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_add(v_size_286_, v___x_287_);
lean_inc_ref(v_e_226_);
v___x_289_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_284_, v___x_288_, v_i_285_, v_e_226_, v___x_265_);
lean_dec(v_i_285_);
v___y_238_ = v___x_289_;
goto v___jp_237_;
}
v___jp_290_:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4___redArg(v_visited_235_);
lean_dec_ref(v_visited_235_);
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___redArg(v___x_291_, v_e_226_);
switch(lean_obj_tag(v___x_292_))
{
case 0:
{
lean_object* v_index_293_; lean_object* v_size_294_; lean_object* v___x_295_; 
v_index_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_index_293_);
lean_dec_ref_known(v___x_292_, 3);
v_size_294_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_size_294_);
lean_inc_ref(v_e_226_);
v___x_295_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_291_, v_size_294_, v_index_293_, v_e_226_, v___x_265_);
lean_dec(v_index_293_);
v___y_238_ = v___x_295_;
goto v___jp_237_;
}
case 1:
{
lean_object* v_index_296_; 
v_index_296_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_index_296_);
lean_dec_ref_known(v___x_292_, 1);
v___y_284_ = v___x_291_;
v_i_285_ = v_index_296_;
goto v___jp_283_;
}
default: 
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_291_, v___x_297_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_index_299_; 
v_index_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_index_299_);
lean_dec_ref_known(v___x_298_, 1);
v___y_284_ = v___x_291_;
v_i_285_ = v_index_299_;
goto v___jp_283_;
}
else
{
v___y_238_ = v___x_291_;
goto v___jp_237_;
}
}
}
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec_ref(v_e_226_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v_a_227_);
return v___x_328_;
}
v___jp_228_:
{
lean_object* v___x_232_; lean_object* v_snd_233_; 
v___x_232_ = l_Lean_Expr_NumApps_visit(v_d_229_, v___y_231_);
v_snd_233_ = lean_ctor_get(v___x_232_, 1);
lean_inc(v_snd_233_);
lean_dec_ref(v___x_232_);
v_e_226_ = v_b_230_;
v_a_227_ = v_snd_233_;
goto _start;
}
v___jp_237_:
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___y_238_);
lean_ctor_set(v___x_239_, 1, v_counters_236_);
switch(lean_obj_tag(v_e_226_))
{
case 7:
{
lean_object* v_binderType_240_; lean_object* v_body_241_; 
v_binderType_240_ = lean_ctor_get(v_e_226_, 1);
lean_inc_ref(v_binderType_240_);
v_body_241_ = lean_ctor_get(v_e_226_, 2);
lean_inc_ref(v_body_241_);
lean_dec_ref_known(v_e_226_, 3);
v_d_229_ = v_binderType_240_;
v_b_230_ = v_body_241_;
v___y_231_ = v___x_239_;
goto v___jp_228_;
}
case 6:
{
lean_object* v_binderType_242_; lean_object* v_body_243_; 
v_binderType_242_ = lean_ctor_get(v_e_226_, 1);
lean_inc_ref(v_binderType_242_);
v_body_243_ = lean_ctor_get(v_e_226_, 2);
lean_inc_ref(v_body_243_);
lean_dec_ref_known(v_e_226_, 3);
v_d_229_ = v_binderType_242_;
v_b_230_ = v_body_243_;
v___y_231_ = v___x_239_;
goto v___jp_228_;
}
case 10:
{
lean_object* v_expr_244_; 
v_expr_244_ = lean_ctor_get(v_e_226_, 1);
lean_inc_ref(v_expr_244_);
lean_dec_ref_known(v_e_226_, 2);
v_e_226_ = v_expr_244_;
v_a_227_ = v___x_239_;
goto _start;
}
case 8:
{
lean_object* v_type_246_; lean_object* v_value_247_; lean_object* v_body_248_; lean_object* v___x_249_; lean_object* v_snd_250_; lean_object* v___x_251_; lean_object* v_snd_252_; 
v_type_246_ = lean_ctor_get(v_e_226_, 1);
lean_inc_ref(v_type_246_);
v_value_247_ = lean_ctor_get(v_e_226_, 2);
lean_inc_ref(v_value_247_);
v_body_248_ = lean_ctor_get(v_e_226_, 3);
lean_inc_ref(v_body_248_);
lean_dec_ref_known(v_e_226_, 4);
v___x_249_ = l_Lean_Expr_NumApps_visit(v_type_246_, v___x_239_);
v_snd_250_ = lean_ctor_get(v___x_249_, 1);
lean_inc(v_snd_250_);
lean_dec_ref(v___x_249_);
v___x_251_ = l_Lean_Expr_NumApps_visit(v_value_247_, v_snd_250_);
v_snd_252_ = lean_ctor_get(v___x_251_, 1);
lean_inc(v_snd_252_);
lean_dec_ref(v___x_251_);
v_e_226_ = v_body_248_;
v_a_227_ = v_snd_252_;
goto _start;
}
case 5:
{
lean_object* v_dummy_254_; lean_object* v_nargs_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_dummy_254_ = lean_obj_once(&l_Lean_Expr_NumApps_visit___closed__0, &l_Lean_Expr_NumApps_visit___closed__0_once, _init_l_Lean_Expr_NumApps_visit___closed__0);
v_nargs_255_ = l_Lean_Expr_getAppNumArgs(v_e_226_);
lean_inc(v_nargs_255_);
v___x_256_ = lean_mk_array(v_nargs_255_, v_dummy_254_);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_sub(v_nargs_255_, v___x_257_);
lean_dec(v_nargs_255_);
v___x_259_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__2(v_e_226_, v___x_256_, v___x_258_, v___x_239_);
return v___x_259_;
}
case 11:
{
lean_object* v_struct_260_; 
v_struct_260_ = lean_ctor_get(v_e_226_, 2);
lean_inc_ref(v_struct_260_);
lean_dec_ref_known(v_e_226_, 3);
v_e_226_ = v_struct_260_;
v_a_227_ = v___x_239_;
goto _start;
}
default: 
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec_ref(v_e_226_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_239_);
return v___x_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_, lean_object* v_b_332_, lean_object* v___y_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = lean_usize_dec_eq(v_i_330_, v_stop_331_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_fst_337_; lean_object* v_snd_338_; size_t v___x_339_; size_t v___x_340_; 
v___x_335_ = lean_array_uget_borrowed(v_as_329_, v_i_330_);
lean_inc(v___x_335_);
v___x_336_ = l_Lean_Expr_NumApps_visit(v___x_335_, v___y_333_);
v_fst_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_fst_337_);
v_snd_338_ = lean_ctor_get(v___x_336_, 1);
lean_inc(v_snd_338_);
lean_dec_ref(v___x_336_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_add(v_i_330_, v___x_339_);
v_i_330_ = v___x_340_;
v_b_332_ = v_fst_337_;
v___y_333_ = v_snd_338_;
goto _start;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_b_332_);
lean_ctor_set(v___x_342_, 1, v___y_333_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0___boxed(lean_object* v_as_343_, lean_object* v_i_344_, lean_object* v_stop_345_, lean_object* v_b_346_, lean_object* v___y_347_){
_start:
{
size_t v_i_boxed_348_; size_t v_stop_boxed_349_; lean_object* v_res_350_; 
v_i_boxed_348_ = lean_unbox_usize(v_i_344_);
lean_dec(v_i_344_);
v_stop_boxed_349_ = lean_unbox_usize(v_stop_345_);
lean_dec(v_stop_345_);
v_res_350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_as_343_, v_i_boxed_348_, v_stop_boxed_349_, v_b_346_, v___y_347_);
lean_dec_ref(v_as_343_);
return v_res_350_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(lean_object* v_00_u03b2_351_, lean_object* v_m_352_, lean_object* v_a_353_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_352_, v_a_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___boxed(lean_object* v_00_u03b2_355_, lean_object* v_m_356_, lean_object* v_a_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(v_00_u03b2_355_, v_m_356_, v_a_357_);
lean_dec_ref(v_a_357_);
lean_dec_ref(v_m_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3(lean_object* v_00_u03b2_360_, lean_object* v_m_361_, lean_object* v_query_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___redArg(v_m_361_, v_query_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3___boxed(lean_object* v_00_u03b2_364_, lean_object* v_m_365_, lean_object* v_query_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3(v_00_u03b2_364_, v_m_365_, v_query_366_);
lean_dec_ref(v_query_366_);
lean_dec_ref(v_m_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4(lean_object* v_00_u03b2_368_, lean_object* v_m_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4___redArg(v_m_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4___boxed(lean_object* v_00_u03b2_371_, lean_object* v_m_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4(v_00_u03b2_371_, v_m_372_);
lean_dec_ref(v_m_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(lean_object* v_00_u03b2_374_, lean_object* v_m_375_, lean_object* v_query_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_m_375_, v_query_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_378_, lean_object* v_m_379_, lean_object* v_query_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(v_00_u03b2_378_, v_m_379_, v_query_380_);
lean_dec_ref(v_query_380_);
lean_dec_ref(v_m_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4(lean_object* v_00_u03b2_382_, lean_object* v_m_383_, lean_object* v_query_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4___redArg(v_m_383_, v_query_384_, v_x_385_, v_x_386_, v_x_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4___boxed(lean_object* v_00_u03b2_390_, lean_object* v_m_391_, lean_object* v_query_392_, lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_NumApps_visit_spec__3_spec__4(v_00_u03b2_390_, v_m_391_, v_query_392_, v_x_393_, v_x_394_, v_x_395_, v_x_396_);
lean_dec_ref(v_query_392_);
lean_dec_ref(v_m_391_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6(lean_object* v_00_u03b2_398_, lean_object* v_init_399_, lean_object* v_b_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6___redArg(v_init_399_, v_b_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6___boxed(lean_object* v_00_u03b2_402_, lean_object* v_init_403_, lean_object* v_b_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6(v_00_u03b2_402_, v_init_403_, v_b_404_);
lean_dec_ref(v_b_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_406_, lean_object* v_b_407_, lean_object* v_acc_408_, lean_object* v_i_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7___redArg(v_b_407_, v_acc_408_, v_i_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b2_411_, lean_object* v_b_412_, lean_object* v_acc_413_, lean_object* v_i_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_NumApps_visit_spec__4_spec__6_spec__7(v_00_u03b2_411_, v_b_412_, v_acc_413_, v_i_414_);
lean_dec_ref(v_b_412_);
return v_res_415_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_main___closed__0(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_unsigned_to_nat(64u);
v___x_417_ = l_Lean_mkPtrSet___redArg(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_main___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_box(1);
v___x_419_ = lean_obj_once(&l_Lean_Expr_NumApps_main___closed__0, &l_Lean_Expr_NumApps_main___closed__0_once, _init_l_Lean_Expr_NumApps_main___closed__0);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_main(lean_object* v_e_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_snd_424_; lean_object* v_counters_425_; 
v___x_422_ = lean_obj_once(&l_Lean_Expr_NumApps_main___closed__1, &l_Lean_Expr_NumApps_main___closed__1_once, _init_l_Lean_Expr_NumApps_main___closed__1);
v___x_423_ = l_Lean_Expr_NumApps_visit(v_e_421_, v___x_422_);
v_snd_424_ = lean_ctor_get(v___x_423_, 1);
lean_inc(v_snd_424_);
lean_dec_ref(v___x_423_);
v_counters_425_ = lean_ctor_get(v_snd_424_, 1);
lean_inc(v_counters_425_);
lean_dec(v_snd_424_);
return v_counters_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_NumApps_0__Lean_Expr_numApps_unsafe__1(lean_object* v_e_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Expr_NumApps_main(v_e_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(lean_object* v_threshold_428_, lean_object* v_init_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_d_433_; 
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v_k_436_; lean_object* v_v_437_; lean_object* v_l_438_; lean_object* v_r_439_; lean_object* v___x_440_; lean_object* v_a_441_; 
v_k_436_ = lean_ctor_get(v_x_430_, 1);
v_v_437_ = lean_ctor_get(v_x_430_, 2);
v_l_438_ = lean_ctor_get(v_x_430_, 3);
v_r_439_ = lean_ctor_get(v_x_430_, 4);
v___x_440_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_428_, v_init_429_, v_l_438_);
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
if (lean_obj_tag(v_a_441_) == 0)
{
lean_object* v_a_442_; 
lean_dec_ref(v___x_440_);
v_a_442_ = lean_ctor_get(v_a_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v_a_441_, 1);
v_d_433_ = v_a_442_;
goto v___jp_432_;
}
else
{
lean_object* v_a_443_; uint8_t v___x_444_; 
v_a_443_ = lean_ctor_get(v_a_441_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v_a_441_, 1);
v___x_444_ = lean_nat_dec_lt(v_threshold_428_, v_v_437_);
if (v___x_444_ == 0)
{
lean_object* v_a_445_; 
lean_dec(v_a_443_);
v_a_445_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_445_);
lean_dec_ref(v___x_440_);
if (lean_obj_tag(v_a_445_) == 0)
{
lean_object* v_a_446_; 
v_a_446_ = lean_ctor_get(v_a_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v_a_445_, 1);
v_d_433_ = v_a_446_;
goto v___jp_432_;
}
else
{
lean_object* v_a_447_; 
v_a_447_ = lean_ctor_get(v_a_445_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v_a_445_, 1);
v_init_429_ = v_a_447_;
v_x_430_ = v_r_439_;
goto _start;
}
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec_ref(v___x_440_);
lean_inc(v_v_437_);
lean_inc(v_k_436_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_k_436_);
lean_ctor_set(v___x_449_, 1, v_v_437_);
v___x_450_ = lean_array_push(v_a_443_, v___x_449_);
v_init_429_ = v___x_450_;
v_x_430_ = v_r_439_;
goto _start;
}
}
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v_init_429_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
v___jp_432_:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v_d_433_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1___boxed(lean_object* v_threshold_454_, lean_object* v_init_455_, lean_object* v_x_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_454_, v_init_455_, v_x_456_);
lean_dec(v_x_456_);
lean_dec(v_threshold_454_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(lean_object* v_hi_459_, lean_object* v_pivot_460_, lean_object* v_as_461_, lean_object* v_i_462_, lean_object* v_k_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = lean_nat_dec_lt(v_k_463_, v_hi_459_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec(v_k_463_);
v___x_465_ = lean_array_fswap(v_as_461_, v_i_462_, v_hi_459_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v_i_462_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
return v___x_466_;
}
else
{
lean_object* v_snd_467_; lean_object* v___x_468_; lean_object* v_snd_469_; uint8_t v___x_470_; 
v_snd_467_ = lean_ctor_get(v_pivot_460_, 1);
v___x_468_ = lean_array_fget_borrowed(v_as_461_, v_k_463_);
v_snd_469_ = lean_ctor_get(v___x_468_, 1);
v___x_470_ = lean_nat_dec_lt(v_snd_467_, v_snd_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_add(v_k_463_, v___x_471_);
lean_dec(v_k_463_);
v_k_463_ = v___x_472_;
goto _start;
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = lean_array_fswap(v_as_461_, v_i_462_, v_k_463_);
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_nat_add(v_i_462_, v___x_475_);
lean_dec(v_i_462_);
v___x_477_ = lean_nat_add(v_k_463_, v___x_475_);
lean_dec(v_k_463_);
v_as_461_ = v___x_474_;
v_i_462_ = v___x_476_;
v_k_463_ = v___x_477_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg___boxed(lean_object* v_hi_479_, lean_object* v_pivot_480_, lean_object* v_as_481_, lean_object* v_i_482_, lean_object* v_k_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_479_, v_pivot_480_, v_as_481_, v_i_482_, v_k_483_);
lean_dec_ref(v_pivot_480_);
lean_dec(v_hi_479_);
return v_res_484_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(lean_object* v_a_485_, lean_object* v_b_486_){
_start:
{
lean_object* v_snd_487_; lean_object* v_snd_488_; uint8_t v___x_489_; 
v_snd_487_ = lean_ctor_get(v_b_486_, 1);
v_snd_488_ = lean_ctor_get(v_a_485_, 1);
v___x_489_ = lean_nat_dec_lt(v_snd_487_, v_snd_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0___boxed(lean_object* v_a_490_, lean_object* v_b_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v_a_490_, v_b_491_);
lean_dec_ref(v_b_491_);
lean_dec_ref(v_a_490_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(lean_object* v_n_494_, lean_object* v_as_495_, lean_object* v_lo_496_, lean_object* v_hi_497_){
_start:
{
lean_object* v___y_499_; uint8_t v___x_509_; 
v___x_509_ = lean_nat_dec_lt(v_lo_496_, v_hi_497_);
if (v___x_509_ == 0)
{
lean_dec(v_lo_496_);
return v_as_495_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_mid_512_; lean_object* v___y_514_; lean_object* v___y_520_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_510_ = lean_nat_add(v_lo_496_, v_hi_497_);
v___x_511_ = lean_unsigned_to_nat(1u);
v_mid_512_ = lean_nat_shiftr(v___x_510_, v___x_511_);
lean_dec(v___x_510_);
v___x_525_ = lean_array_fget_borrowed(v_as_495_, v_mid_512_);
v___x_526_ = lean_array_fget_borrowed(v_as_495_, v_lo_496_);
v___x_527_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_525_, v___x_526_);
if (v___x_527_ == 0)
{
v___y_520_ = v_as_495_;
goto v___jp_519_;
}
else
{
lean_object* v___x_528_; 
v___x_528_ = lean_array_fswap(v_as_495_, v_lo_496_, v_mid_512_);
v___y_520_ = v___x_528_;
goto v___jp_519_;
}
v___jp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_515_ = lean_array_fget_borrowed(v___y_514_, v_mid_512_);
v___x_516_ = lean_array_fget_borrowed(v___y_514_, v_hi_497_);
v___x_517_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_dec(v_mid_512_);
v___y_499_ = v___y_514_;
goto v___jp_498_;
}
else
{
lean_object* v___x_518_; 
v___x_518_ = lean_array_fswap(v___y_514_, v_mid_512_, v_hi_497_);
lean_dec(v_mid_512_);
v___y_499_ = v___x_518_;
goto v___jp_498_;
}
}
v___jp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = lean_array_fget_borrowed(v___y_520_, v_hi_497_);
v___x_522_ = lean_array_fget_borrowed(v___y_520_, v_lo_496_);
v___x_523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
v___y_514_ = v___y_520_;
goto v___jp_513_;
}
else
{
lean_object* v___x_524_; 
v___x_524_ = lean_array_fswap(v___y_520_, v_lo_496_, v_hi_497_);
v___y_514_ = v___x_524_;
goto v___jp_513_;
}
}
}
v___jp_498_:
{
lean_object* v_pivot_500_; lean_object* v___x_501_; lean_object* v_fst_502_; lean_object* v_snd_503_; uint8_t v___x_504_; 
v_pivot_500_ = lean_array_fget(v___y_499_, v_hi_497_);
lean_inc_n(v_lo_496_, 2);
v___x_501_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_497_, v_pivot_500_, v___y_499_, v_lo_496_, v_lo_496_);
lean_dec(v_pivot_500_);
v_fst_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_fst_502_);
v_snd_503_ = lean_ctor_get(v___x_501_, 1);
lean_inc(v_snd_503_);
lean_dec_ref(v___x_501_);
v___x_504_ = lean_nat_dec_le(v_hi_497_, v_fst_502_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_494_, v_snd_503_, v_lo_496_, v_fst_502_);
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_fst_502_, v___x_506_);
lean_dec(v_fst_502_);
v_as_495_ = v___x_505_;
v_lo_496_ = v___x_507_;
goto _start;
}
else
{
lean_dec(v_fst_502_);
lean_dec(v_lo_496_);
return v_snd_503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___boxed(lean_object* v_n_529_, lean_object* v_as_530_, lean_object* v_lo_531_, lean_object* v_hi_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_529_, v_as_530_, v_lo_531_, v_hi_532_);
lean_dec(v_hi_532_);
lean_dec(v_n_529_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numApps(lean_object* v_e_536_, lean_object* v_threshold_537_){
_start:
{
lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v_counters_552_; lean_object* v___x_553_; lean_object* v_result_554_; lean_object* v___x_555_; lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_572_; 
v_counters_552_ = l_Lean_Expr_NumApps_main(v_e_536_);
v___x_553_ = lean_unsigned_to_nat(0u);
v_result_554_ = ((lean_object*)(l_Lean_Expr_numApps___closed__0));
v___x_555_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_537_, v_result_554_, v_counters_552_);
lean_dec(v_counters_552_);
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_572_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_572_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_572_;
goto v_resetjp_557_;
}
v___jp_539_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v___y_542_, v___y_540_, v___y_541_, v___y_543_);
lean_dec(v___y_543_);
lean_dec(v___y_542_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
v___jp_546_:
{
uint8_t v___x_551_; 
v___x_551_ = lean_nat_dec_le(v___y_550_, v___y_548_);
if (v___x_551_ == 0)
{
lean_dec(v___y_548_);
lean_inc(v___y_550_);
v___y_540_ = v___y_547_;
v___y_541_ = v___y_550_;
v___y_542_ = v___y_549_;
v___y_543_ = v___y_550_;
goto v___jp_539_;
}
else
{
v___y_540_ = v___y_547_;
v___y_541_ = v___y_550_;
v___y_542_ = v___y_549_;
v___y_543_ = v___y_548_;
goto v___jp_539_;
}
}
v_resetjp_557_:
{
lean_object* v___y_561_; lean_object* v_a_562_; lean_object* v_a_568_; lean_object* v___x_570_; 
v_a_568_ = lean_ctor_get(v_a_556_, 0);
lean_inc_n(v_a_568_, 2);
lean_dec(v_a_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_a_568_);
v___x_570_ = v___x_558_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v___jp_560_:
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = lean_array_get_size(v_a_562_);
v___x_564_ = lean_nat_dec_eq(v___x_563_, v___x_553_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
lean_dec_ref(v___y_561_);
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_sub(v___x_563_, v___x_565_);
v___x_567_ = lean_nat_dec_le(v___x_553_, v___x_566_);
if (v___x_567_ == 0)
{
lean_inc(v___x_566_);
v___y_547_ = v_a_562_;
v___y_548_ = v___x_566_;
v___y_549_ = v___x_563_;
v___y_550_ = v___x_566_;
goto v___jp_546_;
}
else
{
v___y_547_ = v_a_562_;
v___y_548_ = v___x_566_;
v___y_549_ = v___x_563_;
v___y_550_ = v___x_553_;
goto v___jp_546_;
}
}
else
{
lean_dec_ref(v_a_562_);
return v___y_561_;
}
}
v_reusejp_569_:
{
v___y_561_ = v___x_570_;
v_a_562_ = v_a_568_;
goto v___jp_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numApps___boxed(lean_object* v_e_573_, lean_object* v_threshold_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Expr_numApps(v_e_573_, v_threshold_574_);
lean_dec(v_threshold_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(lean_object* v_n_577_, lean_object* v_as_578_, lean_object* v_lo_579_, lean_object* v_hi_580_, lean_object* v_w_581_, lean_object* v_hlo_582_, lean_object* v_hhi_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_577_, v_as_578_, v_lo_579_, v_hi_580_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___boxed(lean_object* v_n_585_, lean_object* v_as_586_, lean_object* v_lo_587_, lean_object* v_hi_588_, lean_object* v_w_589_, lean_object* v_hlo_590_, lean_object* v_hhi_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(v_n_585_, v_as_586_, v_lo_587_, v_hi_588_, v_w_589_, v_hlo_590_, v_hhi_591_);
lean_dec(v_hi_588_);
lean_dec(v_n_585_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(lean_object* v_n_593_, lean_object* v_lo_594_, lean_object* v_hi_595_, lean_object* v_hhi_596_, lean_object* v_pivot_597_, lean_object* v_as_598_, lean_object* v_i_599_, lean_object* v_k_600_, lean_object* v_ilo_601_, lean_object* v_ik_602_, lean_object* v_w_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_595_, v_pivot_597_, v_as_598_, v_i_599_, v_k_600_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___boxed(lean_object* v_n_605_, lean_object* v_lo_606_, lean_object* v_hi_607_, lean_object* v_hhi_608_, lean_object* v_pivot_609_, lean_object* v_as_610_, lean_object* v_i_611_, lean_object* v_k_612_, lean_object* v_ilo_613_, lean_object* v_ik_614_, lean_object* v_w_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(v_n_605_, v_lo_606_, v_hi_607_, v_hhi_608_, v_pivot_609_, v_as_610_, v_i_611_, v_k_612_, v_ilo_613_, v_ik_614_, v_w_615_);
lean_dec_ref(v_pivot_609_);
lean_dec(v_hi_607_);
lean_dec(v_lo_606_);
lean_dec(v_n_605_);
return v_res_616_;
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
