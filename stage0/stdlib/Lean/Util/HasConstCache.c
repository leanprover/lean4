// Lean compiler output
// Module: Lean.Util.HasConstCache
// Imports: public import Lean.Expr public import Std.Data.HashMap.Raw
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg___boxed(lean_object* v_m_54_, lean_object* v_query_55_, lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_m_54_, v_query_55_, v_x_56_, v_x_57_, v_x_58_);
lean_dec_ref(v_query_55_);
lean_dec_ref(v_m_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(lean_object* v_m_60_, lean_object* v_query_61_){
_start:
{
lean_object* v_keyArray_62_; lean_object* v___x_63_; uint64_t v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v_fold_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_keyArray_62_ = lean_ctor_get(v_m_60_, 1);
v___x_63_ = lean_array_get_size(v_keyArray_62_);
v___x_64_ = l_Lean_Expr_hash(v_query_61_);
v___x_65_ = 32ULL;
v___x_66_ = lean_uint64_shift_right(v___x_64_, v___x_65_);
v_fold_67_ = lean_uint64_xor(v___x_64_, v___x_66_);
v___x_68_ = 16ULL;
v___x_69_ = lean_uint64_shift_right(v_fold_67_, v___x_68_);
v___x_70_ = lean_uint64_xor(v_fold_67_, v___x_69_);
v___x_71_ = lean_uint64_to_usize(v___x_70_);
v___x_72_ = lean_usize_of_nat(v___x_63_);
v___x_73_ = ((size_t)1ULL);
v___x_74_ = lean_usize_sub(v___x_72_, v___x_73_);
v___x_75_ = lean_usize_land(v___x_71_, v___x_74_);
v___x_76_ = lean_usize_to_nat(v___x_75_);
v___x_77_ = lean_box(0);
v___x_78_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_m_60_, v_query_61_, v___x_77_, v___x_63_, v___x_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg___boxed(lean_object* v_m_79_, lean_object* v_query_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_m_79_, v_query_80_);
lean_dec_ref(v_query_80_);
lean_dec_ref(v_m_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3___redArg(lean_object* v_b_82_, lean_object* v_acc_83_, lean_object* v_i_84_){
_start:
{
lean_object* v___y_86_; lean_object* v_keyArray_94_; lean_object* v_valueArray_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_keyArray_94_ = lean_ctor_get(v_b_82_, 1);
v_valueArray_95_ = lean_ctor_get(v_b_82_, 2);
v___x_96_ = lean_array_get_size(v_keyArray_94_);
v___x_97_ = lean_nat_dec_lt(v_i_84_, v___x_96_);
if (v___x_97_ == 0)
{
lean_dec(v_i_84_);
return v_acc_83_;
}
else
{
lean_object* v___x_98_; uint8_t v_isSome_99_; 
v___x_98_ = lean_array_fget_borrowed(v_keyArray_94_, v_i_84_);
v_isSome_99_ = lean_noption_is_some(v___x_98_);
if (v_isSome_99_ == 0)
{
goto v___jp_90_;
}
else
{
lean_object* v___x_100_; uint8_t v_isSome_101_; 
v___x_100_ = lean_array_fget_borrowed(v_valueArray_95_, v_i_84_);
v_isSome_101_ = lean_noption_is_some(v___x_100_);
if (v_isSome_101_ == 0)
{
goto v___jp_90_;
}
else
{
lean_object* v_val_102_; lean_object* v_val_103_; lean_object* v_i_105_; lean_object* v___x_110_; 
lean_inc(v___x_98_);
v_val_102_ = lean_noption_get(v___x_98_);
lean_inc(v___x_100_);
v_val_103_ = lean_noption_get(v___x_100_);
v___x_110_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_acc_83_, v_val_102_);
switch(lean_obj_tag(v___x_110_))
{
case 0:
{
lean_object* v_index_111_; lean_object* v_size_112_; lean_object* v___x_113_; 
v_index_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_index_111_);
lean_dec_ref_known(v___x_110_, 3);
v_size_112_ = lean_ctor_get(v_acc_83_, 0);
lean_inc(v_size_112_);
v___x_113_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_83_, v_size_112_, v_index_111_, v_val_102_, v_val_103_);
lean_dec(v_index_111_);
v___y_86_ = v___x_113_;
goto v___jp_85_;
}
case 1:
{
lean_object* v_index_114_; 
v_index_114_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_index_114_);
lean_dec_ref_known(v___x_110_, 1);
v_i_105_ = v_index_114_;
goto v___jp_104_;
}
default: 
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_83_, v___x_115_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_index_117_; 
v_index_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_index_117_);
lean_dec_ref_known(v___x_116_, 1);
v_i_105_ = v_index_117_;
goto v___jp_104_;
}
else
{
lean_dec(v_val_103_);
lean_dec(v_val_102_);
v___y_86_ = v_acc_83_;
goto v___jp_85_;
}
}
}
v___jp_104_:
{
lean_object* v_size_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_size_106_ = lean_ctor_get(v_acc_83_, 0);
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_108_ = lean_nat_add(v_size_106_, v___x_107_);
v___x_109_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_83_, v___x_108_, v_i_105_, v_val_102_, v_val_103_);
lean_dec(v_i_105_);
v___y_86_ = v___x_109_;
goto v___jp_85_;
}
}
}
}
v___jp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_i_84_, v___x_87_);
lean_dec(v_i_84_);
v_acc_83_ = v___y_86_;
v_i_84_ = v___x_88_;
goto _start;
}
v___jp_90_:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_add(v_i_84_, v___x_91_);
lean_dec(v_i_84_);
v_i_84_ = v___x_92_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_118_, lean_object* v_acc_119_, lean_object* v_i_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3___redArg(v_b_118_, v_acc_119_, v_i_120_);
lean_dec_ref(v_b_118_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2___redArg(lean_object* v_init_122_, lean_object* v_b_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3___redArg(v_b_123_, v_init_122_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2___redArg___boxed(lean_object* v_init_126_, lean_object* v_b_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2___redArg(v_init_126_, v_b_127_);
lean_dec_ref(v_b_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1___redArg(lean_object* v_m_129_){
_start:
{
lean_object* v_keyArray_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v_cellCount_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v_target_137_; lean_object* v___x_138_; 
v_keyArray_130_ = lean_ctor_get(v_m_129_, 1);
v___x_131_ = lean_array_get_size(v_keyArray_130_);
v___x_132_ = lean_unsigned_to_nat(2u);
v_cellCount_133_ = lean_nat_mul(v___x_131_, v___x_132_);
v___x_134_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_133_);
v___x_135_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_133_);
v___x_136_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_133_);
v_target_137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_137_, 0, v___x_134_);
lean_ctor_set(v_target_137_, 1, v___x_135_);
lean_ctor_set(v_target_137_, 2, v___x_136_);
v___x_138_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2___redArg(v_target_137_, v_m_129_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1___redArg___boxed(lean_object* v_m_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1___redArg(v_m_139_);
lean_dec_ref(v_m_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(lean_object* v_e_141_, uint8_t v_r_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___y_145_; lean_object* v_i_146_; lean_object* v___y_155_; lean_object* v___y_170_; lean_object* v_i_171_; lean_object* v_size_179_; lean_object* v_keyArray_180_; lean_object* v___x_181_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_size_179_ = lean_ctor_get(v_a_143_, 0);
v_keyArray_180_ = lean_ctor_get(v_a_143_, 1);
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_array_get_size(v_keyArray_180_);
v___x_197_ = lean_nat_dec_lt(v___x_181_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec_ref(v_e_141_);
v___x_198_ = lean_box(v_r_142_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v_a_143_);
return v___x_199_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_a_143_, v_e_141_);
switch(lean_obj_tag(v___x_200_))
{
case 0:
{
lean_object* v_index_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
lean_inc(v_size_179_);
v_index_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_index_201_);
lean_dec_ref_known(v___x_200_, 3);
v___x_202_ = lean_box(v_r_142_);
v___x_203_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_143_, v_size_179_, v_index_201_, v_e_141_, v___x_202_);
lean_dec(v_index_201_);
v___x_204_ = lean_box(v_r_142_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
return v___x_205_;
}
case 1:
{
lean_object* v_index_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_index_206_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_index_206_);
lean_dec_ref_known(v___x_200_, 1);
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v_size_179_, v___x_207_);
v___x_209_ = lean_nat_dec_lt(v___x_208_, v___x_196_);
if (v___x_209_ == 0)
{
lean_dec(v___x_208_);
lean_dec(v_index_206_);
goto v___jp_182_;
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_210_ = lean_unsigned_to_nat(4u);
v___x_211_ = lean_nat_mul(v___x_208_, v___x_210_);
v___x_212_ = lean_unsigned_to_nat(3u);
v___x_213_ = lean_nat_mul(v___x_196_, v___x_212_);
v___x_214_ = lean_nat_dec_le(v___x_211_, v___x_213_);
lean_dec(v___x_213_);
lean_dec(v___x_211_);
if (v___x_214_ == 0)
{
lean_dec(v___x_208_);
lean_dec(v_index_206_);
goto v___jp_182_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = lean_box(v_r_142_);
v___x_216_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_143_, v___x_208_, v_index_206_, v_e_141_, v___x_215_);
lean_dec(v_index_206_);
v___x_217_ = lean_box(v_r_142_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_216_);
return v___x_218_;
}
}
}
default: 
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_add(v_size_179_, v___x_219_);
v___x_221_ = lean_nat_dec_lt(v___x_220_, v___x_196_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec(v___x_220_);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1___redArg(v_a_143_);
lean_dec_ref(v_a_143_);
v___y_155_ = v___x_222_;
goto v___jp_154_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_223_ = lean_unsigned_to_nat(4u);
v___x_224_ = lean_nat_mul(v___x_220_, v___x_223_);
lean_dec(v___x_220_);
v___x_225_ = lean_unsigned_to_nat(3u);
v___x_226_ = lean_nat_mul(v___x_196_, v___x_225_);
v___x_227_ = lean_nat_dec_le(v___x_224_, v___x_226_);
lean_dec(v___x_226_);
lean_dec(v___x_224_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
v___x_228_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1___redArg(v_a_143_);
lean_dec_ref(v_a_143_);
v___y_155_ = v___x_228_;
goto v___jp_154_;
}
else
{
v___y_155_ = v_a_143_;
goto v___jp_154_;
}
}
}
}
}
v___jp_144_:
{
lean_object* v_size_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_size_147_ = lean_ctor_get(v___y_145_, 0);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_size_147_, v___x_148_);
v___x_150_ = lean_box(v_r_142_);
v___x_151_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_145_, v___x_149_, v_i_146_, v_e_141_, v___x_150_);
lean_dec(v_i_146_);
v___x_152_ = lean_box(v_r_142_);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
return v___x_153_;
}
v___jp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v___y_155_, v_e_141_);
switch(lean_obj_tag(v___x_156_))
{
case 0:
{
lean_object* v_index_157_; lean_object* v_size_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_index_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_index_157_);
lean_dec_ref_known(v___x_156_, 3);
v_size_158_ = lean_ctor_get(v___y_155_, 0);
lean_inc(v_size_158_);
v___x_159_ = lean_box(v_r_142_);
v___x_160_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_155_, v_size_158_, v_index_157_, v_e_141_, v___x_159_);
lean_dec(v_index_157_);
v___x_161_ = lean_box(v_r_142_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
return v___x_162_;
}
case 1:
{
lean_object* v_index_163_; 
v_index_163_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_index_163_);
lean_dec_ref_known(v___x_156_, 1);
v___y_145_ = v___y_155_;
v_i_146_ = v_index_163_;
goto v___jp_144_;
}
default: 
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_155_, v___x_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_index_166_; 
v_index_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_index_166_);
lean_dec_ref_known(v___x_165_, 1);
v___y_145_ = v___y_155_;
v_i_146_ = v_index_166_;
goto v___jp_144_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec_ref(v_e_141_);
v___x_167_ = lean_box(v_r_142_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___y_155_);
return v___x_168_;
}
}
}
}
v___jp_169_:
{
lean_object* v_size_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_size_172_ = lean_ctor_get(v___y_170_, 0);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_size_172_, v___x_173_);
v___x_175_ = lean_box(v_r_142_);
v___x_176_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_170_, v___x_174_, v_i_171_, v_e_141_, v___x_175_);
lean_dec(v_i_171_);
v___x_177_ = lean_box(v_r_142_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
return v___x_178_;
}
v___jp_182_:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1___redArg(v_a_143_);
lean_dec_ref(v_a_143_);
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v___x_183_, v_e_141_);
switch(lean_obj_tag(v___x_184_))
{
case 0:
{
lean_object* v_index_185_; lean_object* v_size_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_index_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_index_185_);
lean_dec_ref_known(v___x_184_, 3);
v_size_186_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_size_186_);
v___x_187_ = lean_box(v_r_142_);
v___x_188_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_183_, v_size_186_, v_index_185_, v_e_141_, v___x_187_);
lean_dec(v_index_185_);
v___x_189_ = lean_box(v_r_142_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
return v___x_190_;
}
case 1:
{
lean_object* v_index_191_; 
v_index_191_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_index_191_);
lean_dec_ref_known(v___x_184_, 1);
v___y_170_ = v___x_183_;
v_i_171_ = v_index_191_;
goto v___jp_169_;
}
default: 
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_183_, v___x_181_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_index_193_; 
v_index_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_index_193_);
lean_dec_ref_known(v___x_192_, 1);
v___y_170_ = v___x_183_;
v_i_171_ = v_index_193_;
goto v___jp_169_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec_ref(v_e_141_);
v___x_194_ = lean_box(v_r_142_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_183_);
return v___x_195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg___boxed(lean_object* v_e_229_, lean_object* v_r_230_, lean_object* v_a_231_){
_start:
{
uint8_t v_r_boxed_232_; lean_object* v_res_233_; 
v_r_boxed_232_ = lean_unbox(v_r_230_);
v_res_233_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_229_, v_r_boxed_232_, v_a_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(lean_object* v_declNames_234_, lean_object* v_e_235_, uint8_t v_r_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_235_, v_r_236_, v_a_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___boxed(lean_object* v_declNames_239_, lean_object* v_e_240_, lean_object* v_r_241_, lean_object* v_a_242_){
_start:
{
uint8_t v_r_boxed_243_; lean_object* v_res_244_; 
v_r_boxed_243_ = lean_unbox(v_r_241_);
v_res_244_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(v_declNames_239_, v_e_240_, v_r_boxed_243_, v_a_242_);
lean_dec_ref(v_declNames_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0(lean_object* v_00_u03b2_245_, lean_object* v_m_246_, lean_object* v_query_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_m_246_, v_query_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___boxed(lean_object* v_00_u03b2_249_, lean_object* v_m_250_, lean_object* v_query_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0(v_00_u03b2_249_, v_m_250_, v_query_251_);
lean_dec_ref(v_query_251_);
lean_dec_ref(v_m_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1(lean_object* v_00_u03b2_253_, lean_object* v_m_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1___redArg(v_m_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1___boxed(lean_object* v_00_u03b2_256_, lean_object* v_m_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1(v_00_u03b2_256_, v_m_257_);
lean_dec_ref(v_m_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(lean_object* v_00_u03b2_259_, lean_object* v_m_260_, lean_object* v_query_261_, lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_m_260_, v_query_261_, v_x_262_, v_x_263_, v_x_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_267_, lean_object* v_m_268_, lean_object* v_query_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(v_00_u03b2_267_, v_m_268_, v_query_269_, v_x_270_, v_x_271_, v_x_272_, v_x_273_);
lean_dec_ref(v_query_269_);
lean_dec_ref(v_m_268_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2(lean_object* v_00_u03b2_275_, lean_object* v_init_276_, lean_object* v_b_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2___redArg(v_init_276_, v_b_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2___boxed(lean_object* v_00_u03b2_279_, lean_object* v_init_280_, lean_object* v_b_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2(v_00_u03b2_279_, v_init_280_, v_b_281_);
lean_dec_ref(v_b_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_283_, lean_object* v_b_284_, lean_object* v_acc_285_, lean_object* v_i_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3___redArg(v_b_284_, v_acc_285_, v_i_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_288_, lean_object* v_b_289_, lean_object* v_acc_290_, lean_object* v_i_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__1_spec__2_spec__3(v_00_u03b2_288_, v_b_289_, v_acc_290_, v_i_291_);
lean_dec_ref(v_b_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(lean_object* v_m_293_, lean_object* v_query_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_m_293_, v_query_294_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_index_296_; lean_object* v_key_297_; lean_object* v_value_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
v_index_296_ = lean_ctor_get(v___x_295_, 0);
v_key_297_ = lean_ctor_get(v___x_295_, 1);
v_value_298_ = lean_ctor_get(v___x_295_, 2);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_295_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_value_298_);
lean_inc(v_key_297_);
lean_inc(v_index_296_);
lean_dec(v___x_295_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_index_296_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_key_297_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_value_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
else
{
lean_object* v___x_306_; 
lean_dec(v___x_295_);
v___x_306_ = lean_box(1);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg___boxed(lean_object* v_m_307_, lean_object* v_query_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_m_307_, v_query_308_);
lean_dec_ref(v_query_308_);
lean_dec_ref(v_m_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(lean_object* v_m_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_m_310_, v_a_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_value_313_; lean_object* v___x_314_; 
v_value_313_ = lean_ctor_get(v___x_312_, 2);
lean_inc(v_value_313_);
lean_dec_ref_known(v___x_312_, 3);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v_value_313_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; 
v___x_315_ = lean_box(0);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg___boxed(lean_object* v_m_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_316_, v_a_317_);
lean_dec_ref(v_a_317_);
lean_dec_ref(v_m_316_);
return v_res_318_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(lean_object* v_a_319_, lean_object* v_as_320_, size_t v_i_321_, size_t v_stop_322_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = lean_usize_dec_eq(v_i_321_, v_stop_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_array_uget_borrowed(v_as_320_, v_i_321_);
v___x_325_ = lean_name_eq(v_a_319_, v___x_324_);
if (v___x_325_ == 0)
{
size_t v___x_326_; size_t v___x_327_; 
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_add(v_i_321_, v___x_326_);
v_i_321_ = v___x_327_;
goto _start;
}
else
{
return v___x_325_;
}
}
else
{
uint8_t v___x_329_; 
v___x_329_ = 0;
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0___boxed(lean_object* v_a_330_, lean_object* v_as_331_, lean_object* v_i_332_, lean_object* v_stop_333_){
_start:
{
size_t v_i_boxed_334_; size_t v_stop_boxed_335_; uint8_t v_res_336_; lean_object* v_r_337_; 
v_i_boxed_334_ = lean_unbox_usize(v_i_332_);
lean_dec(v_i_332_);
v_stop_boxed_335_ = lean_unbox_usize(v_stop_333_);
lean_dec(v_stop_333_);
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_330_, v_as_331_, v_i_boxed_334_, v_stop_boxed_335_);
lean_dec_ref(v_as_331_);
lean_dec(v_a_330_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(lean_object* v_as_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_array_get_size(v_as_338_);
v___x_342_ = lean_nat_dec_lt(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
return v___x_342_;
}
else
{
if (v___x_342_ == 0)
{
return v___x_342_;
}
else
{
size_t v___x_343_; size_t v___x_344_; uint8_t v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_341_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_339_, v_as_338_, v___x_343_, v___x_344_);
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0___boxed(lean_object* v_as_346_, lean_object* v_a_347_){
_start:
{
uint8_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(v_as_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_as_346_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object* v_declNames_350_, lean_object* v_e_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___y_354_; lean_object* v___y_360_; lean_object* v___y_366_; lean_object* v_d_372_; lean_object* v_b_373_; lean_object* v___y_374_; lean_object* v_keyArray_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_keyArray_423_ = lean_ctor_get(v_a_352_, 1);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_array_get_size(v_keyArray_423_);
v___x_426_ = lean_nat_dec_lt(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
goto v___jp_380_;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_a_352_, v_e_351_);
if (lean_obj_tag(v___x_427_) == 1)
{
lean_object* v_val_428_; lean_object* v___x_429_; 
lean_dec_ref(v_e_351_);
v_val_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_val_428_);
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_val_428_);
lean_ctor_set(v___x_429_, 1, v_a_352_);
return v___x_429_;
}
else
{
lean_dec(v___x_427_);
goto v___jp_380_;
}
}
v___jp_353_:
{
lean_object* v_fst_355_; lean_object* v_snd_356_; uint8_t v___x_357_; lean_object* v___x_358_; 
v_fst_355_ = lean_ctor_get(v___y_354_, 0);
lean_inc(v_fst_355_);
v_snd_356_ = lean_ctor_get(v___y_354_, 1);
lean_inc(v_snd_356_);
lean_dec_ref(v___y_354_);
v___x_357_ = lean_unbox(v_fst_355_);
lean_dec(v_fst_355_);
v___x_358_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_351_, v___x_357_, v_snd_356_);
return v___x_358_;
}
v___jp_359_:
{
lean_object* v_fst_361_; lean_object* v_snd_362_; uint8_t v___x_363_; lean_object* v___x_364_; 
v_fst_361_ = lean_ctor_get(v___y_360_, 0);
lean_inc(v_fst_361_);
v_snd_362_ = lean_ctor_get(v___y_360_, 1);
lean_inc(v_snd_362_);
lean_dec_ref(v___y_360_);
v___x_363_ = lean_unbox(v_fst_361_);
lean_dec(v_fst_361_);
v___x_364_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_351_, v___x_363_, v_snd_362_);
return v___x_364_;
}
v___jp_365_:
{
lean_object* v_fst_367_; lean_object* v_snd_368_; uint8_t v___x_369_; lean_object* v___x_370_; 
v_fst_367_ = lean_ctor_get(v___y_366_, 0);
lean_inc(v_fst_367_);
v_snd_368_ = lean_ctor_get(v___y_366_, 1);
lean_inc(v_snd_368_);
lean_dec_ref(v___y_366_);
v___x_369_ = lean_unbox(v_fst_367_);
lean_dec(v_fst_367_);
v___x_370_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_351_, v___x_369_, v_snd_368_);
return v___x_370_;
}
v___jp_371_:
{
lean_object* v___x_375_; lean_object* v_fst_376_; uint8_t v___x_377_; 
v___x_375_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_350_, v_d_372_, v___y_374_);
v_fst_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_fst_376_);
v___x_377_ = lean_unbox(v_fst_376_);
lean_dec(v_fst_376_);
if (v___x_377_ == 0)
{
lean_object* v_snd_378_; lean_object* v___x_379_; 
v_snd_378_ = lean_ctor_get(v___x_375_, 1);
lean_inc(v_snd_378_);
lean_dec_ref(v___x_375_);
v___x_379_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_350_, v_b_373_, v_snd_378_);
v___y_366_ = v___x_379_;
goto v___jp_365_;
}
else
{
lean_dec_ref(v_b_373_);
v___y_366_ = v___x_375_;
goto v___jp_365_;
}
}
v___jp_380_:
{
switch(lean_obj_tag(v_e_351_))
{
case 4:
{
lean_object* v_declName_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_declName_381_ = lean_ctor_get(v_e_351_, 0);
lean_inc(v_declName_381_);
lean_dec_ref_known(v_e_351_, 2);
v___x_382_ = l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(v_declNames_350_, v_declName_381_);
lean_dec(v_declName_381_);
v___x_383_ = lean_box(v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_a_352_);
return v___x_384_;
}
case 5:
{
lean_object* v_fn_385_; lean_object* v_arg_386_; lean_object* v___x_387_; lean_object* v_fst_388_; uint8_t v___x_389_; 
v_fn_385_ = lean_ctor_get(v_e_351_, 0);
v_arg_386_ = lean_ctor_get(v_e_351_, 1);
lean_inc_ref(v_fn_385_);
v___x_387_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_350_, v_fn_385_, v_a_352_);
v_fst_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_fst_388_);
v___x_389_ = lean_unbox(v_fst_388_);
lean_dec(v_fst_388_);
if (v___x_389_ == 0)
{
lean_object* v_snd_390_; lean_object* v___x_391_; 
v_snd_390_ = lean_ctor_get(v___x_387_, 1);
lean_inc(v_snd_390_);
lean_dec_ref(v___x_387_);
lean_inc_ref(v_arg_386_);
v___x_391_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_350_, v_arg_386_, v_snd_390_);
v___y_360_ = v___x_391_;
goto v___jp_359_;
}
else
{
v___y_360_ = v___x_387_;
goto v___jp_359_;
}
}
case 6:
{
lean_object* v_binderType_392_; lean_object* v_body_393_; 
v_binderType_392_ = lean_ctor_get(v_e_351_, 1);
v_body_393_ = lean_ctor_get(v_e_351_, 2);
lean_inc_ref(v_body_393_);
lean_inc_ref(v_binderType_392_);
v_d_372_ = v_binderType_392_;
v_b_373_ = v_body_393_;
v___y_374_ = v_a_352_;
goto v___jp_371_;
}
case 7:
{
lean_object* v_binderType_394_; lean_object* v_body_395_; 
v_binderType_394_ = lean_ctor_get(v_e_351_, 1);
v_body_395_ = lean_ctor_get(v_e_351_, 2);
lean_inc_ref(v_body_395_);
lean_inc_ref(v_binderType_394_);
v_d_372_ = v_binderType_394_;
v_b_373_ = v_body_395_;
v___y_374_ = v_a_352_;
goto v___jp_371_;
}
case 8:
{
lean_object* v_type_396_; lean_object* v_value_397_; lean_object* v_body_398_; lean_object* v___x_399_; lean_object* v_fst_400_; uint8_t v___x_401_; 
v_type_396_ = lean_ctor_get(v_e_351_, 1);
v_value_397_ = lean_ctor_get(v_e_351_, 2);
v_body_398_ = lean_ctor_get(v_e_351_, 3);
lean_inc_ref(v_type_396_);
v___x_399_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_350_, v_type_396_, v_a_352_);
v_fst_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_fst_400_);
v___x_401_ = lean_unbox(v_fst_400_);
lean_dec(v_fst_400_);
if (v___x_401_ == 0)
{
lean_object* v_snd_402_; lean_object* v___x_403_; lean_object* v_fst_404_; uint8_t v___x_405_; 
v_snd_402_ = lean_ctor_get(v___x_399_, 1);
lean_inc(v_snd_402_);
lean_dec_ref(v___x_399_);
lean_inc_ref(v_value_397_);
v___x_403_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_350_, v_value_397_, v_snd_402_);
v_fst_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_fst_404_);
v___x_405_ = lean_unbox(v_fst_404_);
lean_dec(v_fst_404_);
if (v___x_405_ == 0)
{
lean_object* v_snd_406_; lean_object* v___x_407_; 
v_snd_406_ = lean_ctor_get(v___x_403_, 1);
lean_inc(v_snd_406_);
lean_dec_ref(v___x_403_);
lean_inc_ref(v_body_398_);
v___x_407_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_350_, v_body_398_, v_snd_406_);
v___y_354_ = v___x_407_;
goto v___jp_353_;
}
else
{
v___y_354_ = v___x_403_;
goto v___jp_353_;
}
}
else
{
v___y_354_ = v___x_399_;
goto v___jp_353_;
}
}
case 10:
{
lean_object* v_expr_408_; lean_object* v___x_409_; lean_object* v_fst_410_; lean_object* v_snd_411_; uint8_t v___x_412_; lean_object* v___x_413_; 
v_expr_408_ = lean_ctor_get(v_e_351_, 1);
lean_inc_ref(v_expr_408_);
v___x_409_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_350_, v_expr_408_, v_a_352_);
v_fst_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_fst_410_);
v_snd_411_ = lean_ctor_get(v___x_409_, 1);
lean_inc(v_snd_411_);
lean_dec_ref(v___x_409_);
v___x_412_ = lean_unbox(v_fst_410_);
lean_dec(v_fst_410_);
v___x_413_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_351_, v___x_412_, v_snd_411_);
return v___x_413_;
}
case 11:
{
lean_object* v_struct_414_; lean_object* v___x_415_; lean_object* v_fst_416_; lean_object* v_snd_417_; uint8_t v___x_418_; lean_object* v___x_419_; 
v_struct_414_ = lean_ctor_get(v_e_351_, 2);
lean_inc_ref(v_struct_414_);
v___x_415_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_350_, v_struct_414_, v_a_352_);
v_fst_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_fst_416_);
v_snd_417_ = lean_ctor_get(v___x_415_, 1);
lean_inc(v_snd_417_);
lean_dec_ref(v___x_415_);
v___x_418_ = lean_unbox(v_fst_416_);
lean_dec(v_fst_416_);
v___x_419_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_351_, v___x_418_, v_snd_417_);
return v___x_419_;
}
default: 
{
uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec_ref(v_e_351_);
v___x_420_ = 0;
v___x_421_ = lean_box(v___x_420_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v_a_352_);
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe___boxed(lean_object* v_declNames_430_, lean_object* v_e_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_430_, v_e_431_, v_a_432_);
lean_dec_ref(v_declNames_430_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(lean_object* v_00_u03b2_434_, lean_object* v_m_435_, lean_object* v_a_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_435_, v_a_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___boxed(lean_object* v_00_u03b2_438_, lean_object* v_m_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(v_00_u03b2_438_, v_m_439_, v_a_440_);
lean_dec_ref(v_a_440_);
lean_dec_ref(v_m_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(lean_object* v_00_u03b2_442_, lean_object* v_m_443_, lean_object* v_query_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_m_443_, v_query_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___boxed(lean_object* v_00_u03b2_446_, lean_object* v_m_447_, lean_object* v_query_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(v_00_u03b2_446_, v_m_447_, v_query_448_);
lean_dec_ref(v_query_448_);
lean_dec_ref(v_m_447_);
return v_res_449_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_HasConstCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_HasConstCache(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_HasConstCache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_HasConstCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_HasConstCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_HasConstCache(builtin);
}
#ifdef __cplusplus
}
#endif
