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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_tail_5_; size_t v___x_6_; size_t v___x_7_; uint8_t v___x_8_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v___x_6_ = lean_ptr_addr(v_key_4_);
v___x_7_ = lean_ptr_addr(v_a_1_);
v___x_8_ = lean_usize_dec_eq(v___x_6_, v___x_7_);
if (v___x_8_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec_ref(v_a_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(lean_object* v_a_14_, lean_object* v_b_15_, lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_dec(v_b_15_);
lean_dec_ref(v_a_14_);
return v_x_16_;
}
else
{
lean_object* v_key_17_; lean_object* v_value_18_; lean_object* v_tail_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_33_; 
v_key_17_ = lean_ctor_get(v_x_16_, 0);
v_value_18_ = lean_ctor_get(v_x_16_, 1);
v_tail_19_ = lean_ctor_get(v_x_16_, 2);
v_isSharedCheck_33_ = !lean_is_exclusive(v_x_16_);
if (v_isSharedCheck_33_ == 0)
{
v___x_21_ = v_x_16_;
v_isShared_22_ = v_isSharedCheck_33_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_tail_19_);
lean_inc(v_value_18_);
lean_inc(v_key_17_);
lean_dec(v_x_16_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_33_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
size_t v___x_23_; size_t v___x_24_; uint8_t v___x_25_; 
v___x_23_ = lean_ptr_addr(v_key_17_);
v___x_24_ = lean_ptr_addr(v_a_14_);
v___x_25_ = lean_usize_dec_eq(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_26_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_14_, v_b_15_, v_tail_19_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 2, v___x_26_);
v___x_28_ = v___x_21_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_key_17_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_value_18_);
lean_ctor_set(v_reuseFailAlloc_29_, 2, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
else
{
lean_object* v___x_31_; 
lean_dec(v_value_18_);
lean_dec(v_key_17_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 1, v_b_15_);
lean_ctor_set(v___x_21_, 0, v_a_14_);
v___x_31_ = v___x_21_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_14_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_b_15_);
lean_ctor_set(v_reuseFailAlloc_32_, 2, v_tail_19_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
return v_x_34_;
}
else
{
lean_object* v_key_36_; lean_object* v_value_37_; lean_object* v_tail_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_61_; 
v_key_36_ = lean_ctor_get(v_x_35_, 0);
v_value_37_ = lean_ctor_get(v_x_35_, 1);
v_tail_38_ = lean_ctor_get(v_x_35_, 2);
v_isSharedCheck_61_ = !lean_is_exclusive(v_x_35_);
if (v_isSharedCheck_61_ == 0)
{
v___x_40_ = v_x_35_;
v_isShared_41_ = v_isSharedCheck_61_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_tail_38_);
lean_inc(v_value_37_);
lean_inc(v_key_36_);
lean_dec(v_x_35_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_61_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; uint64_t v___x_43_; uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v_fold_46_; uint64_t v___x_47_; uint64_t v___x_48_; uint64_t v___x_49_; size_t v___x_50_; size_t v___x_51_; size_t v___x_52_; size_t v___x_53_; size_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_42_ = lean_array_get_size(v_x_34_);
v___x_43_ = l_Lean_Expr_hash(v_key_36_);
v___x_44_ = 32ULL;
v___x_45_ = lean_uint64_shift_right(v___x_43_, v___x_44_);
v_fold_46_ = lean_uint64_xor(v___x_43_, v___x_45_);
v___x_47_ = 16ULL;
v___x_48_ = lean_uint64_shift_right(v_fold_46_, v___x_47_);
v___x_49_ = lean_uint64_xor(v_fold_46_, v___x_48_);
v___x_50_ = lean_uint64_to_usize(v___x_49_);
v___x_51_ = lean_usize_of_nat(v___x_42_);
v___x_52_ = ((size_t)1ULL);
v___x_53_ = lean_usize_sub(v___x_51_, v___x_52_);
v___x_54_ = lean_usize_land(v___x_50_, v___x_53_);
v___x_55_ = lean_array_uget_borrowed(v_x_34_, v___x_54_);
lean_inc(v___x_55_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 2, v___x_55_);
v___x_57_ = v___x_40_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_key_36_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_value_37_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v___x_55_);
v___x_57_ = v_reuseFailAlloc_60_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
lean_object* v___x_58_; 
v___x_58_ = lean_array_uset(v_x_34_, v___x_54_, v___x_57_);
v_x_34_ = v___x_58_;
v_x_35_ = v_tail_38_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(lean_object* v_i_62_, lean_object* v_source_63_, lean_object* v_target_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_array_get_size(v_source_63_);
v___x_66_ = lean_nat_dec_lt(v_i_62_, v___x_65_);
if (v___x_66_ == 0)
{
lean_dec_ref(v_source_63_);
lean_dec(v_i_62_);
return v_target_64_;
}
else
{
lean_object* v_es_67_; lean_object* v___x_68_; lean_object* v_source_69_; lean_object* v_target_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_es_67_ = lean_array_fget(v_source_63_, v_i_62_);
v___x_68_ = lean_box(0);
v_source_69_ = lean_array_fset(v_source_63_, v_i_62_, v___x_68_);
v_target_70_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_target_64_, v_es_67_);
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v_i_62_, v___x_71_);
lean_dec(v_i_62_);
v_i_62_ = v___x_72_;
v_source_63_ = v_source_69_;
v_target_64_ = v_target_70_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(lean_object* v_data_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_nbuckets_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_75_ = lean_array_get_size(v_data_74_);
v___x_76_ = lean_unsigned_to_nat(2u);
v_nbuckets_77_ = lean_nat_mul(v___x_75_, v___x_76_);
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_box(0);
v___x_80_ = lean_mk_array(v_nbuckets_77_, v___x_79_);
v___x_81_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(v___x_78_, v_data_74_, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(lean_object* v_m_82_, lean_object* v_a_83_, lean_object* v_b_84_){
_start:
{
lean_object* v_size_85_; lean_object* v_buckets_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_129_; 
v_size_85_ = lean_ctor_get(v_m_82_, 0);
v_buckets_86_ = lean_ctor_get(v_m_82_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_m_82_);
if (v_isSharedCheck_129_ == 0)
{
v___x_88_ = v_m_82_;
v_isShared_89_ = v_isSharedCheck_129_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_buckets_86_);
lean_inc(v_size_85_);
lean_dec(v_m_82_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_129_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v_fold_94_; uint64_t v___x_95_; uint64_t v___x_96_; uint64_t v___x_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v_bkt_103_; uint8_t v___x_104_; 
v___x_90_ = lean_array_get_size(v_buckets_86_);
v___x_91_ = l_Lean_Expr_hash(v_a_83_);
v___x_92_ = 32ULL;
v___x_93_ = lean_uint64_shift_right(v___x_91_, v___x_92_);
v_fold_94_ = lean_uint64_xor(v___x_91_, v___x_93_);
v___x_95_ = 16ULL;
v___x_96_ = lean_uint64_shift_right(v_fold_94_, v___x_95_);
v___x_97_ = lean_uint64_xor(v_fold_94_, v___x_96_);
v___x_98_ = lean_uint64_to_usize(v___x_97_);
v___x_99_ = lean_usize_of_nat(v___x_90_);
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_sub(v___x_99_, v___x_100_);
v___x_102_ = lean_usize_land(v___x_98_, v___x_101_);
v_bkt_103_ = lean_array_uget_borrowed(v_buckets_86_, v___x_102_);
v___x_104_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_83_, v_bkt_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v_size_x27_106_; lean_object* v___x_107_; lean_object* v_buckets_x27_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_105_ = lean_unsigned_to_nat(1u);
v_size_x27_106_ = lean_nat_add(v_size_85_, v___x_105_);
lean_dec(v_size_85_);
lean_inc(v_bkt_103_);
v___x_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_107_, 0, v_a_83_);
lean_ctor_set(v___x_107_, 1, v_b_84_);
lean_ctor_set(v___x_107_, 2, v_bkt_103_);
v_buckets_x27_108_ = lean_array_uset(v_buckets_86_, v___x_102_, v___x_107_);
v___x_109_ = lean_unsigned_to_nat(4u);
v___x_110_ = lean_nat_mul(v_size_x27_106_, v___x_109_);
v___x_111_ = lean_unsigned_to_nat(3u);
v___x_112_ = lean_nat_div(v___x_110_, v___x_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_array_get_size(v_buckets_x27_108_);
v___x_114_ = lean_nat_dec_le(v___x_112_, v___x_113_);
lean_dec(v___x_112_);
if (v___x_114_ == 0)
{
lean_object* v_val_115_; lean_object* v___x_117_; 
v_val_115_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(v_buckets_x27_108_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 1, v_val_115_);
lean_ctor_set(v___x_88_, 0, v_size_x27_106_);
v___x_117_ = v___x_88_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_size_x27_106_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_val_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
else
{
lean_object* v___x_120_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 1, v_buckets_x27_108_);
lean_ctor_set(v___x_88_, 0, v_size_x27_106_);
v___x_120_ = v___x_88_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_size_x27_106_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_buckets_x27_108_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_object* v___x_122_; lean_object* v_buckets_x27_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_bkt_103_);
v___x_122_ = lean_box(0);
v_buckets_x27_123_ = lean_array_uset(v_buckets_86_, v___x_102_, v___x_122_);
v___x_124_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_83_, v_b_84_, v_bkt_103_);
v___x_125_ = lean_array_uset(v_buckets_x27_123_, v___x_102_, v___x_124_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 1, v___x_125_);
v___x_127_ = v___x_88_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_size_85_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(lean_object* v_e_130_, uint8_t v_r_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_buckets_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_buckets_133_ = lean_ctor_get(v_a_132_, 1);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_array_get_size(v_buckets_133_);
v___x_136_ = lean_nat_dec_lt(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec_ref(v_e_130_);
v___x_137_ = lean_box(v_r_131_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v_a_132_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_139_ = lean_box(v_r_131_);
v___x_140_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_a_132_, v_e_130_, v___x_139_);
v___x_141_ = lean_box(v_r_131_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg___boxed(lean_object* v_e_143_, lean_object* v_r_144_, lean_object* v_a_145_){
_start:
{
uint8_t v_r_boxed_146_; lean_object* v_res_147_; 
v_r_boxed_146_ = lean_unbox(v_r_144_);
v_res_147_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_143_, v_r_boxed_146_, v_a_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(lean_object* v_declNames_148_, lean_object* v_e_149_, uint8_t v_r_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_149_, v_r_150_, v_a_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___boxed(lean_object* v_declNames_153_, lean_object* v_e_154_, lean_object* v_r_155_, lean_object* v_a_156_){
_start:
{
uint8_t v_r_boxed_157_; lean_object* v_res_158_; 
v_r_boxed_157_ = lean_unbox(v_r_155_);
v_res_158_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(v_declNames_153_, v_e_154_, v_r_boxed_157_, v_a_156_);
lean_dec_ref(v_declNames_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0(lean_object* v_00_u03b2_159_, lean_object* v_m_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_m_160_, v_a_161_, v_b_162_);
return v___x_163_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(lean_object* v_00_u03b2_164_, lean_object* v_a_165_, lean_object* v_x_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_165_, v_x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_168_, lean_object* v_a_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(v_00_u03b2_168_, v_a_169_, v_x_170_);
lean_dec(v_x_170_);
lean_dec_ref(v_a_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1(lean_object* v_00_u03b2_173_, lean_object* v_data_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(v_data_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2(lean_object* v_00_u03b2_176_, lean_object* v_a_177_, lean_object* v_b_178_, lean_object* v_x_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_177_, v_b_178_, v_x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_181_, lean_object* v_i_182_, lean_object* v_source_183_, lean_object* v_target_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(v_i_182_, v_source_183_, v_target_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_187_, v_x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(lean_object* v_a_190_, lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(0);
return v___x_192_;
}
else
{
lean_object* v_key_193_; lean_object* v_value_194_; lean_object* v_tail_195_; size_t v___x_196_; size_t v___x_197_; uint8_t v___x_198_; 
v_key_193_ = lean_ctor_get(v_x_191_, 0);
v_value_194_ = lean_ctor_get(v_x_191_, 1);
v_tail_195_ = lean_ctor_get(v_x_191_, 2);
v___x_196_ = lean_ptr_addr(v_key_193_);
v___x_197_ = lean_ptr_addr(v_a_190_);
v___x_198_ = lean_usize_dec_eq(v___x_196_, v___x_197_);
if (v___x_198_ == 0)
{
v_x_191_ = v_tail_195_;
goto _start;
}
else
{
lean_object* v___x_200_; 
lean_inc(v_value_194_);
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v_value_194_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg___boxed(lean_object* v_a_201_, lean_object* v_x_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_201_, v_x_202_);
lean_dec(v_x_202_);
lean_dec_ref(v_a_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(lean_object* v_m_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_buckets_206_; lean_object* v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v_fold_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_buckets_206_ = lean_ctor_get(v_m_204_, 1);
v___x_207_ = lean_array_get_size(v_buckets_206_);
v___x_208_ = l_Lean_Expr_hash(v_a_205_);
v___x_209_ = 32ULL;
v___x_210_ = lean_uint64_shift_right(v___x_208_, v___x_209_);
v_fold_211_ = lean_uint64_xor(v___x_208_, v___x_210_);
v___x_212_ = 16ULL;
v___x_213_ = lean_uint64_shift_right(v_fold_211_, v___x_212_);
v___x_214_ = lean_uint64_xor(v_fold_211_, v___x_213_);
v___x_215_ = lean_uint64_to_usize(v___x_214_);
v___x_216_ = lean_usize_of_nat(v___x_207_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_sub(v___x_216_, v___x_217_);
v___x_219_ = lean_usize_land(v___x_215_, v___x_218_);
v___x_220_ = lean_array_uget_borrowed(v_buckets_206_, v___x_219_);
v___x_221_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_205_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg___boxed(lean_object* v_m_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_222_, v_a_223_);
lean_dec_ref(v_a_223_);
lean_dec_ref(v_m_222_);
return v_res_224_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(lean_object* v_a_225_, lean_object* v_as_226_, size_t v_i_227_, size_t v_stop_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = lean_usize_dec_eq(v_i_227_, v_stop_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_array_uget_borrowed(v_as_226_, v_i_227_);
v___x_231_ = lean_name_eq(v_a_225_, v___x_230_);
if (v___x_231_ == 0)
{
size_t v___x_232_; size_t v___x_233_; 
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_add(v_i_227_, v___x_232_);
v_i_227_ = v___x_233_;
goto _start;
}
else
{
return v___x_231_;
}
}
else
{
uint8_t v___x_235_; 
v___x_235_ = 0;
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0___boxed(lean_object* v_a_236_, lean_object* v_as_237_, lean_object* v_i_238_, lean_object* v_stop_239_){
_start:
{
size_t v_i_boxed_240_; size_t v_stop_boxed_241_; uint8_t v_res_242_; lean_object* v_r_243_; 
v_i_boxed_240_ = lean_unbox_usize(v_i_238_);
lean_dec(v_i_238_);
v_stop_boxed_241_ = lean_unbox_usize(v_stop_239_);
lean_dec(v_stop_239_);
v_res_242_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_236_, v_as_237_, v_i_boxed_240_, v_stop_boxed_241_);
lean_dec_ref(v_as_237_);
lean_dec(v_a_236_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(lean_object* v_as_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_array_get_size(v_as_244_);
v___x_248_ = lean_nat_dec_lt(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
return v___x_248_;
}
else
{
if (v___x_248_ == 0)
{
return v___x_248_;
}
else
{
size_t v___x_249_; size_t v___x_250_; uint8_t v___x_251_; 
v___x_249_ = ((size_t)0ULL);
v___x_250_ = lean_usize_of_nat(v___x_247_);
v___x_251_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_245_, v_as_244_, v___x_249_, v___x_250_);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0___boxed(lean_object* v_as_252_, lean_object* v_a_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(v_as_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_as_252_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object* v_declNames_256_, lean_object* v_e_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___y_260_; lean_object* v___y_266_; lean_object* v___y_272_; lean_object* v_d_278_; lean_object* v_b_279_; lean_object* v___y_280_; lean_object* v_buckets_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_buckets_329_ = lean_ctor_get(v_a_258_, 1);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_array_get_size(v_buckets_329_);
v___x_332_ = lean_nat_dec_lt(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
goto v___jp_286_;
}
else
{
lean_object* v___x_333_; 
v___x_333_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_a_258_, v_e_257_);
if (lean_obj_tag(v___x_333_) == 1)
{
lean_object* v_val_334_; lean_object* v___x_335_; 
lean_dec_ref(v_e_257_);
v_val_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_val_334_);
lean_dec_ref(v___x_333_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v_val_334_);
lean_ctor_set(v___x_335_, 1, v_a_258_);
return v___x_335_;
}
else
{
lean_dec(v___x_333_);
goto v___jp_286_;
}
}
v___jp_259_:
{
lean_object* v_fst_261_; lean_object* v_snd_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
v_fst_261_ = lean_ctor_get(v___y_260_, 0);
lean_inc(v_fst_261_);
v_snd_262_ = lean_ctor_get(v___y_260_, 1);
lean_inc(v_snd_262_);
lean_dec_ref(v___y_260_);
v___x_263_ = lean_unbox(v_fst_261_);
lean_dec(v_fst_261_);
v___x_264_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_257_, v___x_263_, v_snd_262_);
return v___x_264_;
}
v___jp_265_:
{
lean_object* v_fst_267_; lean_object* v_snd_268_; uint8_t v___x_269_; lean_object* v___x_270_; 
v_fst_267_ = lean_ctor_get(v___y_266_, 0);
lean_inc(v_fst_267_);
v_snd_268_ = lean_ctor_get(v___y_266_, 1);
lean_inc(v_snd_268_);
lean_dec_ref(v___y_266_);
v___x_269_ = lean_unbox(v_fst_267_);
lean_dec(v_fst_267_);
v___x_270_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_257_, v___x_269_, v_snd_268_);
return v___x_270_;
}
v___jp_271_:
{
lean_object* v_fst_273_; lean_object* v_snd_274_; uint8_t v___x_275_; lean_object* v___x_276_; 
v_fst_273_ = lean_ctor_get(v___y_272_, 0);
lean_inc(v_fst_273_);
v_snd_274_ = lean_ctor_get(v___y_272_, 1);
lean_inc(v_snd_274_);
lean_dec_ref(v___y_272_);
v___x_275_ = lean_unbox(v_fst_273_);
lean_dec(v_fst_273_);
v___x_276_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_257_, v___x_275_, v_snd_274_);
return v___x_276_;
}
v___jp_277_:
{
lean_object* v___x_281_; lean_object* v_fst_282_; uint8_t v___x_283_; 
v___x_281_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_256_, v_d_278_, v___y_280_);
v_fst_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_fst_282_);
v___x_283_ = lean_unbox(v_fst_282_);
lean_dec(v_fst_282_);
if (v___x_283_ == 0)
{
lean_object* v_snd_284_; lean_object* v___x_285_; 
v_snd_284_ = lean_ctor_get(v___x_281_, 1);
lean_inc(v_snd_284_);
lean_dec_ref(v___x_281_);
v___x_285_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_256_, v_b_279_, v_snd_284_);
v___y_272_ = v___x_285_;
goto v___jp_271_;
}
else
{
lean_dec_ref(v_b_279_);
v___y_272_ = v___x_281_;
goto v___jp_271_;
}
}
v___jp_286_:
{
switch(lean_obj_tag(v_e_257_))
{
case 4:
{
lean_object* v_declName_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_declName_287_ = lean_ctor_get(v_e_257_, 0);
lean_inc(v_declName_287_);
lean_dec_ref(v_e_257_);
v___x_288_ = l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(v_declNames_256_, v_declName_287_);
lean_dec(v_declName_287_);
v___x_289_ = lean_box(v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_a_258_);
return v___x_290_;
}
case 5:
{
lean_object* v_fn_291_; lean_object* v_arg_292_; lean_object* v___x_293_; lean_object* v_fst_294_; uint8_t v___x_295_; 
v_fn_291_ = lean_ctor_get(v_e_257_, 0);
v_arg_292_ = lean_ctor_get(v_e_257_, 1);
lean_inc_ref(v_fn_291_);
v___x_293_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_256_, v_fn_291_, v_a_258_);
v_fst_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_fst_294_);
v___x_295_ = lean_unbox(v_fst_294_);
lean_dec(v_fst_294_);
if (v___x_295_ == 0)
{
lean_object* v_snd_296_; lean_object* v___x_297_; 
v_snd_296_ = lean_ctor_get(v___x_293_, 1);
lean_inc(v_snd_296_);
lean_dec_ref(v___x_293_);
lean_inc_ref(v_arg_292_);
v___x_297_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_256_, v_arg_292_, v_snd_296_);
v___y_266_ = v___x_297_;
goto v___jp_265_;
}
else
{
v___y_266_ = v___x_293_;
goto v___jp_265_;
}
}
case 6:
{
lean_object* v_binderType_298_; lean_object* v_body_299_; 
v_binderType_298_ = lean_ctor_get(v_e_257_, 1);
v_body_299_ = lean_ctor_get(v_e_257_, 2);
lean_inc_ref(v_body_299_);
lean_inc_ref(v_binderType_298_);
v_d_278_ = v_binderType_298_;
v_b_279_ = v_body_299_;
v___y_280_ = v_a_258_;
goto v___jp_277_;
}
case 7:
{
lean_object* v_binderType_300_; lean_object* v_body_301_; 
v_binderType_300_ = lean_ctor_get(v_e_257_, 1);
v_body_301_ = lean_ctor_get(v_e_257_, 2);
lean_inc_ref(v_body_301_);
lean_inc_ref(v_binderType_300_);
v_d_278_ = v_binderType_300_;
v_b_279_ = v_body_301_;
v___y_280_ = v_a_258_;
goto v___jp_277_;
}
case 8:
{
lean_object* v_type_302_; lean_object* v_value_303_; lean_object* v_body_304_; lean_object* v___x_305_; lean_object* v_fst_306_; uint8_t v___x_307_; 
v_type_302_ = lean_ctor_get(v_e_257_, 1);
v_value_303_ = lean_ctor_get(v_e_257_, 2);
v_body_304_ = lean_ctor_get(v_e_257_, 3);
lean_inc_ref(v_type_302_);
v___x_305_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_256_, v_type_302_, v_a_258_);
v_fst_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_fst_306_);
v___x_307_ = lean_unbox(v_fst_306_);
lean_dec(v_fst_306_);
if (v___x_307_ == 0)
{
lean_object* v_snd_308_; lean_object* v___x_309_; lean_object* v_fst_310_; uint8_t v___x_311_; 
v_snd_308_ = lean_ctor_get(v___x_305_, 1);
lean_inc(v_snd_308_);
lean_dec_ref(v___x_305_);
lean_inc_ref(v_value_303_);
v___x_309_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_256_, v_value_303_, v_snd_308_);
v_fst_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_fst_310_);
v___x_311_ = lean_unbox(v_fst_310_);
lean_dec(v_fst_310_);
if (v___x_311_ == 0)
{
lean_object* v_snd_312_; lean_object* v___x_313_; 
v_snd_312_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_snd_312_);
lean_dec_ref(v___x_309_);
lean_inc_ref(v_body_304_);
v___x_313_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_256_, v_body_304_, v_snd_312_);
v___y_260_ = v___x_313_;
goto v___jp_259_;
}
else
{
v___y_260_ = v___x_309_;
goto v___jp_259_;
}
}
else
{
v___y_260_ = v___x_305_;
goto v___jp_259_;
}
}
case 10:
{
lean_object* v_expr_314_; lean_object* v___x_315_; lean_object* v_fst_316_; lean_object* v_snd_317_; uint8_t v___x_318_; lean_object* v___x_319_; 
v_expr_314_ = lean_ctor_get(v_e_257_, 1);
lean_inc_ref(v_expr_314_);
v___x_315_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_256_, v_expr_314_, v_a_258_);
v_fst_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_fst_316_);
v_snd_317_ = lean_ctor_get(v___x_315_, 1);
lean_inc(v_snd_317_);
lean_dec_ref(v___x_315_);
v___x_318_ = lean_unbox(v_fst_316_);
lean_dec(v_fst_316_);
v___x_319_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_257_, v___x_318_, v_snd_317_);
return v___x_319_;
}
case 11:
{
lean_object* v_struct_320_; lean_object* v___x_321_; lean_object* v_fst_322_; lean_object* v_snd_323_; uint8_t v___x_324_; lean_object* v___x_325_; 
v_struct_320_ = lean_ctor_get(v_e_257_, 2);
lean_inc_ref(v_struct_320_);
v___x_321_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_256_, v_struct_320_, v_a_258_);
v_fst_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_fst_322_);
v_snd_323_ = lean_ctor_get(v___x_321_, 1);
lean_inc(v_snd_323_);
lean_dec_ref(v___x_321_);
v___x_324_ = lean_unbox(v_fst_322_);
lean_dec(v_fst_322_);
v___x_325_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_257_, v___x_324_, v_snd_323_);
return v___x_325_;
}
default: 
{
uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec_ref(v_e_257_);
v___x_326_ = 0;
v___x_327_ = lean_box(v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v_a_258_);
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe___boxed(lean_object* v_declNames_336_, lean_object* v_e_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_336_, v_e_337_, v_a_338_);
lean_dec_ref(v_declNames_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(lean_object* v_00_u03b2_340_, lean_object* v_m_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_341_, v_a_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___boxed(lean_object* v_00_u03b2_344_, lean_object* v_m_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(v_00_u03b2_344_, v_m_345_, v_a_346_);
lean_dec_ref(v_a_346_);
lean_dec_ref(v_m_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(lean_object* v_00_u03b2_348_, lean_object* v_a_349_, lean_object* v_x_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_349_, v_x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___boxed(lean_object* v_00_u03b2_352_, lean_object* v_a_353_, lean_object* v_x_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(v_00_u03b2_352_, v_a_353_, v_x_354_);
lean_dec(v_x_354_);
lean_dec_ref(v_a_353_);
return v_res_355_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_HasConstCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
