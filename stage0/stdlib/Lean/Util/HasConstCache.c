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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_nbuckets_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_75_ = lean_array_get_size(v_data_74_);
v___x_76_ = lean_unsigned_to_nat(2u);
v_nbuckets_77_ = lean_nat_mul(v___x_75_, v___x_76_);
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_box(0);
v___x_80_ = lean_mk_array(v_nbuckets_77_, v___x_79_);
v___x_81_ = lean_array_propagate_mark(v_data_74_, v___x_80_);
v___x_82_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(v___x_78_, v_data_74_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(lean_object* v_m_83_, lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
lean_object* v_size_86_; lean_object* v_buckets_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_130_; 
v_size_86_ = lean_ctor_get(v_m_83_, 0);
v_buckets_87_ = lean_ctor_get(v_m_83_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_m_83_);
if (v_isSharedCheck_130_ == 0)
{
v___x_89_ = v_m_83_;
v_isShared_90_ = v_isSharedCheck_130_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_buckets_87_);
lean_inc(v_size_86_);
lean_dec(v_m_83_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_130_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; uint64_t v_fold_95_; uint64_t v___x_96_; uint64_t v___x_97_; uint64_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; size_t v___x_103_; lean_object* v_bkt_104_; uint8_t v___x_105_; 
v___x_91_ = lean_array_get_size(v_buckets_87_);
v___x_92_ = l_Lean_Expr_hash(v_a_84_);
v___x_93_ = 32ULL;
v___x_94_ = lean_uint64_shift_right(v___x_92_, v___x_93_);
v_fold_95_ = lean_uint64_xor(v___x_92_, v___x_94_);
v___x_96_ = 16ULL;
v___x_97_ = lean_uint64_shift_right(v_fold_95_, v___x_96_);
v___x_98_ = lean_uint64_xor(v_fold_95_, v___x_97_);
v___x_99_ = lean_uint64_to_usize(v___x_98_);
v___x_100_ = lean_usize_of_nat(v___x_91_);
v___x_101_ = ((size_t)1ULL);
v___x_102_ = lean_usize_sub(v___x_100_, v___x_101_);
v___x_103_ = lean_usize_land(v___x_99_, v___x_102_);
v_bkt_104_ = lean_array_uget_borrowed(v_buckets_87_, v___x_103_);
v___x_105_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_84_, v_bkt_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v_size_x27_107_; lean_object* v___x_108_; lean_object* v_buckets_x27_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v_size_x27_107_ = lean_nat_add(v_size_86_, v___x_106_);
lean_dec(v_size_86_);
lean_inc(v_bkt_104_);
v___x_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_108_, 0, v_a_84_);
lean_ctor_set(v___x_108_, 1, v_b_85_);
lean_ctor_set(v___x_108_, 2, v_bkt_104_);
v_buckets_x27_109_ = lean_array_uset(v_buckets_87_, v___x_103_, v___x_108_);
v___x_110_ = lean_unsigned_to_nat(4u);
v___x_111_ = lean_nat_mul(v_size_x27_107_, v___x_110_);
v___x_112_ = lean_unsigned_to_nat(3u);
v___x_113_ = lean_nat_div(v___x_111_, v___x_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_array_get_size(v_buckets_x27_109_);
v___x_115_ = lean_nat_dec_le(v___x_113_, v___x_114_);
lean_dec(v___x_113_);
if (v___x_115_ == 0)
{
lean_object* v_val_116_; lean_object* v___x_118_; 
v_val_116_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(v_buckets_x27_109_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_val_116_);
lean_ctor_set(v___x_89_, 0, v_size_x27_107_);
v___x_118_ = v___x_89_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_size_x27_107_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_val_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
else
{
lean_object* v___x_121_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_buckets_x27_109_);
lean_ctor_set(v___x_89_, 0, v_size_x27_107_);
v___x_121_ = v___x_89_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_size_x27_107_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_buckets_x27_109_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
else
{
lean_object* v___x_123_; lean_object* v_buckets_x27_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
lean_inc(v_bkt_104_);
v___x_123_ = lean_box(0);
v_buckets_x27_124_ = lean_array_uset(v_buckets_87_, v___x_103_, v___x_123_);
v___x_125_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_84_, v_b_85_, v_bkt_104_);
v___x_126_ = lean_array_uset(v_buckets_x27_124_, v___x_103_, v___x_125_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v___x_126_);
v___x_128_ = v___x_89_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_size_86_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(lean_object* v_e_131_, uint8_t v_r_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_buckets_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_buckets_134_ = lean_ctor_get(v_a_133_, 1);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_array_get_size(v_buckets_134_);
v___x_137_ = lean_nat_dec_lt(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec_ref(v_e_131_);
v___x_138_ = lean_box(v_r_132_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_a_133_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = lean_box(v_r_132_);
v___x_141_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_a_133_, v_e_131_, v___x_140_);
v___x_142_ = lean_box(v_r_132_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg___boxed(lean_object* v_e_144_, lean_object* v_r_145_, lean_object* v_a_146_){
_start:
{
uint8_t v_r_boxed_147_; lean_object* v_res_148_; 
v_r_boxed_147_ = lean_unbox(v_r_145_);
v_res_148_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_144_, v_r_boxed_147_, v_a_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(lean_object* v_declNames_149_, lean_object* v_e_150_, uint8_t v_r_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_150_, v_r_151_, v_a_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___boxed(lean_object* v_declNames_154_, lean_object* v_e_155_, lean_object* v_r_156_, lean_object* v_a_157_){
_start:
{
uint8_t v_r_boxed_158_; lean_object* v_res_159_; 
v_r_boxed_158_ = lean_unbox(v_r_156_);
v_res_159_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(v_declNames_154_, v_e_155_, v_r_boxed_158_, v_a_157_);
lean_dec_ref(v_declNames_154_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0(lean_object* v_00_u03b2_160_, lean_object* v_m_161_, lean_object* v_a_162_, lean_object* v_b_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_m_161_, v_a_162_, v_b_163_);
return v___x_164_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(lean_object* v_00_u03b2_165_, lean_object* v_a_166_, lean_object* v_x_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_166_, v_x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_169_, lean_object* v_a_170_, lean_object* v_x_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(v_00_u03b2_169_, v_a_170_, v_x_171_);
lean_dec(v_x_171_);
lean_dec_ref(v_a_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1(lean_object* v_00_u03b2_174_, lean_object* v_data_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(v_data_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2(lean_object* v_00_u03b2_177_, lean_object* v_a_178_, lean_object* v_b_179_, lean_object* v_x_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_178_, v_b_179_, v_x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_182_, lean_object* v_i_183_, lean_object* v_source_184_, lean_object* v_target_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(v_i_183_, v_source_184_, v_target_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_188_, v_x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(lean_object* v_a_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
lean_object* v___x_193_; 
v___x_193_ = lean_box(0);
return v___x_193_;
}
else
{
lean_object* v_key_194_; lean_object* v_value_195_; lean_object* v_tail_196_; size_t v___x_197_; size_t v___x_198_; uint8_t v___x_199_; 
v_key_194_ = lean_ctor_get(v_x_192_, 0);
v_value_195_ = lean_ctor_get(v_x_192_, 1);
v_tail_196_ = lean_ctor_get(v_x_192_, 2);
v___x_197_ = lean_ptr_addr(v_key_194_);
v___x_198_ = lean_ptr_addr(v_a_191_);
v___x_199_ = lean_usize_dec_eq(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
v_x_192_ = v_tail_196_;
goto _start;
}
else
{
lean_object* v___x_201_; 
lean_inc(v_value_195_);
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v_value_195_);
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg___boxed(lean_object* v_a_202_, lean_object* v_x_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_202_, v_x_203_);
lean_dec(v_x_203_);
lean_dec_ref(v_a_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(lean_object* v_m_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_buckets_207_; lean_object* v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v_fold_212_; uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_buckets_207_ = lean_ctor_get(v_m_205_, 1);
v___x_208_ = lean_array_get_size(v_buckets_207_);
v___x_209_ = l_Lean_Expr_hash(v_a_206_);
v___x_210_ = 32ULL;
v___x_211_ = lean_uint64_shift_right(v___x_209_, v___x_210_);
v_fold_212_ = lean_uint64_xor(v___x_209_, v___x_211_);
v___x_213_ = 16ULL;
v___x_214_ = lean_uint64_shift_right(v_fold_212_, v___x_213_);
v___x_215_ = lean_uint64_xor(v_fold_212_, v___x_214_);
v___x_216_ = lean_uint64_to_usize(v___x_215_);
v___x_217_ = lean_usize_of_nat(v___x_208_);
v___x_218_ = ((size_t)1ULL);
v___x_219_ = lean_usize_sub(v___x_217_, v___x_218_);
v___x_220_ = lean_usize_land(v___x_216_, v___x_219_);
v___x_221_ = lean_array_uget_borrowed(v_buckets_207_, v___x_220_);
v___x_222_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_206_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg___boxed(lean_object* v_m_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_223_, v_a_224_);
lean_dec_ref(v_a_224_);
lean_dec_ref(v_m_223_);
return v_res_225_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(lean_object* v_a_226_, lean_object* v_as_227_, size_t v_i_228_, size_t v_stop_229_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = lean_usize_dec_eq(v_i_228_, v_stop_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_array_uget_borrowed(v_as_227_, v_i_228_);
v___x_232_ = lean_name_eq(v_a_226_, v___x_231_);
if (v___x_232_ == 0)
{
size_t v___x_233_; size_t v___x_234_; 
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_add(v_i_228_, v___x_233_);
v_i_228_ = v___x_234_;
goto _start;
}
else
{
return v___x_232_;
}
}
else
{
uint8_t v___x_236_; 
v___x_236_ = 0;
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0___boxed(lean_object* v_a_237_, lean_object* v_as_238_, lean_object* v_i_239_, lean_object* v_stop_240_){
_start:
{
size_t v_i_boxed_241_; size_t v_stop_boxed_242_; uint8_t v_res_243_; lean_object* v_r_244_; 
v_i_boxed_241_ = lean_unbox_usize(v_i_239_);
lean_dec(v_i_239_);
v_stop_boxed_242_ = lean_unbox_usize(v_stop_240_);
lean_dec(v_stop_240_);
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_237_, v_as_238_, v_i_boxed_241_, v_stop_boxed_242_);
lean_dec_ref(v_as_238_);
lean_dec(v_a_237_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(lean_object* v_as_245_, lean_object* v_a_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_array_get_size(v_as_245_);
v___x_249_ = lean_nat_dec_lt(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
return v___x_249_;
}
else
{
if (v___x_249_ == 0)
{
return v___x_249_;
}
else
{
size_t v___x_250_; size_t v___x_251_; uint8_t v___x_252_; 
v___x_250_ = ((size_t)0ULL);
v___x_251_ = lean_usize_of_nat(v___x_248_);
v___x_252_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_246_, v_as_245_, v___x_250_, v___x_251_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0___boxed(lean_object* v_as_253_, lean_object* v_a_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(v_as_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_as_253_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object* v_declNames_257_, lean_object* v_e_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___y_261_; lean_object* v___y_267_; lean_object* v___y_273_; lean_object* v_d_279_; lean_object* v_b_280_; lean_object* v___y_281_; lean_object* v_buckets_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_buckets_330_ = lean_ctor_get(v_a_259_, 1);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = lean_array_get_size(v_buckets_330_);
v___x_333_ = lean_nat_dec_lt(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
goto v___jp_287_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_a_259_, v_e_258_);
if (lean_obj_tag(v___x_334_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_336_; 
lean_dec_ref(v_e_258_);
v_val_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v___x_334_, 1);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_val_335_);
lean_ctor_set(v___x_336_, 1, v_a_259_);
return v___x_336_;
}
else
{
lean_dec(v___x_334_);
goto v___jp_287_;
}
}
v___jp_260_:
{
lean_object* v_fst_262_; lean_object* v_snd_263_; uint8_t v___x_264_; lean_object* v___x_265_; 
v_fst_262_ = lean_ctor_get(v___y_261_, 0);
lean_inc(v_fst_262_);
v_snd_263_ = lean_ctor_get(v___y_261_, 1);
lean_inc(v_snd_263_);
lean_dec_ref(v___y_261_);
v___x_264_ = lean_unbox(v_fst_262_);
lean_dec(v_fst_262_);
v___x_265_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_258_, v___x_264_, v_snd_263_);
return v___x_265_;
}
v___jp_266_:
{
lean_object* v_fst_268_; lean_object* v_snd_269_; uint8_t v___x_270_; lean_object* v___x_271_; 
v_fst_268_ = lean_ctor_get(v___y_267_, 0);
lean_inc(v_fst_268_);
v_snd_269_ = lean_ctor_get(v___y_267_, 1);
lean_inc(v_snd_269_);
lean_dec_ref(v___y_267_);
v___x_270_ = lean_unbox(v_fst_268_);
lean_dec(v_fst_268_);
v___x_271_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_258_, v___x_270_, v_snd_269_);
return v___x_271_;
}
v___jp_272_:
{
lean_object* v_fst_274_; lean_object* v_snd_275_; uint8_t v___x_276_; lean_object* v___x_277_; 
v_fst_274_ = lean_ctor_get(v___y_273_, 0);
lean_inc(v_fst_274_);
v_snd_275_ = lean_ctor_get(v___y_273_, 1);
lean_inc(v_snd_275_);
lean_dec_ref(v___y_273_);
v___x_276_ = lean_unbox(v_fst_274_);
lean_dec(v_fst_274_);
v___x_277_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_258_, v___x_276_, v_snd_275_);
return v___x_277_;
}
v___jp_278_:
{
lean_object* v___x_282_; lean_object* v_fst_283_; uint8_t v___x_284_; 
v___x_282_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_257_, v_d_279_, v___y_281_);
v_fst_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_fst_283_);
v___x_284_ = lean_unbox(v_fst_283_);
lean_dec(v_fst_283_);
if (v___x_284_ == 0)
{
lean_object* v_snd_285_; lean_object* v___x_286_; 
v_snd_285_ = lean_ctor_get(v___x_282_, 1);
lean_inc(v_snd_285_);
lean_dec_ref(v___x_282_);
v___x_286_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_257_, v_b_280_, v_snd_285_);
v___y_273_ = v___x_286_;
goto v___jp_272_;
}
else
{
lean_dec_ref(v_b_280_);
v___y_273_ = v___x_282_;
goto v___jp_272_;
}
}
v___jp_287_:
{
switch(lean_obj_tag(v_e_258_))
{
case 4:
{
lean_object* v_declName_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_declName_288_ = lean_ctor_get(v_e_258_, 0);
lean_inc(v_declName_288_);
lean_dec_ref_known(v_e_258_, 2);
v___x_289_ = l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(v_declNames_257_, v_declName_288_);
lean_dec(v_declName_288_);
v___x_290_ = lean_box(v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_a_259_);
return v___x_291_;
}
case 5:
{
lean_object* v_fn_292_; lean_object* v_arg_293_; lean_object* v___x_294_; lean_object* v_fst_295_; uint8_t v___x_296_; 
v_fn_292_ = lean_ctor_get(v_e_258_, 0);
v_arg_293_ = lean_ctor_get(v_e_258_, 1);
lean_inc_ref(v_fn_292_);
v___x_294_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_257_, v_fn_292_, v_a_259_);
v_fst_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_fst_295_);
v___x_296_ = lean_unbox(v_fst_295_);
lean_dec(v_fst_295_);
if (v___x_296_ == 0)
{
lean_object* v_snd_297_; lean_object* v___x_298_; 
v_snd_297_ = lean_ctor_get(v___x_294_, 1);
lean_inc(v_snd_297_);
lean_dec_ref(v___x_294_);
lean_inc_ref(v_arg_293_);
v___x_298_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_257_, v_arg_293_, v_snd_297_);
v___y_267_ = v___x_298_;
goto v___jp_266_;
}
else
{
v___y_267_ = v___x_294_;
goto v___jp_266_;
}
}
case 6:
{
lean_object* v_binderType_299_; lean_object* v_body_300_; 
v_binderType_299_ = lean_ctor_get(v_e_258_, 1);
v_body_300_ = lean_ctor_get(v_e_258_, 2);
lean_inc_ref(v_body_300_);
lean_inc_ref(v_binderType_299_);
v_d_279_ = v_binderType_299_;
v_b_280_ = v_body_300_;
v___y_281_ = v_a_259_;
goto v___jp_278_;
}
case 7:
{
lean_object* v_binderType_301_; lean_object* v_body_302_; 
v_binderType_301_ = lean_ctor_get(v_e_258_, 1);
v_body_302_ = lean_ctor_get(v_e_258_, 2);
lean_inc_ref(v_body_302_);
lean_inc_ref(v_binderType_301_);
v_d_279_ = v_binderType_301_;
v_b_280_ = v_body_302_;
v___y_281_ = v_a_259_;
goto v___jp_278_;
}
case 8:
{
lean_object* v_type_303_; lean_object* v_value_304_; lean_object* v_body_305_; lean_object* v___x_306_; lean_object* v_fst_307_; uint8_t v___x_308_; 
v_type_303_ = lean_ctor_get(v_e_258_, 1);
v_value_304_ = lean_ctor_get(v_e_258_, 2);
v_body_305_ = lean_ctor_get(v_e_258_, 3);
lean_inc_ref(v_type_303_);
v___x_306_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_257_, v_type_303_, v_a_259_);
v_fst_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_fst_307_);
v___x_308_ = lean_unbox(v_fst_307_);
lean_dec(v_fst_307_);
if (v___x_308_ == 0)
{
lean_object* v_snd_309_; lean_object* v___x_310_; lean_object* v_fst_311_; uint8_t v___x_312_; 
v_snd_309_ = lean_ctor_get(v___x_306_, 1);
lean_inc(v_snd_309_);
lean_dec_ref(v___x_306_);
lean_inc_ref(v_value_304_);
v___x_310_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_257_, v_value_304_, v_snd_309_);
v_fst_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_fst_311_);
v___x_312_ = lean_unbox(v_fst_311_);
lean_dec(v_fst_311_);
if (v___x_312_ == 0)
{
lean_object* v_snd_313_; lean_object* v___x_314_; 
v_snd_313_ = lean_ctor_get(v___x_310_, 1);
lean_inc(v_snd_313_);
lean_dec_ref(v___x_310_);
lean_inc_ref(v_body_305_);
v___x_314_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_257_, v_body_305_, v_snd_313_);
v___y_261_ = v___x_314_;
goto v___jp_260_;
}
else
{
v___y_261_ = v___x_310_;
goto v___jp_260_;
}
}
else
{
v___y_261_ = v___x_306_;
goto v___jp_260_;
}
}
case 10:
{
lean_object* v_expr_315_; lean_object* v___x_316_; lean_object* v_fst_317_; lean_object* v_snd_318_; uint8_t v___x_319_; lean_object* v___x_320_; 
v_expr_315_ = lean_ctor_get(v_e_258_, 1);
lean_inc_ref(v_expr_315_);
v___x_316_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_257_, v_expr_315_, v_a_259_);
v_fst_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_fst_317_);
v_snd_318_ = lean_ctor_get(v___x_316_, 1);
lean_inc(v_snd_318_);
lean_dec_ref(v___x_316_);
v___x_319_ = lean_unbox(v_fst_317_);
lean_dec(v_fst_317_);
v___x_320_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_258_, v___x_319_, v_snd_318_);
return v___x_320_;
}
case 11:
{
lean_object* v_struct_321_; lean_object* v___x_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; uint8_t v___x_325_; lean_object* v___x_326_; 
v_struct_321_ = lean_ctor_get(v_e_258_, 2);
lean_inc_ref(v_struct_321_);
v___x_322_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_257_, v_struct_321_, v_a_259_);
v_fst_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_fst_323_);
v_snd_324_ = lean_ctor_get(v___x_322_, 1);
lean_inc(v_snd_324_);
lean_dec_ref(v___x_322_);
v___x_325_ = lean_unbox(v_fst_323_);
lean_dec(v_fst_323_);
v___x_326_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_258_, v___x_325_, v_snd_324_);
return v___x_326_;
}
default: 
{
uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v_e_258_);
v___x_327_ = 0;
v___x_328_ = lean_box(v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_a_259_);
return v___x_329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe___boxed(lean_object* v_declNames_337_, lean_object* v_e_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_337_, v_e_338_, v_a_339_);
lean_dec_ref(v_declNames_337_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(lean_object* v_00_u03b2_341_, lean_object* v_m_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_342_, v_a_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___boxed(lean_object* v_00_u03b2_345_, lean_object* v_m_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(v_00_u03b2_345_, v_m_346_, v_a_347_);
lean_dec_ref(v_a_347_);
lean_dec_ref(v_m_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(lean_object* v_00_u03b2_349_, lean_object* v_a_350_, lean_object* v_x_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_350_, v_x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___boxed(lean_object* v_00_u03b2_353_, lean_object* v_a_354_, lean_object* v_x_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(v_00_u03b2_353_, v_a_354_, v_x_355_);
lean_dec(v_x_355_);
lean_dec_ref(v_a_354_);
return v_res_356_;
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
