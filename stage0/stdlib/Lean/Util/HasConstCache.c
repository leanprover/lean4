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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_10_;
v_res_10_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_1_, v_x_2_);
stack->m_num = v_res_10_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg___boxed(lean_object* v_a_11_, lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_11_, v_x_12_);
lean_dec(v_x_12_);
lean_dec_ref(v_a_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(lean_object* v_a_15_, lean_object* v_b_16_, lean_object* v_x_17_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_dec(v_b_16_);
lean_dec_ref(v_a_15_);
return v_x_17_;
}
else
{
lean_object* v_key_18_; lean_object* v_value_19_; lean_object* v_tail_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_34_; 
v_key_18_ = lean_ctor_get(v_x_17_, 0);
v_value_19_ = lean_ctor_get(v_x_17_, 1);
v_tail_20_ = lean_ctor_get(v_x_17_, 2);
v_isSharedCheck_34_ = !lean_is_exclusive(v_x_17_);
if (v_isSharedCheck_34_ == 0)
{
v___x_22_ = v_x_17_;
v_isShared_23_ = v_isSharedCheck_34_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_tail_20_);
lean_inc(v_value_19_);
lean_inc(v_key_18_);
lean_dec(v_x_17_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_34_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
size_t v___x_24_; size_t v___x_25_; uint8_t v___x_26_; 
v___x_24_ = lean_ptr_addr(v_key_18_);
v___x_25_ = lean_ptr_addr(v_a_15_);
v___x_26_ = lean_usize_dec_eq(v___x_24_, v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_27_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_15_, v_b_16_, v_tail_20_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 2, v___x_27_);
v___x_29_ = v___x_22_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_key_18_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_value_19_);
lean_ctor_set(v_reuseFailAlloc_30_, 2, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
else
{
lean_object* v___x_32_; 
lean_dec(v_value_19_);
lean_dec(v_key_18_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v_b_16_);
lean_ctor_set(v___x_22_, 0, v_a_15_);
v___x_32_ = v___x_22_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_a_15_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v_b_16_);
lean_ctor_set(v_reuseFailAlloc_33_, 2, v_tail_20_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
return v_x_35_;
}
else
{
lean_object* v_key_37_; lean_object* v_value_38_; lean_object* v_tail_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_62_; 
v_key_37_ = lean_ctor_get(v_x_36_, 0);
v_value_38_ = lean_ctor_get(v_x_36_, 1);
v_tail_39_ = lean_ctor_get(v_x_36_, 2);
v_isSharedCheck_62_ = !lean_is_exclusive(v_x_36_);
if (v_isSharedCheck_62_ == 0)
{
v___x_41_ = v_x_36_;
v_isShared_42_ = v_isSharedCheck_62_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_tail_39_);
lean_inc(v_value_38_);
lean_inc(v_key_37_);
lean_dec(v_x_36_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_62_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v_fold_47_; uint64_t v___x_48_; uint64_t v___x_49_; uint64_t v___x_50_; size_t v___x_51_; size_t v___x_52_; size_t v___x_53_; size_t v___x_54_; size_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_43_ = lean_array_get_size(v_x_35_);
v___x_44_ = l_Lean_Expr_hash(v_key_37_);
v___x_45_ = 32ULL;
v___x_46_ = lean_uint64_shift_right(v___x_44_, v___x_45_);
v_fold_47_ = lean_uint64_xor(v___x_44_, v___x_46_);
v___x_48_ = 16ULL;
v___x_49_ = lean_uint64_shift_right(v_fold_47_, v___x_48_);
v___x_50_ = lean_uint64_xor(v_fold_47_, v___x_49_);
v___x_51_ = lean_uint64_to_usize(v___x_50_);
v___x_52_ = lean_usize_of_nat(v___x_43_);
v___x_53_ = ((size_t)1ULL);
v___x_54_ = lean_usize_sub(v___x_52_, v___x_53_);
v___x_55_ = lean_usize_land(v___x_51_, v___x_54_);
v___x_56_ = lean_array_uget_borrowed(v_x_35_, v___x_55_);
lean_inc(v___x_56_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 2, v___x_56_);
v___x_58_ = v___x_41_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_key_37_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_value_38_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v___x_56_);
v___x_58_ = v_reuseFailAlloc_61_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; 
v___x_59_ = lean_array_uset(v_x_35_, v___x_55_, v___x_58_);
v_x_35_ = v___x_59_;
v_x_36_ = v_tail_39_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(lean_object* v_i_63_, lean_object* v_source_64_, lean_object* v_target_65_){
_start:
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_array_get_size(v_source_64_);
v___x_67_ = lean_nat_dec_lt(v_i_63_, v___x_66_);
if (v___x_67_ == 0)
{
lean_dec_ref(v_source_64_);
lean_dec(v_i_63_);
return v_target_65_;
}
else
{
lean_object* v_es_68_; lean_object* v___x_69_; lean_object* v_source_70_; lean_object* v_target_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_es_68_ = lean_array_fget(v_source_64_, v_i_63_);
v___x_69_ = lean_box(0);
v_source_70_ = lean_array_fset(v_source_64_, v_i_63_, v___x_69_);
v_target_71_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_target_65_, v_es_68_);
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_add(v_i_63_, v___x_72_);
lean_dec(v_i_63_);
v_i_63_ = v___x_73_;
v_source_64_ = v_source_70_;
v_target_65_ = v_target_71_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(lean_object* v_data_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v_nbuckets_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_76_ = lean_array_get_size(v_data_75_);
v___x_77_ = lean_unsigned_to_nat(2u);
v_nbuckets_78_ = lean_nat_mul(v___x_76_, v___x_77_);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_box(0);
v___x_81_ = lean_mk_array(v_nbuckets_78_, v___x_80_);
v___x_82_ = lean_array_propagate_mark(v_data_75_, v___x_81_);
v___x_83_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(v___x_79_, v_data_75_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(lean_object* v_m_84_, lean_object* v_a_85_, lean_object* v_b_86_){
_start:
{
lean_object* v_size_87_; lean_object* v_buckets_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_131_; 
v_size_87_ = lean_ctor_get(v_m_84_, 0);
v_buckets_88_ = lean_ctor_get(v_m_84_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_m_84_);
if (v_isSharedCheck_131_ == 0)
{
v___x_90_ = v_m_84_;
v_isShared_91_ = v_isSharedCheck_131_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_buckets_88_);
lean_inc(v_size_87_);
lean_dec(v_m_84_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_131_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; uint64_t v___x_95_; uint64_t v_fold_96_; uint64_t v___x_97_; uint64_t v___x_98_; uint64_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; size_t v___x_103_; size_t v___x_104_; lean_object* v_bkt_105_; uint8_t v___x_106_; 
v___x_92_ = lean_array_get_size(v_buckets_88_);
v___x_93_ = l_Lean_Expr_hash(v_a_85_);
v___x_94_ = 32ULL;
v___x_95_ = lean_uint64_shift_right(v___x_93_, v___x_94_);
v_fold_96_ = lean_uint64_xor(v___x_93_, v___x_95_);
v___x_97_ = 16ULL;
v___x_98_ = lean_uint64_shift_right(v_fold_96_, v___x_97_);
v___x_99_ = lean_uint64_xor(v_fold_96_, v___x_98_);
v___x_100_ = lean_uint64_to_usize(v___x_99_);
v___x_101_ = lean_usize_of_nat(v___x_92_);
v___x_102_ = ((size_t)1ULL);
v___x_103_ = lean_usize_sub(v___x_101_, v___x_102_);
v___x_104_ = lean_usize_land(v___x_100_, v___x_103_);
v_bkt_105_ = lean_array_uget_borrowed(v_buckets_88_, v___x_104_);
v___x_106_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_85_, v_bkt_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v_size_x27_108_; lean_object* v___x_109_; lean_object* v_buckets_x27_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_107_ = lean_unsigned_to_nat(1u);
v_size_x27_108_ = lean_nat_add(v_size_87_, v___x_107_);
lean_dec(v_size_87_);
lean_inc(v_bkt_105_);
v___x_109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_109_, 0, v_a_85_);
lean_ctor_set(v___x_109_, 1, v_b_86_);
lean_ctor_set(v___x_109_, 2, v_bkt_105_);
v_buckets_x27_110_ = lean_array_uset(v_buckets_88_, v___x_104_, v___x_109_);
v___x_111_ = lean_unsigned_to_nat(4u);
v___x_112_ = lean_nat_mul(v_size_x27_108_, v___x_111_);
v___x_113_ = lean_unsigned_to_nat(3u);
v___x_114_ = lean_nat_div(v___x_112_, v___x_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_array_get_size(v_buckets_x27_110_);
v___x_116_ = lean_nat_dec_le(v___x_114_, v___x_115_);
lean_dec(v___x_114_);
if (v___x_116_ == 0)
{
lean_object* v_val_117_; lean_object* v___x_119_; 
v_val_117_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(v_buckets_x27_110_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v_val_117_);
lean_ctor_set(v___x_90_, 0, v_size_x27_108_);
v___x_119_ = v___x_90_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_size_x27_108_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_val_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
else
{
lean_object* v___x_122_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v_buckets_x27_110_);
lean_ctor_set(v___x_90_, 0, v_size_x27_108_);
v___x_122_ = v___x_90_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_size_x27_108_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_buckets_x27_110_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
else
{
lean_object* v___x_124_; lean_object* v_buckets_x27_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
lean_inc(v_bkt_105_);
v___x_124_ = lean_box(0);
v_buckets_x27_125_ = lean_array_uset(v_buckets_88_, v___x_104_, v___x_124_);
v___x_126_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_85_, v_b_86_, v_bkt_105_);
v___x_127_ = lean_array_uset(v_buckets_x27_125_, v___x_104_, v___x_126_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v___x_127_);
v___x_129_ = v___x_90_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_size_87_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(lean_object* v_e_132_, uint8_t v_r_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_buckets_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_buckets_135_ = lean_ctor_get(v_a_134_, 1);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_array_get_size(v_buckets_135_);
v___x_138_ = lean_nat_dec_lt(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec_ref(v_e_132_);
v___x_139_ = lean_box(v_r_133_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v_a_134_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = lean_box(v_r_133_);
v___x_142_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_a_134_, v_e_132_, v___x_141_);
v___x_143_ = lean_box(v_r_133_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
return v___x_144_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_132_ = stack[0].m_obj;
uint8_t v_r_133_ = stack[1].m_num;
lean_object* v_a_134_ = stack[2].m_obj;
lean_object* v_res_145_;
v_res_145_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_132_, v_r_133_, v_a_134_);
stack->m_obj
 = v_res_145_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg___boxed(lean_object* v_e_146_, lean_object* v_r_147_, lean_object* v_a_148_){
_start:
{
uint8_t v_r_boxed_149_; lean_object* v_res_150_; 
v_r_boxed_149_ = lean_unbox(v_r_147_);
v_res_150_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_146_, v_r_boxed_149_, v_a_148_);
return v_res_150_;
}
}
lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(lean_object* v_declNames_151_, lean_object* v_e_152_, uint8_t v_r_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_152_, v_r_153_, v_a_154_);
return v___x_155_;
}
}
LEAN_EXPORT void l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_151_ = stack[0].m_obj;
lean_object* v_e_152_ = stack[1].m_obj;
uint8_t v_r_153_ = stack[2].m_num;
lean_object* v_a_154_ = stack[3].m_obj;
lean_object* v_res_156_;
v_res_156_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(v_declNames_151_, v_e_152_, v_r_153_, v_a_154_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___boxed(lean_object* v_declNames_157_, lean_object* v_e_158_, lean_object* v_r_159_, lean_object* v_a_160_){
_start:
{
uint8_t v_r_boxed_161_; lean_object* v_res_162_; 
v_r_boxed_161_ = lean_unbox(v_r_159_);
v_res_162_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(v_declNames_157_, v_e_158_, v_r_boxed_161_, v_a_160_);
lean_dec_ref(v_declNames_157_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0(lean_object* v_00_u03b2_163_, lean_object* v_m_164_, lean_object* v_a_165_, lean_object* v_b_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_m_164_, v_a_165_, v_b_166_);
return v___x_167_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(lean_object* v_00_u03b2_168_, lean_object* v_a_169_, lean_object* v_x_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_169_, v_x_170_);
return v___x_171_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_169_ = stack[1].m_obj;
lean_object* v_x_170_ = stack[2].m_obj;
uint8_t v_res_172_;
v_res_172_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(lean_box(0), v_a_169_, v_x_170_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_173_, lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(v_00_u03b2_173_, v_a_174_, v_x_175_);
lean_dec(v_x_175_);
lean_dec_ref(v_a_174_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1(lean_object* v_00_u03b2_178_, lean_object* v_data_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(v_data_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2(lean_object* v_00_u03b2_181_, lean_object* v_a_182_, lean_object* v_b_183_, lean_object* v_x_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_182_, v_b_183_, v_x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_186_, lean_object* v_i_187_, lean_object* v_source_188_, lean_object* v_target_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(v_i_187_, v_source_188_, v_target_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_191_, lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_192_, v_x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(lean_object* v_a_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v___x_197_; 
v___x_197_ = lean_box(0);
return v___x_197_;
}
else
{
lean_object* v_key_198_; lean_object* v_value_199_; lean_object* v_tail_200_; size_t v___x_201_; size_t v___x_202_; uint8_t v___x_203_; 
v_key_198_ = lean_ctor_get(v_x_196_, 0);
v_value_199_ = lean_ctor_get(v_x_196_, 1);
v_tail_200_ = lean_ctor_get(v_x_196_, 2);
v___x_201_ = lean_ptr_addr(v_key_198_);
v___x_202_ = lean_ptr_addr(v_a_195_);
v___x_203_ = lean_usize_dec_eq(v___x_201_, v___x_202_);
if (v___x_203_ == 0)
{
v_x_196_ = v_tail_200_;
goto _start;
}
else
{
lean_object* v___x_205_; 
lean_inc(v_value_199_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v_value_199_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg___boxed(lean_object* v_a_206_, lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_206_, v_x_207_);
lean_dec(v_x_207_);
lean_dec_ref(v_a_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(lean_object* v_m_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_buckets_211_; lean_object* v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v___x_215_; uint64_t v_fold_216_; uint64_t v___x_217_; uint64_t v___x_218_; uint64_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_buckets_211_ = lean_ctor_get(v_m_209_, 1);
v___x_212_ = lean_array_get_size(v_buckets_211_);
v___x_213_ = l_Lean_Expr_hash(v_a_210_);
v___x_214_ = 32ULL;
v___x_215_ = lean_uint64_shift_right(v___x_213_, v___x_214_);
v_fold_216_ = lean_uint64_xor(v___x_213_, v___x_215_);
v___x_217_ = 16ULL;
v___x_218_ = lean_uint64_shift_right(v_fold_216_, v___x_217_);
v___x_219_ = lean_uint64_xor(v_fold_216_, v___x_218_);
v___x_220_ = lean_uint64_to_usize(v___x_219_);
v___x_221_ = lean_usize_of_nat(v___x_212_);
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_sub(v___x_221_, v___x_222_);
v___x_224_ = lean_usize_land(v___x_220_, v___x_223_);
v___x_225_ = lean_array_uget_borrowed(v_buckets_211_, v___x_224_);
v___x_226_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_210_, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg___boxed(lean_object* v_m_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_227_, v_a_228_);
lean_dec_ref(v_a_228_);
lean_dec_ref(v_m_227_);
return v_res_229_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(lean_object* v_a_230_, lean_object* v_as_231_, size_t v_i_232_, size_t v_stop_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_usize_dec_eq(v_i_232_, v_stop_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_array_uget_borrowed(v_as_231_, v_i_232_);
v___x_236_ = lean_name_eq(v_a_230_, v___x_235_);
if (v___x_236_ == 0)
{
size_t v___x_237_; size_t v___x_238_; 
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_add(v_i_232_, v___x_237_);
v_i_232_ = v___x_238_;
goto _start;
}
else
{
return v___x_236_;
}
}
else
{
uint8_t v___x_240_; 
v___x_240_ = 0;
return v___x_240_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_230_ = stack[0].m_obj;
lean_object* v_as_231_ = stack[1].m_obj;
size_t v_i_232_ = stack[2].m_num;
size_t v_stop_233_ = stack[3].m_num;
uint8_t v_res_241_;
v_res_241_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_230_, v_as_231_, v_i_232_, v_stop_233_);
stack->m_num = v_res_241_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0___boxed(lean_object* v_a_242_, lean_object* v_as_243_, lean_object* v_i_244_, lean_object* v_stop_245_){
_start:
{
size_t v_i_boxed_246_; size_t v_stop_boxed_247_; uint8_t v_res_248_; lean_object* v_r_249_; 
v_i_boxed_246_ = lean_unbox_usize(v_i_244_);
lean_dec(v_i_244_);
v_stop_boxed_247_ = lean_unbox_usize(v_stop_245_);
lean_dec(v_stop_245_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_242_, v_as_243_, v_i_boxed_246_, v_stop_boxed_247_);
lean_dec_ref(v_as_243_);
lean_dec(v_a_242_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
uint8_t l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(lean_object* v_as_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_array_get_size(v_as_250_);
v___x_254_ = lean_nat_dec_lt(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
return v___x_254_;
}
else
{
if (v___x_254_ == 0)
{
return v___x_254_;
}
else
{
size_t v___x_255_; size_t v___x_256_; uint8_t v___x_257_; 
v___x_255_ = ((size_t)0ULL);
v___x_256_ = lean_usize_of_nat(v___x_253_);
v___x_257_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_251_, v_as_250_, v___x_255_, v___x_256_);
return v___x_257_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_250_ = stack[0].m_obj;
lean_object* v_a_251_ = stack[1].m_obj;
uint8_t v_res_258_;
v_res_258_ = l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(v_as_250_, v_a_251_);
stack->m_num = v_res_258_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0___boxed(lean_object* v_as_259_, lean_object* v_a_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(v_as_259_, v_a_260_);
lean_dec(v_a_260_);
lean_dec_ref(v_as_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object* v_declNames_263_, lean_object* v_e_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___y_267_; lean_object* v___y_273_; lean_object* v___y_279_; lean_object* v_d_285_; lean_object* v_b_286_; lean_object* v___y_287_; lean_object* v_buckets_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_buckets_336_ = lean_ctor_get(v_a_265_, 1);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_array_get_size(v_buckets_336_);
v___x_339_ = lean_nat_dec_lt(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
goto v___jp_293_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_a_265_, v_e_264_);
if (lean_obj_tag(v___x_340_) == 1)
{
lean_object* v_val_341_; lean_object* v___x_342_; 
lean_dec_ref(v_e_264_);
v_val_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_val_341_);
lean_dec_ref_known(v___x_340_, 1);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_val_341_);
lean_ctor_set(v___x_342_, 1, v_a_265_);
return v___x_342_;
}
else
{
lean_dec(v___x_340_);
goto v___jp_293_;
}
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
v___x_271_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_264_, v___x_270_, v_snd_269_);
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
v___x_277_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_264_, v___x_276_, v_snd_275_);
return v___x_277_;
}
v___jp_278_:
{
lean_object* v_fst_280_; lean_object* v_snd_281_; uint8_t v___x_282_; lean_object* v___x_283_; 
v_fst_280_ = lean_ctor_get(v___y_279_, 0);
lean_inc(v_fst_280_);
v_snd_281_ = lean_ctor_get(v___y_279_, 1);
lean_inc(v_snd_281_);
lean_dec_ref(v___y_279_);
v___x_282_ = lean_unbox(v_fst_280_);
lean_dec(v_fst_280_);
v___x_283_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_264_, v___x_282_, v_snd_281_);
return v___x_283_;
}
v___jp_284_:
{
lean_object* v___x_288_; lean_object* v_fst_289_; uint8_t v___x_290_; 
v___x_288_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_263_, v_d_285_, v___y_287_);
v_fst_289_ = lean_ctor_get(v___x_288_, 0);
v___x_290_ = lean_unbox(v_fst_289_);
if (v___x_290_ == 0)
{
lean_object* v_snd_291_; lean_object* v___x_292_; 
v_snd_291_ = lean_ctor_get(v___x_288_, 1);
lean_inc(v_snd_291_);
lean_dec_ref(v___x_288_);
v___x_292_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_263_, v_b_286_, v_snd_291_);
v___y_279_ = v___x_292_;
goto v___jp_278_;
}
else
{
lean_dec_ref(v_b_286_);
v___y_279_ = v___x_288_;
goto v___jp_278_;
}
}
v___jp_293_:
{
switch(lean_obj_tag(v_e_264_))
{
case 4:
{
lean_object* v_declName_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_declName_294_ = lean_ctor_get(v_e_264_, 0);
lean_inc(v_declName_294_);
lean_dec_ref_known(v_e_264_, 2);
v___x_295_ = l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(v_declNames_263_, v_declName_294_);
lean_dec(v_declName_294_);
v___x_296_ = lean_box(v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_a_265_);
return v___x_297_;
}
case 5:
{
lean_object* v_fn_298_; lean_object* v_arg_299_; lean_object* v___x_300_; lean_object* v_fst_301_; uint8_t v___x_302_; 
v_fn_298_ = lean_ctor_get(v_e_264_, 0);
v_arg_299_ = lean_ctor_get(v_e_264_, 1);
lean_inc_ref(v_fn_298_);
v___x_300_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_263_, v_fn_298_, v_a_265_);
v_fst_301_ = lean_ctor_get(v___x_300_, 0);
v___x_302_ = lean_unbox(v_fst_301_);
if (v___x_302_ == 0)
{
lean_object* v_snd_303_; lean_object* v___x_304_; 
v_snd_303_ = lean_ctor_get(v___x_300_, 1);
lean_inc(v_snd_303_);
lean_dec_ref(v___x_300_);
lean_inc_ref(v_arg_299_);
v___x_304_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_263_, v_arg_299_, v_snd_303_);
v___y_273_ = v___x_304_;
goto v___jp_272_;
}
else
{
v___y_273_ = v___x_300_;
goto v___jp_272_;
}
}
case 6:
{
lean_object* v_binderType_305_; lean_object* v_body_306_; 
v_binderType_305_ = lean_ctor_get(v_e_264_, 1);
v_body_306_ = lean_ctor_get(v_e_264_, 2);
lean_inc_ref(v_body_306_);
lean_inc_ref(v_binderType_305_);
v_d_285_ = v_binderType_305_;
v_b_286_ = v_body_306_;
v___y_287_ = v_a_265_;
goto v___jp_284_;
}
case 7:
{
lean_object* v_binderType_307_; lean_object* v_body_308_; 
v_binderType_307_ = lean_ctor_get(v_e_264_, 1);
v_body_308_ = lean_ctor_get(v_e_264_, 2);
lean_inc_ref(v_body_308_);
lean_inc_ref(v_binderType_307_);
v_d_285_ = v_binderType_307_;
v_b_286_ = v_body_308_;
v___y_287_ = v_a_265_;
goto v___jp_284_;
}
case 8:
{
lean_object* v_type_309_; lean_object* v_value_310_; lean_object* v_body_311_; lean_object* v___x_312_; lean_object* v_fst_313_; uint8_t v___x_314_; 
v_type_309_ = lean_ctor_get(v_e_264_, 1);
v_value_310_ = lean_ctor_get(v_e_264_, 2);
v_body_311_ = lean_ctor_get(v_e_264_, 3);
lean_inc_ref(v_type_309_);
v___x_312_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_263_, v_type_309_, v_a_265_);
v_fst_313_ = lean_ctor_get(v___x_312_, 0);
v___x_314_ = lean_unbox(v_fst_313_);
if (v___x_314_ == 0)
{
lean_object* v_snd_315_; lean_object* v___x_316_; lean_object* v_fst_317_; uint8_t v___x_318_; 
v_snd_315_ = lean_ctor_get(v___x_312_, 1);
lean_inc(v_snd_315_);
lean_dec_ref(v___x_312_);
lean_inc_ref(v_value_310_);
v___x_316_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_263_, v_value_310_, v_snd_315_);
v_fst_317_ = lean_ctor_get(v___x_316_, 0);
v___x_318_ = lean_unbox(v_fst_317_);
if (v___x_318_ == 0)
{
lean_object* v_snd_319_; lean_object* v___x_320_; 
v_snd_319_ = lean_ctor_get(v___x_316_, 1);
lean_inc(v_snd_319_);
lean_dec_ref(v___x_316_);
lean_inc_ref(v_body_311_);
v___x_320_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_263_, v_body_311_, v_snd_319_);
v___y_267_ = v___x_320_;
goto v___jp_266_;
}
else
{
v___y_267_ = v___x_316_;
goto v___jp_266_;
}
}
else
{
v___y_267_ = v___x_312_;
goto v___jp_266_;
}
}
case 10:
{
lean_object* v_expr_321_; lean_object* v___x_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; uint8_t v___x_325_; lean_object* v___x_326_; 
v_expr_321_ = lean_ctor_get(v_e_264_, 1);
lean_inc_ref(v_expr_321_);
v___x_322_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_263_, v_expr_321_, v_a_265_);
v_fst_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_fst_323_);
v_snd_324_ = lean_ctor_get(v___x_322_, 1);
lean_inc(v_snd_324_);
lean_dec_ref(v___x_322_);
v___x_325_ = lean_unbox(v_fst_323_);
lean_dec(v_fst_323_);
v___x_326_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_264_, v___x_325_, v_snd_324_);
return v___x_326_;
}
case 11:
{
lean_object* v_struct_327_; lean_object* v___x_328_; lean_object* v_fst_329_; lean_object* v_snd_330_; uint8_t v___x_331_; lean_object* v___x_332_; 
v_struct_327_ = lean_ctor_get(v_e_264_, 2);
lean_inc_ref(v_struct_327_);
v___x_328_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_263_, v_struct_327_, v_a_265_);
v_fst_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_fst_329_);
v_snd_330_ = lean_ctor_get(v___x_328_, 1);
lean_inc(v_snd_330_);
lean_dec_ref(v___x_328_);
v___x_331_ = lean_unbox(v_fst_329_);
lean_dec(v_fst_329_);
v___x_332_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_264_, v___x_331_, v_snd_330_);
return v___x_332_;
}
default: 
{
uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec_ref(v_e_264_);
v___x_333_ = 0;
v___x_334_ = lean_box(v___x_333_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_a_265_);
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HasConstCache_containsUnsafe___boxed(lean_object* v_declNames_343_, lean_object* v_e_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_343_, v_e_344_, v_a_345_);
lean_dec_ref(v_declNames_343_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(lean_object* v_00_u03b2_347_, lean_object* v_m_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_348_, v_a_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___boxed(lean_object* v_00_u03b2_351_, lean_object* v_m_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(v_00_u03b2_351_, v_m_352_, v_a_353_);
lean_dec_ref(v_a_353_);
lean_dec_ref(v_m_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(lean_object* v_00_u03b2_355_, lean_object* v_a_356_, lean_object* v_x_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_356_, v_x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___boxed(lean_object* v_00_u03b2_359_, lean_object* v_a_360_, lean_object* v_x_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(v_00_u03b2_359_, v_a_360_, v_x_361_);
lean_dec(v_x_361_);
lean_dec_ref(v_a_360_);
return v_res_362_;
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
