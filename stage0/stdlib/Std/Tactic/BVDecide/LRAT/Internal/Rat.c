// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Rat
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Rup public import Std.Tactic.BVDecide.LRAT.Internal.Add import Std.Tactic.Do import Std.Data.HashSet
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
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1;
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__9_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__9_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
return v_x_1_;
}
else
{
lean_object* v_key_3_; lean_object* v_value_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_28_; 
v_key_3_ = lean_ctor_get(v_x_2_, 0);
v_value_4_ = lean_ctor_get(v_x_2_, 1);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v_isSharedCheck_28_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_28_ == 0)
{
v___x_7_ = v_x_2_;
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_value_4_);
lean_inc(v_key_3_);
lean_dec(v_x_2_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; uint64_t v___x_10_; uint64_t v___x_11_; uint64_t v___x_12_; uint64_t v_fold_13_; uint64_t v___x_14_; uint64_t v___x_15_; uint64_t v___x_16_; size_t v___x_17_; size_t v___x_18_; size_t v___x_19_; size_t v___x_20_; size_t v___x_21_; lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_9_ = lean_array_get_size(v_x_1_);
v___x_10_ = lean_uint64_of_nat(v_key_3_);
v___x_11_ = 32ULL;
v___x_12_ = lean_uint64_shift_right(v___x_10_, v___x_11_);
v_fold_13_ = lean_uint64_xor(v___x_10_, v___x_12_);
v___x_14_ = 16ULL;
v___x_15_ = lean_uint64_shift_right(v_fold_13_, v___x_14_);
v___x_16_ = lean_uint64_xor(v_fold_13_, v___x_15_);
v___x_17_ = lean_uint64_to_usize(v___x_16_);
v___x_18_ = lean_usize_of_nat(v___x_9_);
v___x_19_ = ((size_t)1ULL);
v___x_20_ = lean_usize_sub(v___x_18_, v___x_19_);
v___x_21_ = lean_usize_land(v___x_17_, v___x_20_);
v___x_22_ = lean_array_uget_borrowed(v_x_1_, v___x_21_);
lean_inc(v___x_22_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 2, v___x_22_);
v___x_24_ = v___x_7_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_key_3_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_value_4_);
lean_ctor_set(v_reuseFailAlloc_27_, 2, v___x_22_);
v___x_24_ = v_reuseFailAlloc_27_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; 
v___x_25_ = lean_array_uset(v_x_1_, v___x_21_, v___x_24_);
v_x_1_ = v___x_25_;
v_x_2_ = v_tail_5_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_i_29_, lean_object* v_source_30_, lean_object* v_target_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_array_get_size(v_source_30_);
v___x_33_ = lean_nat_dec_lt(v_i_29_, v___x_32_);
if (v___x_33_ == 0)
{
lean_dec_ref(v_source_30_);
lean_dec(v_i_29_);
return v_target_31_;
}
else
{
lean_object* v_es_34_; lean_object* v___x_35_; lean_object* v_source_36_; lean_object* v_target_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_es_34_ = lean_array_fget(v_source_30_, v_i_29_);
v___x_35_ = lean_box(0);
v_source_36_ = lean_array_fset(v_source_30_, v_i_29_, v___x_35_);
v_target_37_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_target_31_, v_es_34_);
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_add(v_i_29_, v___x_38_);
lean_dec(v_i_29_);
v_i_29_ = v___x_39_;
v_source_30_ = v_source_36_;
v_target_31_ = v_target_37_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2___redArg(lean_object* v_data_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_nbuckets_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_42_ = lean_array_get_size(v_data_41_);
v___x_43_ = lean_unsigned_to_nat(2u);
v_nbuckets_44_ = lean_nat_mul(v___x_42_, v___x_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_box(0);
v___x_47_ = lean_mk_array(v_nbuckets_44_, v___x_46_);
v___x_48_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5___redArg(v___x_45_, v_data_41_, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(lean_object* v_a_49_, lean_object* v_x_50_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 0;
return v___x_51_;
}
else
{
lean_object* v_key_52_; lean_object* v_tail_53_; uint8_t v___x_54_; 
v_key_52_ = lean_ctor_get(v_x_50_, 0);
v_tail_53_ = lean_ctor_get(v_x_50_, 2);
v___x_54_ = lean_nat_dec_eq(v_key_52_, v_a_49_);
if (v___x_54_ == 0)
{
v_x_50_ = v_tail_53_;
goto _start;
}
else
{
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg___boxed(lean_object* v_a_56_, lean_object* v_x_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(v_a_56_, v_x_57_);
lean_dec(v_x_57_);
lean_dec(v_a_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1___redArg(lean_object* v_m_60_, lean_object* v_a_61_, lean_object* v_b_62_){
_start:
{
lean_object* v_size_63_; lean_object* v_buckets_64_; lean_object* v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v_fold_69_; uint64_t v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; lean_object* v_bkt_78_; uint8_t v___x_79_; 
v_size_63_ = lean_ctor_get(v_m_60_, 0);
v_buckets_64_ = lean_ctor_get(v_m_60_, 1);
v___x_65_ = lean_array_get_size(v_buckets_64_);
v___x_66_ = lean_uint64_of_nat(v_a_61_);
v___x_67_ = 32ULL;
v___x_68_ = lean_uint64_shift_right(v___x_66_, v___x_67_);
v_fold_69_ = lean_uint64_xor(v___x_66_, v___x_68_);
v___x_70_ = 16ULL;
v___x_71_ = lean_uint64_shift_right(v_fold_69_, v___x_70_);
v___x_72_ = lean_uint64_xor(v_fold_69_, v___x_71_);
v___x_73_ = lean_uint64_to_usize(v___x_72_);
v___x_74_ = lean_usize_of_nat(v___x_65_);
v___x_75_ = ((size_t)1ULL);
v___x_76_ = lean_usize_sub(v___x_74_, v___x_75_);
v___x_77_ = lean_usize_land(v___x_73_, v___x_76_);
v_bkt_78_ = lean_array_uget_borrowed(v_buckets_64_, v___x_77_);
v___x_79_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(v_a_61_, v_bkt_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_100_; 
lean_inc_ref(v_buckets_64_);
lean_inc(v_size_63_);
v_isSharedCheck_100_ = !lean_is_exclusive(v_m_60_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; 
v_unused_101_ = lean_ctor_get(v_m_60_, 1);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_m_60_, 0);
lean_dec(v_unused_102_);
v___x_81_ = v_m_60_;
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
else
{
lean_dec(v_m_60_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v_size_x27_84_; lean_object* v___x_85_; lean_object* v_buckets_x27_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v_size_x27_84_ = lean_nat_add(v_size_63_, v___x_83_);
lean_dec(v_size_63_);
lean_inc(v_bkt_78_);
v___x_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_85_, 0, v_a_61_);
lean_ctor_set(v___x_85_, 1, v_b_62_);
lean_ctor_set(v___x_85_, 2, v_bkt_78_);
v_buckets_x27_86_ = lean_array_uset(v_buckets_64_, v___x_77_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(4u);
v___x_88_ = lean_nat_mul(v_size_x27_84_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_nat_div(v___x_88_, v___x_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_array_get_size(v_buckets_x27_86_);
v___x_92_ = lean_nat_dec_le(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
if (v___x_92_ == 0)
{
lean_object* v_val_93_; lean_object* v___x_95_; 
v_val_93_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2___redArg(v_buckets_x27_86_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_val_93_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_95_ = v___x_81_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_val_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
lean_object* v___x_98_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_buckets_x27_86_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_98_ = v___x_81_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_buckets_x27_86_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_dec(v_b_62_);
lean_dec(v_a_61_);
return v_m_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(lean_object* v_as_103_, size_t v_sz_104_, size_t v_i_105_, lean_object* v_b_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = lean_usize_dec_lt(v_i_105_, v_sz_104_);
if (v___x_107_ == 0)
{
return v_b_106_;
}
else
{
lean_object* v_a_108_; lean_object* v___x_109_; lean_object* v_r_110_; size_t v___x_111_; size_t v___x_112_; 
v_a_108_ = lean_array_uget_borrowed(v_as_103_, v_i_105_);
v___x_109_ = lean_box(0);
lean_inc(v_a_108_);
v_r_110_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1___redArg(v_b_106_, v_a_108_, v___x_109_);
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_add(v_i_105_, v___x_111_);
v_i_105_ = v___x_112_;
v_b_106_ = v_r_110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2___boxed(lean_object* v_as_114_, lean_object* v_sz_115_, lean_object* v_i_116_, lean_object* v_b_117_){
_start:
{
size_t v_sz_boxed_118_; size_t v_i_boxed_119_; lean_object* v_res_120_; 
v_sz_boxed_118_ = lean_unbox_usize(v_sz_115_);
lean_dec(v_sz_115_);
v_i_boxed_119_ = lean_unbox_usize(v_i_116_);
lean_dec(v_i_116_);
v_res_120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(v_as_114_, v_sz_boxed_118_, v_i_boxed_119_, v_b_117_);
lean_dec_ref(v_as_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1(lean_object* v_m_121_, lean_object* v_l_122_){
_start:
{
size_t v_sz_123_; size_t v___x_124_; lean_object* v___x_125_; 
v_sz_123_ = lean_array_size(v_l_122_);
v___x_124_ = ((size_t)0ULL);
v___x_125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(v_l_122_, v_sz_123_, v___x_124_, v_m_121_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1___boxed(lean_object* v_m_126_, lean_object* v_l_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1(v_m_126_, v_l_127_);
lean_dec_ref(v_l_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(size_t v_sz_129_, size_t v_i_130_, lean_object* v_bs_131_){
_start:
{
uint8_t v___x_132_; 
v___x_132_ = lean_usize_dec_lt(v_i_130_, v_sz_129_);
if (v___x_132_ == 0)
{
return v_bs_131_;
}
else
{
lean_object* v_v_133_; lean_object* v_fst_134_; lean_object* v___x_135_; lean_object* v_bs_x27_136_; size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; 
v_v_133_ = lean_array_uget_borrowed(v_bs_131_, v_i_130_);
v_fst_134_ = lean_ctor_get(v_v_133_, 0);
lean_inc(v_fst_134_);
v___x_135_ = lean_unsigned_to_nat(0u);
v_bs_x27_136_ = lean_array_uset(v_bs_131_, v_i_130_, v___x_135_);
v___x_137_ = ((size_t)1ULL);
v___x_138_ = lean_usize_add(v_i_130_, v___x_137_);
v___x_139_ = lean_array_uset(v_bs_x27_136_, v_i_130_, v_fst_134_);
v_i_130_ = v___x_138_;
v_bs_131_ = v___x_139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0___boxed(lean_object* v_sz_141_, lean_object* v_i_142_, lean_object* v_bs_143_){
_start:
{
size_t v_sz_boxed_144_; size_t v_i_boxed_145_; lean_object* v_res_146_; 
v_sz_boxed_144_ = lean_unbox_usize(v_sz_141_);
lean_dec(v_sz_141_);
v_i_boxed_145_ = lean_unbox_usize(v_i_142_);
lean_dec(v_i_142_);
v_res_146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(v_sz_boxed_144_, v_i_boxed_145_, v_bs_143_);
return v_res_146_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg(lean_object* v_m_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_buckets_149_; lean_object* v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v_fold_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; size_t v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_buckets_149_ = lean_ctor_get(v_m_147_, 1);
v___x_150_ = lean_array_get_size(v_buckets_149_);
v___x_151_ = lean_uint64_of_nat(v_a_148_);
v___x_152_ = 32ULL;
v___x_153_ = lean_uint64_shift_right(v___x_151_, v___x_152_);
v_fold_154_ = lean_uint64_xor(v___x_151_, v___x_153_);
v___x_155_ = 16ULL;
v___x_156_ = lean_uint64_shift_right(v_fold_154_, v___x_155_);
v___x_157_ = lean_uint64_xor(v_fold_154_, v___x_156_);
v___x_158_ = lean_uint64_to_usize(v___x_157_);
v___x_159_ = lean_usize_of_nat(v___x_150_);
v___x_160_ = ((size_t)1ULL);
v___x_161_ = lean_usize_sub(v___x_159_, v___x_160_);
v___x_162_ = lean_usize_land(v___x_158_, v___x_161_);
v___x_163_ = lean_array_uget_borrowed(v_buckets_149_, v___x_162_);
v___x_164_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(v_a_148_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg___boxed(lean_object* v_m_165_, lean_object* v_a_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg(v_m_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec_ref(v_m_165_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3(lean_object* v_negPivot_169_, lean_object* v___x_170_, lean_object* v_s_171_, lean_object* v_i_172_){
_start:
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_array_get_size(v_s_171_);
v___x_174_ = lean_nat_dec_lt(v_i_172_, v___x_173_);
if (v___x_174_ == 0)
{
uint8_t v___x_175_; 
lean_dec(v_i_172_);
lean_dec_ref(v_negPivot_169_);
v___x_175_ = 1;
return v___x_175_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = lean_array_fget_borrowed(v_s_171_, v_i_172_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_add(v_i_172_, v___x_177_);
lean_dec(v_i_172_);
v_i_172_ = v___x_178_;
goto _start;
}
else
{
lean_object* v_val_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_187_; 
v_val_180_ = lean_ctor_get(v___x_176_, 0);
v___x_181_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_add(v_i_172_, v___x_182_);
lean_dec(v_i_172_);
lean_inc_ref(v_negPivot_169_);
v___x_187_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v___x_181_, v_negPivot_169_, v_val_180_);
if (v___x_187_ == 0)
{
if (v___x_174_ == 0)
{
goto v___jp_184_;
}
else
{
v_i_172_ = v___x_183_;
goto _start;
}
}
else
{
goto v___jp_184_;
}
v___jp_184_:
{
uint8_t v___x_185_; 
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg(v___x_170_, v___x_183_);
if (v___x_185_ == 0)
{
lean_dec(v___x_183_);
lean_dec_ref(v_negPivot_169_);
return v___x_185_;
}
else
{
v_i_172_ = v___x_183_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___boxed(lean_object* v_negPivot_189_, lean_object* v___x_190_, lean_object* v_s_191_, lean_object* v_i_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3(v_negPivot_189_, v___x_190_, v_s_191_, v_i_192_);
lean_dec_ref(v_s_191_);
lean_dec_ref(v___x_190_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_box(0);
v___x_196_ = lean_unsigned_to_nat(16u);
v___x_197_ = lean_mk_array(v___x_196_, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
return v___x_200_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(lean_object* v_s_201_, lean_object* v_ratHints_202_, lean_object* v_negPivot_203_){
_start:
{
size_t v_sz_204_; size_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_sz_204_ = lean_array_size(v_ratHints_202_);
v___x_205_ = ((size_t)0ULL);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(v_sz_204_, v___x_205_, v_ratHints_202_);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1, &l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1);
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1(v___x_208_, v___x_206_);
lean_dec_ref(v___x_206_);
v___x_210_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3(v_negPivot_203_, v___x_209_, v_s_201_, v___x_207_);
lean_dec_ref(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___boxed(lean_object* v_s_211_, lean_object* v_ratHints_212_, lean_object* v_negPivot_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(v_s_211_, v_ratHints_212_, v_negPivot_213_);
lean_dec_ref(v_s_211_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2(lean_object* v_00_u03b2_216_, lean_object* v_m_217_, lean_object* v_a_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg(v_m_217_, v_a_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___boxed(lean_object* v_00_u03b2_220_, lean_object* v_m_221_, lean_object* v_a_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2(v_00_u03b2_220_, v_m_221_, v_a_222_);
lean_dec(v_a_222_);
lean_dec_ref(v_m_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1(lean_object* v_00_u03b2_225_, lean_object* v_m_226_, lean_object* v_a_227_, lean_object* v_b_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1___redArg(v_m_226_, v_a_227_, v_b_228_);
return v___x_229_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4(lean_object* v_00_u03b2_230_, lean_object* v_a_231_, lean_object* v_x_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(v_a_231_, v_x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___boxed(lean_object* v_00_u03b2_234_, lean_object* v_a_235_, lean_object* v_x_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4(v_00_u03b2_234_, v_a_235_, v_x_236_);
lean_dec(v_x_236_);
lean_dec(v_a_235_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_239_, lean_object* v_data_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2___redArg(v_data_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_242_, lean_object* v_i_243_, lean_object* v_source_244_, lean_object* v_target_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5___redArg(v_i_243_, v_source_244_, v_target_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_247_, lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_x_248_, v_x_249_);
return v___x_250_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(lean_object* v_s_251_, uint8_t v___x_252_, lean_object* v_assign_253_, lean_object* v___y_254_, lean_object* v_pivot_255_, lean_object* v_clause_256_, lean_object* v_as_257_, size_t v_i_258_, size_t v_stop_259_){
_start:
{
uint8_t v___y_261_; uint8_t v___y_262_; uint8_t v___y_267_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc_ref(v_pivot_255_);
v___x_284_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v___x_283_, v_pivot_255_, v_clause_256_);
if (v___x_284_ == 0)
{
uint8_t v___x_285_; 
v___x_285_ = 1;
v___y_267_ = v___x_285_;
goto v___jp_266_;
}
else
{
uint8_t v___x_286_; 
v___x_286_ = 0;
v___y_267_ = v___x_286_;
goto v___jp_266_;
}
v___jp_260_:
{
if (v___y_262_ == 0)
{
size_t v___x_263_; size_t v___x_264_; 
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_add(v_i_258_, v___x_263_);
v_i_258_ = v___x_264_;
goto _start;
}
else
{
lean_dec_ref(v_pivot_255_);
lean_dec_ref(v_assign_253_);
return v___y_261_;
}
}
v___jp_266_:
{
uint8_t v___x_268_; 
v___x_268_ = lean_usize_dec_eq(v_i_258_, v_stop_259_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v_fst_270_; lean_object* v_snd_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_269_ = lean_array_uget_borrowed(v_as_257_, v_i_258_);
v_fst_270_ = lean_ctor_get(v___x_269_, 0);
v_snd_271_ = lean_ctor_get(v___x_269_, 1);
v___x_272_ = 1;
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_sub(v_fst_270_, v___x_273_);
v___x_275_ = lean_array_get_size(v_s_251_);
v___x_276_ = lean_nat_dec_lt(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_dec(v___x_274_);
v___y_261_ = v___x_272_;
v___y_262_ = v___x_252_;
goto v___jp_260_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = lean_array_fget_borrowed(v_s_251_, v___x_274_);
lean_dec(v___x_274_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_dec_ref(v_pivot_255_);
lean_dec_ref(v_assign_253_);
return v___x_272_;
}
else
{
lean_object* v_val_278_; lean_object* v___x_279_; 
v_val_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc_ref(v_assign_253_);
v___x_279_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(v_assign_253_, v_val_278_, v___y_254_);
if (lean_obj_tag(v___x_279_) == 0)
{
v___y_261_ = v___x_272_;
v___y_262_ = v___y_267_;
goto v___jp_260_;
}
else
{
lean_object* v_val_280_; uint8_t v___x_281_; 
v_val_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_val_280_);
lean_dec_ref_known(v___x_279_, 1);
v___x_281_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_251_, v_val_280_, v_snd_271_);
if (v___x_281_ == 0)
{
lean_dec_ref(v_pivot_255_);
lean_dec_ref(v_assign_253_);
return v___x_272_;
}
else
{
v___y_261_ = v___x_272_;
v___y_262_ = v___y_267_;
goto v___jp_260_;
}
}
}
}
}
else
{
uint8_t v___x_282_; 
lean_dec_ref(v_pivot_255_);
lean_dec_ref(v_assign_253_);
v___x_282_ = 0;
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0___boxed(lean_object* v_s_287_, lean_object* v___x_288_, lean_object* v_assign_289_, lean_object* v___y_290_, lean_object* v_pivot_291_, lean_object* v_clause_292_, lean_object* v_as_293_, lean_object* v_i_294_, lean_object* v_stop_295_){
_start:
{
uint8_t v___x_1008__boxed_296_; size_t v_i_boxed_297_; size_t v_stop_boxed_298_; uint8_t v_res_299_; lean_object* v_r_300_; 
v___x_1008__boxed_296_ = lean_unbox(v___x_288_);
v_i_boxed_297_ = lean_unbox_usize(v_i_294_);
lean_dec(v_i_294_);
v_stop_boxed_298_ = lean_unbox_usize(v_stop_295_);
lean_dec(v_stop_295_);
v_res_299_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(v_s_287_, v___x_1008__boxed_296_, v_assign_289_, v___y_290_, v_pivot_291_, v_clause_292_, v_as_293_, v_i_boxed_297_, v_stop_boxed_298_);
lean_dec_ref(v_as_293_);
lean_dec_ref(v_clause_292_);
lean_dec_ref(v___y_290_);
lean_dec_ref(v_s_287_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat(lean_object* v_s_301_, lean_object* v_clause_302_, lean_object* v_pivot_303_, lean_object* v_rupHints_304_, lean_object* v_ratHints_305_){
_start:
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc_ref(v_pivot_303_);
v___x_307_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v___x_306_, v_pivot_303_, v_clause_302_);
if (v___x_307_ == 0)
{
lean_dec_ref(v_ratHints_305_);
lean_dec_ref(v_pivot_303_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(v_clause_302_);
if (lean_obj_tag(v___x_308_) == 1)
{
lean_object* v_val_309_; uint8_t v___x_310_; lean_object* v___x_311_; 
v_val_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_val_309_);
lean_dec_ref_known(v___x_308_, 1);
v___x_310_ = 0;
v___x_311_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(v_s_301_, v_val_309_, v_rupHints_304_);
switch(lean_obj_tag(v___x_311_))
{
case 0:
{
lean_dec_ref(v_ratHints_305_);
lean_dec_ref(v_pivot_303_);
return v___x_307_;
}
case 1:
{
lean_object* v_assign_312_; lean_object* v___y_314_; lean_object* v_snd_322_; uint8_t v___x_323_; 
v_assign_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_assign_312_);
lean_dec_ref_known(v___x_311_, 1);
v_snd_322_ = lean_ctor_get(v_pivot_303_, 1);
v___x_323_ = lean_unbox(v_snd_322_);
if (v___x_323_ == 0)
{
lean_object* v_fst_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_fst_324_ = lean_ctor_get(v_pivot_303_, 0);
v___x_325_ = lean_box(v___x_307_);
lean_inc(v_fst_324_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v_fst_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___y_314_ = v___x_326_;
goto v___jp_313_;
}
else
{
lean_object* v_fst_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_fst_327_ = lean_ctor_get(v_pivot_303_, 0);
v___x_328_ = lean_box(v___x_310_);
lean_inc(v_fst_327_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_fst_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___y_314_ = v___x_329_;
goto v___jp_313_;
}
v___jp_313_:
{
uint8_t v___x_315_; 
lean_inc_ref(v___y_314_);
lean_inc_ref(v_ratHints_305_);
v___x_315_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(v_s_301_, v_ratHints_305_, v___y_314_);
if (v___x_315_ == 0)
{
lean_dec_ref(v___y_314_);
lean_dec_ref(v_assign_312_);
lean_dec_ref(v_ratHints_305_);
lean_dec_ref(v_pivot_303_);
return v___x_310_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_array_get_size(v_ratHints_305_);
v___x_318_ = lean_nat_dec_lt(v___x_316_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec_ref(v___y_314_);
lean_dec_ref(v_assign_312_);
lean_dec_ref(v_ratHints_305_);
lean_dec_ref(v_pivot_303_);
return v___x_315_;
}
else
{
if (v___x_318_ == 0)
{
lean_dec_ref(v___y_314_);
lean_dec_ref(v_assign_312_);
lean_dec_ref(v_ratHints_305_);
lean_dec_ref(v_pivot_303_);
return v___x_315_;
}
else
{
size_t v___x_319_; size_t v___x_320_; uint8_t v___x_321_; 
v___x_319_ = ((size_t)0ULL);
v___x_320_ = lean_usize_of_nat(v___x_317_);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(v_s_301_, v___x_315_, v_assign_312_, v___y_314_, v_pivot_303_, v_clause_302_, v_ratHints_305_, v___x_319_, v___x_320_);
lean_dec_ref(v_ratHints_305_);
lean_dec_ref(v___y_314_);
if (v___x_321_ == 0)
{
return v___x_318_;
}
else
{
return v___x_310_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_ratHints_305_);
lean_dec_ref(v_pivot_303_);
return v___x_310_;
}
}
}
else
{
lean_dec(v___x_308_);
lean_dec_ref(v_ratHints_305_);
lean_dec_ref(v_pivot_303_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat___boxed(lean_object* v_s_330_, lean_object* v_clause_331_, lean_object* v_pivot_332_, lean_object* v_rupHints_333_, lean_object* v_ratHints_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat(v_s_330_, v_clause_331_, v_pivot_332_, v_rupHints_333_, v_ratHints_334_);
lean_dec_ref(v_rupHints_333_);
lean_dec_ref(v_clause_331_);
lean_dec_ref(v_s_330_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__9_splitter___redArg(lean_object* v_x_337_, lean_object* v_h__1_338_, lean_object* v_h__2_339_){
_start:
{
if (lean_obj_tag(v_x_337_) == 1)
{
lean_object* v_val_340_; lean_object* v___x_341_; 
lean_dec(v_h__2_339_);
v_val_340_ = lean_ctor_get(v_x_337_, 0);
lean_inc(v_val_340_);
lean_dec_ref_known(v_x_337_, 1);
v___x_341_ = lean_apply_1(v_h__1_338_, v_val_340_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; 
lean_dec(v_h__1_338_);
v___x_342_ = lean_apply_2(v_h__2_339_, v_x_337_, lean_box(0));
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__9_splitter(lean_object* v_motive_343_, lean_object* v_x_344_, lean_object* v_h__1_345_, lean_object* v_h__2_346_){
_start:
{
if (lean_obj_tag(v_x_344_) == 1)
{
lean_object* v_val_347_; lean_object* v___x_348_; 
lean_dec(v_h__2_346_);
v_val_347_ = lean_ctor_get(v_x_344_, 0);
lean_inc(v_val_347_);
lean_dec_ref_known(v_x_344_, 1);
v___x_348_ = lean_apply_1(v_h__1_345_, v_val_347_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; 
lean_dec(v_h__1_345_);
v___x_349_ = lean_apply_2(v_h__2_346_, v_x_344_, lean_box(0));
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__7_splitter___redArg(lean_object* v_x_350_, lean_object* v_h__1_351_, lean_object* v_h__2_352_, lean_object* v_h__3_353_){
_start:
{
switch(lean_obj_tag(v_x_350_))
{
case 0:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_h__3_353_);
lean_dec(v_h__2_352_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_apply_1(v_h__1_351_, v___x_354_);
return v___x_355_;
}
case 1:
{
lean_object* v_assign_356_; lean_object* v___x_357_; 
lean_dec(v_h__2_352_);
lean_dec(v_h__1_351_);
v_assign_356_ = lean_ctor_get(v_x_350_, 0);
lean_inc_ref(v_assign_356_);
lean_dec_ref_known(v_x_350_, 1);
v___x_357_ = lean_apply_1(v_h__3_353_, v_assign_356_);
return v___x_357_;
}
default: 
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_h__3_353_);
lean_dec(v_h__1_351_);
v___x_358_ = lean_box(0);
v___x_359_ = lean_apply_1(v_h__2_352_, v___x_358_);
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__7_splitter(lean_object* v_motive_360_, lean_object* v_x_361_, lean_object* v_h__1_362_, lean_object* v_h__2_363_, lean_object* v_h__3_364_){
_start:
{
switch(lean_obj_tag(v_x_361_))
{
case 0:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec(v_h__3_364_);
lean_dec(v_h__2_363_);
v___x_365_ = lean_box(0);
v___x_366_ = lean_apply_1(v_h__1_362_, v___x_365_);
return v___x_366_;
}
case 1:
{
lean_object* v_assign_367_; lean_object* v___x_368_; 
lean_dec(v_h__2_363_);
lean_dec(v_h__1_362_);
v_assign_367_ = lean_ctor_get(v_x_361_, 0);
lean_inc_ref(v_assign_367_);
lean_dec_ref_known(v_x_361_, 1);
v___x_368_ = lean_apply_1(v_h__3_364_, v_assign_367_);
return v___x_368_;
}
default: 
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_dec(v_h__3_364_);
lean_dec(v_h__1_362_);
v___x_369_ = lean_box(0);
v___x_370_ = lean_apply_1(v_h__2_363_, v___x_369_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__3_splitter___redArg(lean_object* v_x_371_, lean_object* v_h__1_372_, lean_object* v_h__2_373_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec(v_h__1_372_);
v___x_374_ = lean_box(0);
v___x_375_ = lean_apply_1(v_h__2_373_, v___x_374_);
return v___x_375_;
}
else
{
lean_object* v_val_376_; lean_object* v___x_377_; 
lean_dec(v_h__2_373_);
v_val_376_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v_x_371_, 1);
v___x_377_ = lean_apply_1(v_h__1_372_, v_val_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__3_splitter(lean_object* v_motive_378_, lean_object* v_x_379_, lean_object* v_h__1_380_, lean_object* v_h__2_381_){
_start:
{
if (lean_obj_tag(v_x_379_) == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec(v_h__1_380_);
v___x_382_ = lean_box(0);
v___x_383_ = lean_apply_1(v_h__2_381_, v___x_382_);
return v___x_383_;
}
else
{
lean_object* v_val_384_; lean_object* v___x_385_; 
lean_dec(v_h__2_381_);
v_val_384_ = lean_ctor_get(v_x_379_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v_x_379_, 1);
v___x_385_ = lean_apply_1(v_h__1_380_, v_val_384_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__1_splitter___redArg(lean_object* v_x_386_, lean_object* v_h__1_387_, lean_object* v_h__2_388_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_h__1_387_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_apply_1(v_h__2_388_, v___x_389_);
return v___x_390_;
}
else
{
lean_object* v_val_391_; lean_object* v___x_392_; 
lean_dec(v_h__2_388_);
v_val_391_ = lean_ctor_get(v_x_386_, 0);
lean_inc(v_val_391_);
lean_dec_ref_known(v_x_386_, 1);
v___x_392_ = lean_apply_1(v_h__1_387_, v_val_391_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__1_splitter(lean_object* v_motive_393_, lean_object* v_x_394_, lean_object* v_h__1_395_, lean_object* v_h__2_396_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v_h__1_395_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_apply_1(v_h__2_396_, v___x_397_);
return v___x_398_;
}
else
{
lean_object* v_val_399_; lean_object* v___x_400_; 
lean_dec(v_h__2_396_);
v_val_399_ = lean_ctor_get(v_x_394_, 0);
lean_inc(v_val_399_);
lean_dec_ref_known(v_x_394_, 1);
v___x_400_ = lean_apply_1(v_h__1_395_, v_val_399_);
return v___x_400_;
}
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Add(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Add(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Rat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Rat(builtin);
}
#ifdef __cplusplus
}
#endif
