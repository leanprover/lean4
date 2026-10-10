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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_nbuckets_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_42_ = lean_array_get_size(v_data_41_);
v___x_43_ = lean_unsigned_to_nat(2u);
v_nbuckets_44_ = lean_nat_mul(v___x_42_, v___x_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_box(0);
v___x_47_ = lean_mk_array(v_nbuckets_44_, v___x_46_);
v___x_48_ = lean_array_propagate_mark(v_data_41_, v___x_47_);
v___x_49_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5___redArg(v___x_45_, v_data_41_, v___x_48_);
return v___x_49_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(lean_object* v_a_50_, lean_object* v_x_51_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
else
{
lean_object* v_key_53_; lean_object* v_tail_54_; uint8_t v___x_55_; 
v_key_53_ = lean_ctor_get(v_x_51_, 0);
v_tail_54_ = lean_ctor_get(v_x_51_, 2);
v___x_55_ = lean_nat_dec_eq(v_key_53_, v_a_50_);
if (v___x_55_ == 0)
{
v_x_51_ = v_tail_54_;
goto _start;
}
else
{
return v___x_55_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_50_ = stack[0].m_obj;
lean_object* v_x_51_ = stack[1].m_obj;
uint8_t v_res_57_;
v_res_57_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(v_a_50_, v_x_51_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg___boxed(lean_object* v_a_58_, lean_object* v_x_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(v_a_58_, v_x_59_);
lean_dec(v_x_59_);
lean_dec(v_a_58_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1___redArg(lean_object* v_m_62_, lean_object* v_a_63_, lean_object* v_b_64_){
_start:
{
lean_object* v_size_65_; lean_object* v_buckets_66_; lean_object* v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; uint64_t v_fold_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; lean_object* v_bkt_80_; uint8_t v___x_81_; 
v_size_65_ = lean_ctor_get(v_m_62_, 0);
v_buckets_66_ = lean_ctor_get(v_m_62_, 1);
v___x_67_ = lean_array_get_size(v_buckets_66_);
v___x_68_ = lean_uint64_of_nat(v_a_63_);
v___x_69_ = 32ULL;
v___x_70_ = lean_uint64_shift_right(v___x_68_, v___x_69_);
v_fold_71_ = lean_uint64_xor(v___x_68_, v___x_70_);
v___x_72_ = 16ULL;
v___x_73_ = lean_uint64_shift_right(v_fold_71_, v___x_72_);
v___x_74_ = lean_uint64_xor(v_fold_71_, v___x_73_);
v___x_75_ = lean_uint64_to_usize(v___x_74_);
v___x_76_ = lean_usize_of_nat(v___x_67_);
v___x_77_ = ((size_t)1ULL);
v___x_78_ = lean_usize_sub(v___x_76_, v___x_77_);
v___x_79_ = lean_usize_land(v___x_75_, v___x_78_);
v_bkt_80_ = lean_array_uget_borrowed(v_buckets_66_, v___x_79_);
v___x_81_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(v_a_63_, v_bkt_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_102_; 
lean_inc_ref(v_buckets_66_);
lean_inc(v_size_65_);
v_isSharedCheck_102_ = !lean_is_exclusive(v_m_62_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; lean_object* v_unused_104_; 
v_unused_103_ = lean_ctor_get(v_m_62_, 1);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_m_62_, 0);
lean_dec(v_unused_104_);
v___x_83_ = v_m_62_;
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_m_62_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v_size_x27_86_; lean_object* v___x_87_; lean_object* v_buckets_x27_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v_size_x27_86_ = lean_nat_add(v_size_65_, v___x_85_);
lean_dec(v_size_65_);
lean_inc(v_bkt_80_);
v___x_87_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_87_, 0, v_a_63_);
lean_ctor_set(v___x_87_, 1, v_b_64_);
lean_ctor_set(v___x_87_, 2, v_bkt_80_);
v_buckets_x27_88_ = lean_array_uset(v_buckets_66_, v___x_79_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(4u);
v___x_90_ = lean_nat_mul(v_size_x27_86_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(3u);
v___x_92_ = lean_nat_div(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_array_get_size(v_buckets_x27_88_);
v___x_94_ = lean_nat_dec_le(v___x_92_, v___x_93_);
lean_dec(v___x_92_);
if (v___x_94_ == 0)
{
lean_object* v_val_95_; lean_object* v___x_97_; 
v_val_95_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2___redArg(v_buckets_x27_88_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_val_95_);
lean_ctor_set(v___x_83_, 0, v_size_x27_86_);
v___x_97_ = v___x_83_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_size_x27_86_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_val_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
else
{
lean_object* v___x_100_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_buckets_x27_88_);
lean_ctor_set(v___x_83_, 0, v_size_x27_86_);
v___x_100_ = v___x_83_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_size_x27_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_buckets_x27_88_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
else
{
lean_dec(v_b_64_);
lean_dec(v_a_63_);
return v_m_62_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(lean_object* v_as_105_, size_t v_sz_106_, size_t v_i_107_, lean_object* v_b_108_){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = lean_usize_dec_lt(v_i_107_, v_sz_106_);
if (v___x_109_ == 0)
{
return v_b_108_;
}
else
{
lean_object* v_a_110_; lean_object* v___x_111_; lean_object* v_r_112_; size_t v___x_113_; size_t v___x_114_; 
v_a_110_ = lean_array_uget_borrowed(v_as_105_, v_i_107_);
v___x_111_ = lean_box(0);
lean_inc(v_a_110_);
v_r_112_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1___redArg(v_b_108_, v_a_110_, v___x_111_);
v___x_113_ = ((size_t)1ULL);
v___x_114_ = lean_usize_add(v_i_107_, v___x_113_);
v_i_107_ = v___x_114_;
v_b_108_ = v_r_112_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_105_ = stack[0].m_obj;
size_t v_sz_106_ = stack[1].m_num;
size_t v_i_107_ = stack[2].m_num;
lean_object* v_b_108_ = stack[3].m_obj;
lean_object* v_res_116_;
v_res_116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(v_as_105_, v_sz_106_, v_i_107_, v_b_108_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2___boxed(lean_object* v_as_117_, lean_object* v_sz_118_, lean_object* v_i_119_, lean_object* v_b_120_){
_start:
{
size_t v_sz_boxed_121_; size_t v_i_boxed_122_; lean_object* v_res_123_; 
v_sz_boxed_121_ = lean_unbox_usize(v_sz_118_);
lean_dec(v_sz_118_);
v_i_boxed_122_ = lean_unbox_usize(v_i_119_);
lean_dec(v_i_119_);
v_res_123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(v_as_117_, v_sz_boxed_121_, v_i_boxed_122_, v_b_120_);
lean_dec_ref(v_as_117_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1(lean_object* v_m_124_, lean_object* v_l_125_){
_start:
{
size_t v_sz_126_; size_t v___x_127_; lean_object* v___x_128_; 
v_sz_126_ = lean_array_size(v_l_125_);
v___x_127_ = ((size_t)0ULL);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(v_l_125_, v_sz_126_, v___x_127_, v_m_124_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1___boxed(lean_object* v_m_129_, lean_object* v_l_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1(v_m_129_, v_l_130_);
lean_dec_ref(v_l_130_);
return v_res_131_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(size_t v_sz_132_, size_t v_i_133_, lean_object* v_bs_134_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = lean_usize_dec_lt(v_i_133_, v_sz_132_);
if (v___x_135_ == 0)
{
return v_bs_134_;
}
else
{
lean_object* v_v_136_; lean_object* v_fst_137_; lean_object* v___x_138_; lean_object* v_bs_x27_139_; size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; 
v_v_136_ = lean_array_uget_borrowed(v_bs_134_, v_i_133_);
v_fst_137_ = lean_ctor_get(v_v_136_, 0);
lean_inc(v_fst_137_);
v___x_138_ = lean_unsigned_to_nat(0u);
v_bs_x27_139_ = lean_array_uset(v_bs_134_, v_i_133_, v___x_138_);
v___x_140_ = ((size_t)1ULL);
v___x_141_ = lean_usize_add(v_i_133_, v___x_140_);
v___x_142_ = lean_array_uset(v_bs_x27_139_, v_i_133_, v_fst_137_);
v_i_133_ = v___x_141_;
v_bs_134_ = v___x_142_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_132_ = stack[0].m_num;
size_t v_i_133_ = stack[1].m_num;
lean_object* v_bs_134_ = stack[2].m_obj;
lean_object* v_res_144_;
v_res_144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(v_sz_132_, v_i_133_, v_bs_134_);
stack->m_obj
 = v_res_144_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0___boxed(lean_object* v_sz_145_, lean_object* v_i_146_, lean_object* v_bs_147_){
_start:
{
size_t v_sz_boxed_148_; size_t v_i_boxed_149_; lean_object* v_res_150_; 
v_sz_boxed_148_ = lean_unbox_usize(v_sz_145_);
lean_dec(v_sz_145_);
v_i_boxed_149_ = lean_unbox_usize(v_i_146_);
lean_dec(v_i_146_);
v_res_150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(v_sz_boxed_148_, v_i_boxed_149_, v_bs_147_);
return v_res_150_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg(lean_object* v_m_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_buckets_153_; lean_object* v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v_fold_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_buckets_153_ = lean_ctor_get(v_m_151_, 1);
v___x_154_ = lean_array_get_size(v_buckets_153_);
v___x_155_ = lean_uint64_of_nat(v_a_152_);
v___x_156_ = 32ULL;
v___x_157_ = lean_uint64_shift_right(v___x_155_, v___x_156_);
v_fold_158_ = lean_uint64_xor(v___x_155_, v___x_157_);
v___x_159_ = 16ULL;
v___x_160_ = lean_uint64_shift_right(v_fold_158_, v___x_159_);
v___x_161_ = lean_uint64_xor(v_fold_158_, v___x_160_);
v___x_162_ = lean_uint64_to_usize(v___x_161_);
v___x_163_ = lean_usize_of_nat(v___x_154_);
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_sub(v___x_163_, v___x_164_);
v___x_166_ = lean_usize_land(v___x_162_, v___x_165_);
v___x_167_ = lean_array_uget_borrowed(v_buckets_153_, v___x_166_);
v___x_168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(v_a_152_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_151_ = stack[0].m_obj;
lean_object* v_a_152_ = stack[1].m_obj;
uint8_t v_res_169_;
v_res_169_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg(v_m_151_, v_a_152_);
stack->m_num = v_res_169_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg___boxed(lean_object* v_m_170_, lean_object* v_a_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg(v_m_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_m_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3(lean_object* v_negPivot_174_, lean_object* v___x_175_, lean_object* v_s_176_, lean_object* v_i_177_){
_start:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_array_get_size(v_s_176_);
v___x_179_ = lean_nat_dec_lt(v_i_177_, v___x_178_);
if (v___x_179_ == 0)
{
uint8_t v___x_180_; 
lean_dec(v_i_177_);
lean_dec_ref(v_negPivot_174_);
v___x_180_ = 1;
return v___x_180_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = lean_array_fget_borrowed(v_s_176_, v_i_177_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_add(v_i_177_, v___x_182_);
lean_dec(v_i_177_);
v_i_177_ = v___x_183_;
goto _start;
}
else
{
lean_object* v_val_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_192_; 
v_val_185_ = lean_ctor_get(v___x_181_, 0);
v___x_186_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v_i_177_, v___x_187_);
lean_dec(v_i_177_);
lean_inc_ref(v_negPivot_174_);
v___x_192_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v___x_186_, v_negPivot_174_, v_val_185_);
if (v___x_192_ == 0)
{
if (v___x_179_ == 0)
{
goto v___jp_189_;
}
else
{
v_i_177_ = v___x_188_;
goto _start;
}
}
else
{
goto v___jp_189_;
}
v___jp_189_:
{
uint8_t v___x_190_; 
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg(v___x_175_, v___x_188_);
if (v___x_190_ == 0)
{
lean_dec(v___x_188_);
lean_dec_ref(v_negPivot_174_);
return v___x_190_;
}
else
{
v_i_177_ = v___x_188_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_negPivot_174_ = stack[0].m_obj;
lean_object* v___x_175_ = stack[1].m_obj;
lean_object* v_s_176_ = stack[2].m_obj;
lean_object* v_i_177_ = stack[3].m_obj;
uint8_t v_res_194_;
v_res_194_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3(v_negPivot_174_, v___x_175_, v_s_176_, v_i_177_);
stack->m_num = v_res_194_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___boxed(lean_object* v_negPivot_195_, lean_object* v___x_196_, lean_object* v_s_197_, lean_object* v_i_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3(v_negPivot_195_, v___x_196_, v_s_197_, v_i_198_);
lean_dec_ref(v_s_197_);
lean_dec_ref(v___x_196_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_box(0);
v___x_202_ = lean_unsigned_to_nat(16u);
v___x_203_ = lean_mk_array(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
return v___x_206_;
}
}
uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(lean_object* v_s_207_, lean_object* v_ratHints_208_, lean_object* v_negPivot_209_){
_start:
{
size_t v_sz_210_; size_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_sz_210_ = lean_array_size(v_ratHints_208_);
v___x_211_ = ((size_t)0ULL);
v___x_212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(v_sz_210_, v___x_211_, v_ratHints_208_);
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1, &l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1);
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1(v___x_214_, v___x_212_);
lean_dec_ref(v___x_212_);
v___x_216_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3(v_negPivot_209_, v___x_215_, v_s_207_, v___x_213_);
lean_dec_ref(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_207_ = stack[0].m_obj;
lean_object* v_ratHints_208_ = stack[1].m_obj;
lean_object* v_negPivot_209_ = stack[2].m_obj;
uint8_t v_res_217_;
v_res_217_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(v_s_207_, v_ratHints_208_, v_negPivot_209_);
stack->m_num = v_res_217_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___boxed(lean_object* v_s_218_, lean_object* v_ratHints_219_, lean_object* v_negPivot_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(v_s_218_, v_ratHints_219_, v_negPivot_220_);
lean_dec_ref(v_s_218_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2(lean_object* v_00_u03b2_223_, lean_object* v_m_224_, lean_object* v_a_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___redArg(v_m_224_, v_a_225_);
return v___x_226_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_224_ = stack[1].m_obj;
lean_object* v_a_225_ = stack[2].m_obj;
uint8_t v_res_227_;
v_res_227_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2(lean_box(0), v_m_224_, v_a_225_);
stack->m_num = v_res_227_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___boxed(lean_object* v_00_u03b2_228_, lean_object* v_m_229_, lean_object* v_a_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2(v_00_u03b2_228_, v_m_229_, v_a_230_);
lean_dec(v_a_230_);
lean_dec_ref(v_m_229_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1(lean_object* v_00_u03b2_233_, lean_object* v_m_234_, lean_object* v_a_235_, lean_object* v_b_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1___redArg(v_m_234_, v_a_235_, v_b_236_);
return v___x_237_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4(lean_object* v_00_u03b2_238_, lean_object* v_a_239_, lean_object* v_x_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___redArg(v_a_239_, v_x_240_);
return v___x_241_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_239_ = stack[1].m_obj;
lean_object* v_x_240_ = stack[2].m_obj;
uint8_t v_res_242_;
v_res_242_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4(lean_box(0), v_a_239_, v_x_240_);
stack->m_num = v_res_242_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4___boxed(lean_object* v_00_u03b2_243_, lean_object* v_a_244_, lean_object* v_x_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2_spec__4(v_00_u03b2_243_, v_a_244_, v_x_245_);
lean_dec(v_x_245_);
lean_dec(v_a_244_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_248_, lean_object* v_data_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2___redArg(v_data_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_251_, lean_object* v_i_252_, lean_object* v_source_253_, lean_object* v_target_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5___redArg(v_i_252_, v_source_253_, v_target_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_x_257_, v_x_258_);
return v___x_259_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(lean_object* v_s_260_, uint8_t v___x_261_, lean_object* v_assign_262_, lean_object* v___y_263_, lean_object* v_pivot_264_, lean_object* v_clause_265_, lean_object* v_as_266_, size_t v_i_267_, size_t v_stop_268_){
_start:
{
uint8_t v___y_270_; uint8_t v___y_271_; uint8_t v___y_276_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc_ref(v_pivot_264_);
v___x_293_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v___x_292_, v_pivot_264_, v_clause_265_);
if (v___x_293_ == 0)
{
uint8_t v___x_294_; 
v___x_294_ = 1;
v___y_276_ = v___x_294_;
goto v___jp_275_;
}
else
{
uint8_t v___x_295_; 
v___x_295_ = 0;
v___y_276_ = v___x_295_;
goto v___jp_275_;
}
v___jp_269_:
{
if (v___y_271_ == 0)
{
size_t v___x_272_; size_t v___x_273_; 
v___x_272_ = ((size_t)1ULL);
v___x_273_ = lean_usize_add(v_i_267_, v___x_272_);
v_i_267_ = v___x_273_;
goto _start;
}
else
{
lean_dec_ref(v_pivot_264_);
lean_dec_ref(v_assign_262_);
return v___y_270_;
}
}
v___jp_275_:
{
uint8_t v___x_277_; 
v___x_277_ = lean_usize_dec_eq(v_i_267_, v_stop_268_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v_fst_279_; lean_object* v_snd_280_; uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_278_ = lean_array_uget_borrowed(v_as_266_, v_i_267_);
v_fst_279_ = lean_ctor_get(v___x_278_, 0);
v_snd_280_ = lean_ctor_get(v___x_278_, 1);
v___x_281_ = 1;
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_sub(v_fst_279_, v___x_282_);
v___x_284_ = lean_array_get_size(v_s_260_);
v___x_285_ = lean_nat_dec_lt(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_dec(v___x_283_);
v___y_270_ = v___x_281_;
v___y_271_ = v___x_261_;
goto v___jp_269_;
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_array_fget_borrowed(v_s_260_, v___x_283_);
lean_dec(v___x_283_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_dec_ref(v_pivot_264_);
lean_dec_ref(v_assign_262_);
return v___x_281_;
}
else
{
lean_object* v_val_287_; lean_object* v___x_288_; 
v_val_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc_ref(v_assign_262_);
v___x_288_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(v_assign_262_, v_val_287_, v___y_263_);
if (lean_obj_tag(v___x_288_) == 0)
{
v___y_270_ = v___x_281_;
v___y_271_ = v___y_276_;
goto v___jp_269_;
}
else
{
lean_object* v_val_289_; uint8_t v___x_290_; 
v_val_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_val_289_);
lean_dec_ref_known(v___x_288_, 1);
v___x_290_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_260_, v_val_289_, v_snd_280_);
if (v___x_290_ == 0)
{
lean_dec_ref(v_pivot_264_);
lean_dec_ref(v_assign_262_);
return v___x_281_;
}
else
{
v___y_270_ = v___x_281_;
v___y_271_ = v___y_276_;
goto v___jp_269_;
}
}
}
}
}
else
{
uint8_t v___x_291_; 
lean_dec_ref(v_pivot_264_);
lean_dec_ref(v_assign_262_);
v___x_291_ = 0;
return v___x_291_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_260_ = stack[0].m_obj;
uint8_t v___x_261_ = stack[1].m_num;
lean_object* v_assign_262_ = stack[2].m_obj;
lean_object* v___y_263_ = stack[3].m_obj;
lean_object* v_pivot_264_ = stack[4].m_obj;
lean_object* v_clause_265_ = stack[5].m_obj;
lean_object* v_as_266_ = stack[6].m_obj;
size_t v_i_267_ = stack[7].m_num;
size_t v_stop_268_ = stack[8].m_num;
uint8_t v_res_296_;
v_res_296_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(v_s_260_, v___x_261_, v_assign_262_, v___y_263_, v_pivot_264_, v_clause_265_, v_as_266_, v_i_267_, v_stop_268_);
stack->m_num = v_res_296_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0___boxed(lean_object* v_s_297_, lean_object* v___x_298_, lean_object* v_assign_299_, lean_object* v___y_300_, lean_object* v_pivot_301_, lean_object* v_clause_302_, lean_object* v_as_303_, lean_object* v_i_304_, lean_object* v_stop_305_){
_start:
{
uint8_t v___x_1010__boxed_306_; size_t v_i_boxed_307_; size_t v_stop_boxed_308_; uint8_t v_res_309_; lean_object* v_r_310_; 
v___x_1010__boxed_306_ = lean_unbox(v___x_298_);
v_i_boxed_307_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_stop_boxed_308_ = lean_unbox_usize(v_stop_305_);
lean_dec(v_stop_305_);
v_res_309_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(v_s_297_, v___x_1010__boxed_306_, v_assign_299_, v___y_300_, v_pivot_301_, v_clause_302_, v_as_303_, v_i_boxed_307_, v_stop_boxed_308_);
lean_dec_ref(v_as_303_);
lean_dec_ref(v_clause_302_);
lean_dec_ref(v___y_300_);
lean_dec_ref(v_s_297_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat(lean_object* v_s_311_, lean_object* v_clause_312_, lean_object* v_pivot_313_, lean_object* v_rupHints_314_, lean_object* v_ratHints_315_){
_start:
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc_ref(v_pivot_313_);
v___x_317_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v___x_316_, v_pivot_313_, v_clause_312_);
if (v___x_317_ == 0)
{
lean_dec_ref(v_ratHints_315_);
lean_dec_ref(v_pivot_313_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(v_clause_312_);
if (lean_obj_tag(v___x_318_) == 1)
{
lean_object* v_val_319_; uint8_t v___x_320_; lean_object* v___x_321_; 
v_val_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_val_319_);
lean_dec_ref_known(v___x_318_, 1);
v___x_320_ = 0;
v___x_321_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(v_s_311_, v_val_319_, v_rupHints_314_);
switch(lean_obj_tag(v___x_321_))
{
case 0:
{
lean_dec_ref(v_ratHints_315_);
lean_dec_ref(v_pivot_313_);
return v___x_317_;
}
case 1:
{
lean_object* v_assign_322_; lean_object* v___y_324_; lean_object* v_snd_332_; uint8_t v___x_333_; 
v_assign_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc_ref(v_assign_322_);
lean_dec_ref_known(v___x_321_, 1);
v_snd_332_ = lean_ctor_get(v_pivot_313_, 1);
v___x_333_ = lean_unbox(v_snd_332_);
if (v___x_333_ == 0)
{
lean_object* v_fst_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_fst_334_ = lean_ctor_get(v_pivot_313_, 0);
v___x_335_ = lean_box(v___x_317_);
lean_inc(v_fst_334_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_fst_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___y_324_ = v___x_336_;
goto v___jp_323_;
}
else
{
lean_object* v_fst_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_fst_337_ = lean_ctor_get(v_pivot_313_, 0);
v___x_338_ = lean_box(v___x_320_);
lean_inc(v_fst_337_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_fst_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___y_324_ = v___x_339_;
goto v___jp_323_;
}
v___jp_323_:
{
uint8_t v___x_325_; 
lean_inc_ref(v___y_324_);
lean_inc_ref(v_ratHints_315_);
v___x_325_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(v_s_311_, v_ratHints_315_, v___y_324_);
if (v___x_325_ == 0)
{
lean_dec_ref(v___y_324_);
lean_dec_ref(v_assign_322_);
lean_dec_ref(v_ratHints_315_);
lean_dec_ref(v_pivot_313_);
return v___x_320_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_array_get_size(v_ratHints_315_);
v___x_328_ = lean_nat_dec_lt(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_dec_ref(v___y_324_);
lean_dec_ref(v_assign_322_);
lean_dec_ref(v_ratHints_315_);
lean_dec_ref(v_pivot_313_);
return v___x_325_;
}
else
{
if (v___x_328_ == 0)
{
lean_dec_ref(v___y_324_);
lean_dec_ref(v_assign_322_);
lean_dec_ref(v_ratHints_315_);
lean_dec_ref(v_pivot_313_);
return v___x_325_;
}
else
{
size_t v___x_329_; size_t v___x_330_; uint8_t v___x_331_; 
v___x_329_ = ((size_t)0ULL);
v___x_330_ = lean_usize_of_nat(v___x_327_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(v_s_311_, v___x_325_, v_assign_322_, v___y_324_, v_pivot_313_, v_clause_312_, v_ratHints_315_, v___x_329_, v___x_330_);
lean_dec_ref(v_ratHints_315_);
lean_dec_ref(v___y_324_);
if (v___x_331_ == 0)
{
return v___x_328_;
}
else
{
return v___x_320_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_ratHints_315_);
lean_dec_ref(v_pivot_313_);
return v___x_320_;
}
}
}
else
{
lean_dec(v___x_318_);
lean_dec_ref(v_ratHints_315_);
lean_dec_ref(v_pivot_313_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_311_ = stack[0].m_obj;
lean_object* v_clause_312_ = stack[1].m_obj;
lean_object* v_pivot_313_ = stack[2].m_obj;
lean_object* v_rupHints_314_ = stack[3].m_obj;
lean_object* v_ratHints_315_ = stack[4].m_obj;
uint8_t v_res_340_;
v_res_340_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat(v_s_311_, v_clause_312_, v_pivot_313_, v_rupHints_314_, v_ratHints_315_);
stack->m_num = v_res_340_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat___boxed(lean_object* v_s_341_, lean_object* v_clause_342_, lean_object* v_pivot_343_, lean_object* v_rupHints_344_, lean_object* v_ratHints_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat(v_s_341_, v_clause_342_, v_pivot_343_, v_rupHints_344_, v_ratHints_345_);
lean_dec_ref(v_rupHints_344_);
lean_dec_ref(v_clause_342_);
lean_dec_ref(v_s_341_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__9_splitter___redArg(lean_object* v_x_348_, lean_object* v_h__1_349_, lean_object* v_h__2_350_){
_start:
{
if (lean_obj_tag(v_x_348_) == 1)
{
lean_object* v_val_351_; lean_object* v___x_352_; 
lean_dec(v_h__2_350_);
v_val_351_ = lean_ctor_get(v_x_348_, 0);
lean_inc(v_val_351_);
lean_dec_ref_known(v_x_348_, 1);
v___x_352_ = lean_apply_1(v_h__1_349_, v_val_351_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; 
lean_dec(v_h__1_349_);
v___x_353_ = lean_apply_2(v_h__2_350_, v_x_348_, lean_box(0));
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__9_splitter(lean_object* v_motive_354_, lean_object* v_x_355_, lean_object* v_h__1_356_, lean_object* v_h__2_357_){
_start:
{
if (lean_obj_tag(v_x_355_) == 1)
{
lean_object* v_val_358_; lean_object* v___x_359_; 
lean_dec(v_h__2_357_);
v_val_358_ = lean_ctor_get(v_x_355_, 0);
lean_inc(v_val_358_);
lean_dec_ref_known(v_x_355_, 1);
v___x_359_ = lean_apply_1(v_h__1_356_, v_val_358_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; 
lean_dec(v_h__1_356_);
v___x_360_ = lean_apply_2(v_h__2_357_, v_x_355_, lean_box(0));
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__7_splitter___redArg(lean_object* v_x_361_, lean_object* v_h__1_362_, lean_object* v_h__2_363_, lean_object* v_h__3_364_){
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__7_splitter(lean_object* v_motive_371_, lean_object* v_x_372_, lean_object* v_h__1_373_, lean_object* v_h__2_374_, lean_object* v_h__3_375_){
_start:
{
switch(lean_obj_tag(v_x_372_))
{
case 0:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_h__3_375_);
lean_dec(v_h__2_374_);
v___x_376_ = lean_box(0);
v___x_377_ = lean_apply_1(v_h__1_373_, v___x_376_);
return v___x_377_;
}
case 1:
{
lean_object* v_assign_378_; lean_object* v___x_379_; 
lean_dec(v_h__2_374_);
lean_dec(v_h__1_373_);
v_assign_378_ = lean_ctor_get(v_x_372_, 0);
lean_inc_ref(v_assign_378_);
lean_dec_ref_known(v_x_372_, 1);
v___x_379_ = lean_apply_1(v_h__3_375_, v_assign_378_);
return v___x_379_;
}
default: 
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_h__3_375_);
lean_dec(v_h__1_373_);
v___x_380_ = lean_box(0);
v___x_381_ = lean_apply_1(v_h__2_374_, v___x_380_);
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__3_splitter___redArg(lean_object* v_x_382_, lean_object* v_h__1_383_, lean_object* v_h__2_384_){
_start:
{
if (lean_obj_tag(v_x_382_) == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_h__1_383_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_apply_1(v_h__2_384_, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v_val_387_; lean_object* v___x_388_; 
lean_dec(v_h__2_384_);
v_val_387_ = lean_ctor_get(v_x_382_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v_x_382_, 1);
v___x_388_ = lean_apply_1(v_h__1_383_, v_val_387_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__3_splitter(lean_object* v_motive_389_, lean_object* v_x_390_, lean_object* v_h__1_391_, lean_object* v_h__2_392_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_h__1_391_);
v___x_393_ = lean_box(0);
v___x_394_ = lean_apply_1(v_h__2_392_, v___x_393_);
return v___x_394_;
}
else
{
lean_object* v_val_395_; lean_object* v___x_396_; 
lean_dec(v_h__2_392_);
v_val_395_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v_x_390_, 1);
v___x_396_ = lean_apply_1(v_h__1_391_, v_val_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__1_splitter___redArg(lean_object* v_x_397_, lean_object* v_h__1_398_, lean_object* v_h__2_399_){
_start:
{
if (lean_obj_tag(v_x_397_) == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec(v_h__1_398_);
v___x_400_ = lean_box(0);
v___x_401_ = lean_apply_1(v_h__2_399_, v___x_400_);
return v___x_401_;
}
else
{
lean_object* v_val_402_; lean_object* v___x_403_; 
lean_dec(v_h__2_399_);
v_val_402_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v_x_397_, 1);
v___x_403_ = lean_apply_1(v_h__1_398_, v_val_402_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__1_splitter(lean_object* v_motive_404_, lean_object* v_x_405_, lean_object* v_h__1_406_, lean_object* v_h__2_407_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v_h__1_406_);
v___x_408_ = lean_box(0);
v___x_409_ = lean_apply_1(v_h__2_407_, v___x_408_);
return v___x_409_;
}
else
{
lean_object* v_val_410_; lean_object* v___x_411_; 
lean_dec(v_h__2_407_);
v_val_410_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v_x_405_, 1);
v___x_411_ = lean_apply_1(v_h__1_406_, v_val_410_);
return v___x_411_;
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
