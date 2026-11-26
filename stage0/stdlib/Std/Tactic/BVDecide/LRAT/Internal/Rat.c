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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_contains_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_contains_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1;
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_contains_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2(lean_object* v_c_1_, lean_object* v_lit_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_atoms_8_; lean_object* v_polarities_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v_atoms_8_ = lean_ctor_get(v_c_1_, 0);
v_polarities_9_ = lean_ctor_get(v_c_1_, 1);
v___x_10_ = lean_array_get_size(v_atoms_8_);
v___x_11_ = lean_nat_dec_lt(v_i_3_, v___x_10_);
if (v___x_11_ == 0)
{
lean_dec(v_i_3_);
return v___x_11_;
}
else
{
lean_object* v_fst_12_; lean_object* v_snd_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v_fst_12_ = lean_ctor_get(v_lit_2_, 0);
v_snd_13_ = lean_ctor_get(v_lit_2_, 1);
v___x_14_ = lean_array_fget_borrowed(v_atoms_8_, v_i_3_);
v___x_15_ = lean_nat_dec_eq(v___x_14_, v_fst_12_);
if (v___x_15_ == 0)
{
goto v___jp_4_;
}
else
{
uint8_t v___x_16_; uint8_t v___x_17_; uint8_t v___x_18_; uint8_t v___x_19_; 
v___x_16_ = lean_byte_array_fget(v_polarities_9_, v_i_3_);
v___x_17_ = 1;
v___x_18_ = lean_uint8_dec_eq(v___x_16_, v___x_17_);
v___x_19_ = lean_unbox(v_snd_13_);
if (v___x_19_ == 0)
{
if (v___x_18_ == 0)
{
lean_dec(v_i_3_);
return v___x_11_;
}
else
{
goto v___jp_4_;
}
}
else
{
if (v___x_18_ == 0)
{
goto v___jp_4_;
}
else
{
lean_dec(v_i_3_);
return v___x_11_;
}
}
}
}
v___jp_4_:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_add(v_i_3_, v___x_5_);
lean_dec(v_i_3_);
v_i_3_ = v___x_6_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_contains_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2___boxed(lean_object* v_c_20_, lean_object* v_lit_21_, lean_object* v_i_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_contains_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2(v_c_20_, v_lit_21_, v_i_22_);
lean_dec_ref(v_lit_21_);
lean_dec_ref(v_c_20_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5___redArg(lean_object* v_a_25_, lean_object* v_x_26_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
uint8_t v___x_27_; 
v___x_27_ = 0;
return v___x_27_;
}
else
{
lean_object* v_key_28_; lean_object* v_tail_29_; uint8_t v___x_30_; 
v_key_28_ = lean_ctor_get(v_x_26_, 0);
v_tail_29_ = lean_ctor_get(v_x_26_, 2);
v___x_30_ = lean_nat_dec_eq(v_key_28_, v_a_25_);
if (v___x_30_ == 0)
{
v_x_26_ = v_tail_29_;
goto _start;
}
else
{
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5___redArg___boxed(lean_object* v_a_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5___redArg(v_a_32_, v_x_33_);
lean_dec(v_x_33_);
lean_dec(v_a_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___redArg(lean_object* v_m_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_buckets_38_; lean_object* v___x_39_; uint64_t v___x_40_; uint64_t v___x_41_; uint64_t v___x_42_; uint64_t v_fold_43_; uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; size_t v___x_47_; size_t v___x_48_; size_t v___x_49_; size_t v___x_50_; size_t v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v_buckets_38_ = lean_ctor_get(v_m_36_, 1);
v___x_39_ = lean_array_get_size(v_buckets_38_);
v___x_40_ = lean_uint64_of_nat(v_a_37_);
v___x_41_ = 32ULL;
v___x_42_ = lean_uint64_shift_right(v___x_40_, v___x_41_);
v_fold_43_ = lean_uint64_xor(v___x_40_, v___x_42_);
v___x_44_ = 16ULL;
v___x_45_ = lean_uint64_shift_right(v_fold_43_, v___x_44_);
v___x_46_ = lean_uint64_xor(v_fold_43_, v___x_45_);
v___x_47_ = lean_uint64_to_usize(v___x_46_);
v___x_48_ = lean_usize_of_nat(v___x_39_);
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_sub(v___x_48_, v___x_49_);
v___x_51_ = lean_usize_land(v___x_47_, v___x_50_);
v___x_52_ = lean_array_uget_borrowed(v_buckets_38_, v___x_51_);
v___x_53_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5___redArg(v_a_37_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___redArg___boxed(lean_object* v_m_54_, lean_object* v_a_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___redArg(v_m_54_, v_a_55_);
lean_dec(v_a_55_);
lean_dec_ref(v_m_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__4(lean_object* v_negPivot_58_, lean_object* v___x_59_, lean_object* v_s_60_, lean_object* v_i_61_){
_start:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_array_get_size(v_s_60_);
v___x_63_ = lean_nat_dec_lt(v_i_61_, v___x_62_);
if (v___x_63_ == 0)
{
uint8_t v___x_64_; 
lean_dec(v_i_61_);
v___x_64_ = 1;
return v___x_64_;
}
else
{
lean_object* v___x_65_; 
v___x_65_ = lean_array_fget_borrowed(v_s_60_, v_i_61_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_add(v_i_61_, v___x_66_);
lean_dec(v_i_61_);
v_i_61_ = v___x_67_;
goto _start;
}
else
{
lean_object* v_val_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_val_69_ = lean_ctor_get(v___x_65_, 0);
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v_i_61_, v___x_70_);
lean_dec(v_i_61_);
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_contains_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2(v_val_69_, v_negPivot_58_, v___x_72_);
if (v___x_73_ == 0)
{
v_i_61_ = v___x_71_;
goto _start;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___redArg(v___x_59_, v___x_71_);
if (v___x_75_ == 0)
{
lean_dec(v___x_71_);
return v___x_75_;
}
else
{
v_i_61_ = v___x_71_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__4___boxed(lean_object* v_negPivot_77_, lean_object* v___x_78_, lean_object* v_s_79_, lean_object* v_i_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__4(v_negPivot_77_, v___x_78_, v_s_79_, v_i_80_);
lean_dec_ref(v_s_79_);
lean_dec_ref(v___x_78_);
lean_dec_ref(v_negPivot_77_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6_spec__9___redArg(lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
return v_x_83_;
}
else
{
lean_object* v_key_85_; lean_object* v_value_86_; lean_object* v_tail_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_110_; 
v_key_85_ = lean_ctor_get(v_x_84_, 0);
v_value_86_ = lean_ctor_get(v_x_84_, 1);
v_tail_87_ = lean_ctor_get(v_x_84_, 2);
v_isSharedCheck_110_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_110_ == 0)
{
v___x_89_ = v_x_84_;
v_isShared_90_ = v_isSharedCheck_110_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_tail_87_);
lean_inc(v_value_86_);
lean_inc(v_key_85_);
lean_dec(v_x_84_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_110_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; uint64_t v_fold_95_; uint64_t v___x_96_; uint64_t v___x_97_; uint64_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; size_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_91_ = lean_array_get_size(v_x_83_);
v___x_92_ = lean_uint64_of_nat(v_key_85_);
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
v___x_104_ = lean_array_uget_borrowed(v_x_83_, v___x_103_);
lean_inc(v___x_104_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 2, v___x_104_);
v___x_106_ = v___x_89_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_key_85_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_value_86_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v___x_104_);
v___x_106_ = v_reuseFailAlloc_109_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; 
v___x_107_ = lean_array_uset(v_x_83_, v___x_103_, v___x_106_);
v_x_83_ = v___x_107_;
v_x_84_ = v_tail_87_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6___redArg(lean_object* v_i_111_, lean_object* v_source_112_, lean_object* v_target_113_){
_start:
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = lean_array_get_size(v_source_112_);
v___x_115_ = lean_nat_dec_lt(v_i_111_, v___x_114_);
if (v___x_115_ == 0)
{
lean_dec_ref(v_source_112_);
lean_dec(v_i_111_);
return v_target_113_;
}
else
{
lean_object* v_es_116_; lean_object* v___x_117_; lean_object* v_source_118_; lean_object* v_target_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_es_116_ = lean_array_fget(v_source_112_, v_i_111_);
v___x_117_ = lean_box(0);
v_source_118_ = lean_array_fset(v_source_112_, v_i_111_, v___x_117_);
v_target_119_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6_spec__9___redArg(v_target_113_, v_es_116_);
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_add(v_i_111_, v___x_120_);
lean_dec(v_i_111_);
v_i_111_ = v___x_121_;
v_source_112_ = v_source_118_;
v_target_113_ = v_target_119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2___redArg(lean_object* v_data_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v_nbuckets_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_124_ = lean_array_get_size(v_data_123_);
v___x_125_ = lean_unsigned_to_nat(2u);
v_nbuckets_126_ = lean_nat_mul(v___x_124_, v___x_125_);
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_box(0);
v___x_129_ = lean_mk_array(v_nbuckets_126_, v___x_128_);
v___x_130_ = lean_array_propagate_mark(v_data_123_, v___x_129_);
v___x_131_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6___redArg(v___x_127_, v_data_123_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1___redArg(lean_object* v_m_132_, lean_object* v_a_133_, lean_object* v_b_134_){
_start:
{
lean_object* v_size_135_; lean_object* v_buckets_136_; lean_object* v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v_fold_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v_bkt_150_; uint8_t v___x_151_; 
v_size_135_ = lean_ctor_get(v_m_132_, 0);
v_buckets_136_ = lean_ctor_get(v_m_132_, 1);
v___x_137_ = lean_array_get_size(v_buckets_136_);
v___x_138_ = lean_uint64_of_nat(v_a_133_);
v___x_139_ = 32ULL;
v___x_140_ = lean_uint64_shift_right(v___x_138_, v___x_139_);
v_fold_141_ = lean_uint64_xor(v___x_138_, v___x_140_);
v___x_142_ = 16ULL;
v___x_143_ = lean_uint64_shift_right(v_fold_141_, v___x_142_);
v___x_144_ = lean_uint64_xor(v_fold_141_, v___x_143_);
v___x_145_ = lean_uint64_to_usize(v___x_144_);
v___x_146_ = lean_usize_of_nat(v___x_137_);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_sub(v___x_146_, v___x_147_);
v___x_149_ = lean_usize_land(v___x_145_, v___x_148_);
v_bkt_150_ = lean_array_uget_borrowed(v_buckets_136_, v___x_149_);
v___x_151_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5___redArg(v_a_133_, v_bkt_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_172_; 
lean_inc_ref(v_buckets_136_);
lean_inc(v_size_135_);
v_isSharedCheck_172_ = !lean_is_exclusive(v_m_132_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; lean_object* v_unused_174_; 
v_unused_173_ = lean_ctor_get(v_m_132_, 1);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_m_132_, 0);
lean_dec(v_unused_174_);
v___x_153_ = v_m_132_;
v_isShared_154_ = v_isSharedCheck_172_;
goto v_resetjp_152_;
}
else
{
lean_dec(v_m_132_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_172_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v_size_x27_156_; lean_object* v___x_157_; lean_object* v_buckets_x27_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_155_ = lean_unsigned_to_nat(1u);
v_size_x27_156_ = lean_nat_add(v_size_135_, v___x_155_);
lean_dec(v_size_135_);
lean_inc(v_bkt_150_);
v___x_157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_157_, 0, v_a_133_);
lean_ctor_set(v___x_157_, 1, v_b_134_);
lean_ctor_set(v___x_157_, 2, v_bkt_150_);
v_buckets_x27_158_ = lean_array_uset(v_buckets_136_, v___x_149_, v___x_157_);
v___x_159_ = lean_unsigned_to_nat(4u);
v___x_160_ = lean_nat_mul(v_size_x27_156_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(3u);
v___x_162_ = lean_nat_div(v___x_160_, v___x_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_array_get_size(v_buckets_x27_158_);
v___x_164_ = lean_nat_dec_le(v___x_162_, v___x_163_);
lean_dec(v___x_162_);
if (v___x_164_ == 0)
{
lean_object* v_val_165_; lean_object* v___x_167_; 
v_val_165_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2___redArg(v_buckets_x27_158_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v_val_165_);
lean_ctor_set(v___x_153_, 0, v_size_x27_156_);
v___x_167_ = v___x_153_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_size_x27_156_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_val_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
else
{
lean_object* v___x_170_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v_buckets_x27_158_);
lean_ctor_set(v___x_153_, 0, v_size_x27_156_);
v___x_170_ = v___x_153_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_size_x27_156_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_buckets_x27_158_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
else
{
lean_dec(v_b_134_);
lean_dec(v_a_133_);
return v_m_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(lean_object* v_as_175_, size_t v_sz_176_, size_t v_i_177_, lean_object* v_b_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = lean_usize_dec_lt(v_i_177_, v_sz_176_);
if (v___x_179_ == 0)
{
return v_b_178_;
}
else
{
lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v_r_182_; size_t v___x_183_; size_t v___x_184_; 
v_a_180_ = lean_array_uget_borrowed(v_as_175_, v_i_177_);
v___x_181_ = lean_box(0);
lean_inc(v_a_180_);
v_r_182_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1___redArg(v_b_178_, v_a_180_, v___x_181_);
v___x_183_ = ((size_t)1ULL);
v___x_184_ = lean_usize_add(v_i_177_, v___x_183_);
v_i_177_ = v___x_184_;
v_b_178_ = v_r_182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2___boxed(lean_object* v_as_186_, lean_object* v_sz_187_, lean_object* v_i_188_, lean_object* v_b_189_){
_start:
{
size_t v_sz_boxed_190_; size_t v_i_boxed_191_; lean_object* v_res_192_; 
v_sz_boxed_190_ = lean_unbox_usize(v_sz_187_);
lean_dec(v_sz_187_);
v_i_boxed_191_ = lean_unbox_usize(v_i_188_);
lean_dec(v_i_188_);
v_res_192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(v_as_186_, v_sz_boxed_190_, v_i_boxed_191_, v_b_189_);
lean_dec_ref(v_as_186_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1(lean_object* v_m_193_, lean_object* v_l_194_){
_start:
{
size_t v_sz_195_; size_t v___x_196_; lean_object* v___x_197_; 
v_sz_195_ = lean_array_size(v_l_194_);
v___x_196_ = ((size_t)0ULL);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__2(v_l_194_, v_sz_195_, v___x_196_, v_m_193_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1___boxed(lean_object* v_m_198_, lean_object* v_l_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1(v_m_198_, v_l_199_);
lean_dec_ref(v_l_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(size_t v_sz_201_, size_t v_i_202_, lean_object* v_bs_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = lean_usize_dec_lt(v_i_202_, v_sz_201_);
if (v___x_204_ == 0)
{
return v_bs_203_;
}
else
{
lean_object* v_v_205_; lean_object* v_fst_206_; lean_object* v___x_207_; lean_object* v_bs_x27_208_; size_t v___x_209_; size_t v___x_210_; lean_object* v___x_211_; 
v_v_205_ = lean_array_uget_borrowed(v_bs_203_, v_i_202_);
v_fst_206_ = lean_ctor_get(v_v_205_, 0);
lean_inc(v_fst_206_);
v___x_207_ = lean_unsigned_to_nat(0u);
v_bs_x27_208_ = lean_array_uset(v_bs_203_, v_i_202_, v___x_207_);
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_add(v_i_202_, v___x_209_);
v___x_211_ = lean_array_uset(v_bs_x27_208_, v_i_202_, v_fst_206_);
v_i_202_ = v___x_210_;
v_bs_203_ = v___x_211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0___boxed(lean_object* v_sz_213_, lean_object* v_i_214_, lean_object* v_bs_215_){
_start:
{
size_t v_sz_boxed_216_; size_t v_i_boxed_217_; lean_object* v_res_218_; 
v_sz_boxed_216_ = lean_unbox_usize(v_sz_213_);
lean_dec(v_sz_213_);
v_i_boxed_217_ = lean_unbox_usize(v_i_214_);
lean_dec(v_i_214_);
v_res_218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(v_sz_boxed_216_, v_i_boxed_217_, v_bs_215_);
return v_res_218_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_box(0);
v___x_220_ = lean_unsigned_to_nat(16u);
v___x_221_ = lean_mk_array(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__0);
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
return v___x_224_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(lean_object* v_s_225_, lean_object* v_ratHints_226_, lean_object* v_negPivot_227_){
_start:
{
size_t v_sz_228_; size_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_sz_228_ = lean_array_size(v_ratHints_226_);
v___x_229_ = ((size_t)0ULL);
v___x_230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__0(v_sz_228_, v___x_229_, v_ratHints_226_);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1, &l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___closed__1);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1(v___x_232_, v___x_230_);
lean_dec_ref(v___x_230_);
v___x_234_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__4(v_negPivot_227_, v___x_233_, v_s_225_, v___x_231_);
lean_dec_ref(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive___boxed(lean_object* v_s_235_, lean_object* v_ratHints_236_, lean_object* v_negPivot_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(v_s_235_, v_ratHints_236_, v_negPivot_237_);
lean_dec_ref(v_negPivot_237_);
lean_dec_ref(v_s_235_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3(lean_object* v_00_u03b2_240_, lean_object* v_m_241_, lean_object* v_a_242_){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___redArg(v_m_241_, v_a_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3___boxed(lean_object* v_00_u03b2_244_, lean_object* v_m_245_, lean_object* v_a_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3(v_00_u03b2_244_, v_m_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_m_245_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1(lean_object* v_00_u03b2_249_, lean_object* v_m_250_, lean_object* v_a_251_, lean_object* v_b_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1___redArg(v_m_250_, v_a_251_, v_b_252_);
return v___x_253_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5(lean_object* v_00_u03b2_254_, lean_object* v_a_255_, lean_object* v_x_256_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5___redArg(v_a_255_, v_x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5___boxed(lean_object* v_00_u03b2_258_, lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__3_spec__5(v_00_u03b2_258_, v_a_259_, v_x_260_);
lean_dec(v_x_260_);
lean_dec(v_a_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_263_, lean_object* v_data_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2___redArg(v_data_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_266_, lean_object* v_i_267_, lean_object* v_source_268_, lean_object* v_target_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6___redArg(v_i_267_, v_source_268_, v_target_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__1_spec__1_spec__2_spec__6_spec__9___redArg(v_x_272_, v_x_273_);
return v___x_274_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(lean_object* v_s_275_, uint8_t v___x_276_, lean_object* v_assign_277_, lean_object* v___y_278_, lean_object* v_as_279_, size_t v_i_280_, size_t v_stop_281_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = lean_usize_dec_eq(v_i_280_, v_stop_281_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v_fst_288_; lean_object* v_snd_289_; uint8_t v___x_290_; uint8_t v___y_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_287_ = lean_array_uget_borrowed(v_as_279_, v_i_280_);
v_fst_288_ = lean_ctor_get(v___x_287_, 0);
v_snd_289_ = lean_ctor_get(v___x_287_, 1);
v___x_290_ = 1;
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_sub(v_fst_288_, v___x_293_);
v___x_295_ = lean_array_get_size(v_s_275_);
v___x_296_ = lean_nat_dec_lt(v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_dec(v___x_294_);
v___y_292_ = v___x_276_;
goto v___jp_291_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_array_fget_borrowed(v_s_275_, v___x_294_);
lean_dec(v___x_294_);
if (lean_obj_tag(v___x_297_) == 0)
{
v___y_292_ = v___x_276_;
goto v___jp_291_;
}
else
{
lean_object* v_val_298_; lean_object* v___x_299_; 
v_val_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc_ref(v_assign_277_);
v___x_299_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_extendOfClauseWithout(v_assign_277_, v_val_298_, v___y_278_);
if (lean_obj_tag(v___x_299_) == 0)
{
goto v___jp_282_;
}
else
{
lean_object* v_val_300_; uint8_t v___x_301_; 
v_val_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_val_300_);
lean_dec_ref_known(v___x_299_, 1);
v___x_301_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_275_, v_val_300_, v_snd_289_);
if (v___x_301_ == 0)
{
v___y_292_ = v___x_276_;
goto v___jp_291_;
}
else
{
goto v___jp_282_;
}
}
}
}
v___jp_291_:
{
if (v___y_292_ == 0)
{
goto v___jp_282_;
}
else
{
lean_dec_ref(v_assign_277_);
return v___x_290_;
}
}
}
else
{
uint8_t v___x_302_; 
lean_dec_ref(v_assign_277_);
v___x_302_ = 0;
return v___x_302_;
}
v___jp_282_:
{
size_t v___x_283_; size_t v___x_284_; 
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_add(v_i_280_, v___x_283_);
v_i_280_ = v___x_284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0___boxed(lean_object* v_s_303_, lean_object* v___x_304_, lean_object* v_assign_305_, lean_object* v___y_306_, lean_object* v_as_307_, lean_object* v_i_308_, lean_object* v_stop_309_){
_start:
{
uint8_t v___x_996__boxed_310_; size_t v_i_boxed_311_; size_t v_stop_boxed_312_; uint8_t v_res_313_; lean_object* v_r_314_; 
v___x_996__boxed_310_ = lean_unbox(v___x_304_);
v_i_boxed_311_ = lean_unbox_usize(v_i_308_);
lean_dec(v_i_308_);
v_stop_boxed_312_ = lean_unbox_usize(v_stop_309_);
lean_dec(v_stop_309_);
v_res_313_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(v_s_303_, v___x_996__boxed_310_, v_assign_305_, v___y_306_, v_as_307_, v_i_boxed_311_, v_stop_boxed_312_);
lean_dec_ref(v_as_307_);
lean_dec_ref(v___y_306_);
lean_dec_ref(v_s_303_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat(lean_object* v_s_315_, lean_object* v_clause_316_, lean_object* v_pivot_317_, lean_object* v_rupHints_318_, lean_object* v_ratHints_319_){
_start:
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_contains_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive_spec__2(v_clause_316_, v_pivot_317_, v___x_320_);
if (v___x_321_ == 0)
{
lean_dec_ref(v_ratHints_319_);
lean_dec_ref(v_pivot_317_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(v_clause_316_);
if (lean_obj_tag(v___x_322_) == 1)
{
lean_object* v_val_323_; uint8_t v___x_324_; lean_object* v___x_325_; 
v_val_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_val_323_);
lean_dec_ref_known(v___x_322_, 1);
v___x_324_ = 0;
v___x_325_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(v_s_315_, v_val_323_, v_rupHints_318_);
switch(lean_obj_tag(v___x_325_))
{
case 0:
{
lean_dec_ref(v_ratHints_319_);
lean_dec_ref(v_pivot_317_);
return v___x_321_;
}
case 1:
{
lean_object* v_assign_326_; lean_object* v___y_328_; lean_object* v_snd_335_; uint8_t v___x_336_; 
v_assign_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_assign_326_);
lean_dec_ref_known(v___x_325_, 1);
v_snd_335_ = lean_ctor_get(v_pivot_317_, 1);
v___x_336_ = lean_unbox(v_snd_335_);
if (v___x_336_ == 0)
{
lean_object* v_fst_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_345_; 
v_fst_337_ = lean_ctor_get(v_pivot_317_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_pivot_317_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v_pivot_317_, 1);
lean_dec(v_unused_346_);
v___x_339_ = v_pivot_317_;
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_fst_337_);
lean_dec(v_pivot_317_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_box(v___x_321_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_fst_337_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
v___y_328_ = v___x_343_;
goto v___jp_327_;
}
}
}
else
{
lean_object* v_fst_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_355_; 
v_fst_347_ = lean_ctor_get(v_pivot_317_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_pivot_317_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; 
v_unused_356_ = lean_ctor_get(v_pivot_317_, 1);
lean_dec(v_unused_356_);
v___x_349_ = v_pivot_317_;
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_fst_347_);
lean_dec(v_pivot_317_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_box(v___x_324_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v___x_351_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_fst_347_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
v___y_328_ = v___x_353_;
goto v___jp_327_;
}
}
}
v___jp_327_:
{
uint8_t v___x_329_; 
lean_inc_ref(v_ratHints_319_);
v___x_329_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRatHintsExhaustive(v_s_315_, v_ratHints_319_, v___y_328_);
if (v___x_329_ == 0)
{
lean_dec_ref(v___y_328_);
lean_dec_ref(v_assign_326_);
lean_dec_ref(v_ratHints_319_);
return v___x_324_;
}
else
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_array_get_size(v_ratHints_319_);
v___x_331_ = lean_nat_dec_lt(v___x_320_, v___x_330_);
if (v___x_331_ == 0)
{
lean_dec_ref(v___y_328_);
lean_dec_ref(v_assign_326_);
lean_dec_ref(v_ratHints_319_);
return v___x_329_;
}
else
{
if (v___x_331_ == 0)
{
lean_dec_ref(v___y_328_);
lean_dec_ref(v_assign_326_);
lean_dec_ref(v_ratHints_319_);
return v___x_329_;
}
else
{
size_t v___x_332_; size_t v___x_333_; uint8_t v___x_334_; 
v___x_332_ = ((size_t)0ULL);
v___x_333_ = lean_usize_of_nat(v___x_330_);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_spec__0(v_s_315_, v___x_329_, v_assign_326_, v___y_328_, v_ratHints_319_, v___x_332_, v___x_333_);
lean_dec_ref(v_ratHints_319_);
lean_dec_ref(v___y_328_);
if (v___x_334_ == 0)
{
return v___x_331_;
}
else
{
return v___x_324_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_ratHints_319_);
lean_dec_ref(v_pivot_317_);
return v___x_324_;
}
}
}
else
{
lean_dec(v___x_322_);
lean_dec_ref(v_ratHints_319_);
lean_dec_ref(v_pivot_317_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat___boxed(lean_object* v_s_357_, lean_object* v_clause_358_, lean_object* v_pivot_359_, lean_object* v_rupHints_360_, lean_object* v_ratHints_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat(v_s_357_, v_clause_358_, v_pivot_359_, v_rupHints_360_, v_ratHints_361_);
lean_dec_ref(v_rupHints_360_);
lean_dec_ref(v_clause_358_);
lean_dec_ref(v_s_357_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__9_splitter___redArg(lean_object* v_x_364_, lean_object* v_h__1_365_, lean_object* v_h__2_366_){
_start:
{
if (lean_obj_tag(v_x_364_) == 1)
{
lean_object* v_val_367_; lean_object* v___x_368_; 
lean_dec(v_h__2_366_);
v_val_367_ = lean_ctor_get(v_x_364_, 0);
lean_inc(v_val_367_);
lean_dec_ref_known(v_x_364_, 1);
v___x_368_ = lean_apply_1(v_h__1_365_, v_val_367_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; 
lean_dec(v_h__1_365_);
v___x_369_ = lean_apply_2(v_h__2_366_, v_x_364_, lean_box(0));
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__9_splitter(lean_object* v_motive_370_, lean_object* v_x_371_, lean_object* v_h__1_372_, lean_object* v_h__2_373_){
_start:
{
if (lean_obj_tag(v_x_371_) == 1)
{
lean_object* v_val_374_; lean_object* v___x_375_; 
lean_dec(v_h__2_373_);
v_val_374_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v_x_371_, 1);
v___x_375_ = lean_apply_1(v_h__1_372_, v_val_374_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; 
lean_dec(v_h__1_372_);
v___x_376_ = lean_apply_2(v_h__2_373_, v_x_371_, lean_box(0));
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__7_splitter___redArg(lean_object* v_x_377_, lean_object* v_h__1_378_, lean_object* v_h__2_379_, lean_object* v_h__3_380_){
_start:
{
switch(lean_obj_tag(v_x_377_))
{
case 0:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_h__3_380_);
lean_dec(v_h__2_379_);
v___x_381_ = lean_box(0);
v___x_382_ = lean_apply_1(v_h__1_378_, v___x_381_);
return v___x_382_;
}
case 1:
{
lean_object* v_assign_383_; lean_object* v___x_384_; 
lean_dec(v_h__2_379_);
lean_dec(v_h__1_378_);
v_assign_383_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_assign_383_);
lean_dec_ref_known(v_x_377_, 1);
v___x_384_ = lean_apply_1(v_h__3_380_, v_assign_383_);
return v___x_384_;
}
default: 
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_h__3_380_);
lean_dec(v_h__1_378_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_apply_1(v_h__2_379_, v___x_385_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__7_splitter(lean_object* v_motive_387_, lean_object* v_x_388_, lean_object* v_h__1_389_, lean_object* v_h__2_390_, lean_object* v_h__3_391_){
_start:
{
switch(lean_obj_tag(v_x_388_))
{
case 0:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec(v_h__3_391_);
lean_dec(v_h__2_390_);
v___x_392_ = lean_box(0);
v___x_393_ = lean_apply_1(v_h__1_389_, v___x_392_);
return v___x_393_;
}
case 1:
{
lean_object* v_assign_394_; lean_object* v___x_395_; 
lean_dec(v_h__2_390_);
lean_dec(v_h__1_389_);
v_assign_394_ = lean_ctor_get(v_x_388_, 0);
lean_inc_ref(v_assign_394_);
lean_dec_ref_known(v_x_388_, 1);
v___x_395_ = lean_apply_1(v_h__3_391_, v_assign_394_);
return v___x_395_;
}
default: 
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec(v_h__3_391_);
lean_dec(v_h__1_389_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_apply_1(v_h__2_390_, v___x_396_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__3_splitter___redArg(lean_object* v_x_398_, lean_object* v_h__1_399_, lean_object* v_h__2_400_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec(v_h__1_399_);
v___x_401_ = lean_box(0);
v___x_402_ = lean_apply_1(v_h__2_400_, v___x_401_);
return v___x_402_;
}
else
{
lean_object* v_val_403_; lean_object* v___x_404_; 
lean_dec(v_h__2_400_);
v_val_403_ = lean_ctor_get(v_x_398_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v_x_398_, 1);
v___x_404_ = lean_apply_1(v_h__1_399_, v_val_403_);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__3_splitter(lean_object* v_motive_405_, lean_object* v_x_406_, lean_object* v_h__1_407_, lean_object* v_h__2_408_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v_h__1_407_);
v___x_409_ = lean_box(0);
v___x_410_ = lean_apply_1(v_h__2_408_, v___x_409_);
return v___x_410_;
}
else
{
lean_object* v_val_411_; lean_object* v___x_412_; 
lean_dec(v_h__2_408_);
v_val_411_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_val_411_);
lean_dec_ref_known(v_x_406_, 1);
v___x_412_ = lean_apply_1(v_h__1_407_, v_val_411_);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__1_splitter___redArg(lean_object* v_x_413_, lean_object* v_h__1_414_, lean_object* v_h__2_415_){
_start:
{
if (lean_obj_tag(v_x_413_) == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec(v_h__1_414_);
v___x_416_ = lean_box(0);
v___x_417_ = lean_apply_1(v_h__2_415_, v___x_416_);
return v___x_417_;
}
else
{
lean_object* v_val_418_; lean_object* v___x_419_; 
lean_dec(v_h__2_415_);
v_val_418_ = lean_ctor_get(v_x_413_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v_x_413_, 1);
v___x_419_ = lean_apply_1(v_h__1_414_, v_val_418_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rat_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkRat_match__1_splitter(lean_object* v_motive_420_, lean_object* v_x_421_, lean_object* v_h__1_422_, lean_object* v_h__2_423_){
_start:
{
if (lean_obj_tag(v_x_421_) == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v_h__1_422_);
v___x_424_ = lean_box(0);
v___x_425_ = lean_apply_1(v_h__2_423_, v___x_424_);
return v___x_425_;
}
else
{
lean_object* v_val_426_; lean_object* v___x_427_; 
lean_dec(v_h__2_423_);
v_val_426_ = lean_ctor_get(v_x_421_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v_x_421_, 1);
v___x_427_ = lean_apply_1(v_h__1_422_, v_val_426_);
return v___x_427_;
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
