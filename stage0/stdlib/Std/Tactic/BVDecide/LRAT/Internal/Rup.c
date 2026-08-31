// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Rup
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Basic public import Std.Tactic.BVDecide.LRAT.Internal.Assignment import Init.Omega import Init.ByCases import Std.Sat.CNF.SpecLemmas import Std.Tactic.Do
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_byte_array_uget(lean_object*, size_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_conflict_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_conflict_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_extended_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_extended_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_error_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_error_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0 = (const lean_object*)&l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__28_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__28_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__10_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__10_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 1)
{
lean_object* v_assign_9_; lean_object* v___x_10_; 
v_assign_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc_ref(v_assign_9_);
lean_dec_ref_known(v_t_7_, 1);
v___x_10_ = lean_apply_1(v_k_8_, v_assign_9_);
return v___x_10_;
}
else
{
lean_dec(v_t_7_);
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_conflict_elim___redArg(lean_object* v_t_23_, lean_object* v_conflict_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_23_, v_conflict_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_conflict_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_conflict_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_27_, v_conflict_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_extended_elim___redArg(lean_object* v_t_31_, lean_object* v_extended_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_31_, v_extended_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_extended_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_extended_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_35_, v_extended_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_error_elim___redArg(lean_object* v_t_39_, lean_object* v_error_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_39_, v_error_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_error_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_error_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_43_, v_error_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg(lean_object* v_a_47_, lean_object* v_fallback_48_, lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_inc(v_fallback_48_);
return v_fallback_48_;
}
else
{
lean_object* v_key_50_; lean_object* v_value_51_; lean_object* v_tail_52_; uint8_t v___x_53_; 
v_key_50_ = lean_ctor_get(v_x_49_, 0);
v_value_51_ = lean_ctor_get(v_x_49_, 1);
v_tail_52_ = lean_ctor_get(v_x_49_, 2);
v___x_53_ = lean_nat_dec_eq(v_key_50_, v_a_47_);
if (v___x_53_ == 0)
{
v_x_49_ = v_tail_52_;
goto _start;
}
else
{
lean_inc(v_value_51_);
return v_value_51_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg___boxed(lean_object* v_a_55_, lean_object* v_fallback_56_, lean_object* v_x_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg(v_a_55_, v_fallback_56_, v_x_57_);
lean_dec(v_x_57_);
lean_dec(v_fallback_56_);
lean_dec(v_a_55_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(lean_object* v_m_59_, lean_object* v_a_60_, lean_object* v_fallback_61_){
_start:
{
lean_object* v_buckets_62_; lean_object* v___x_63_; uint64_t v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v_fold_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_buckets_62_ = lean_ctor_get(v_m_59_, 1);
v___x_63_ = lean_array_get_size(v_buckets_62_);
v___x_64_ = lean_uint64_of_nat(v_a_60_);
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
v___x_76_ = lean_array_uget_borrowed(v_buckets_62_, v___x_75_);
v___x_77_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg(v_a_60_, v_fallback_61_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg___boxed(lean_object* v_m_78_, lean_object* v_a_79_, lean_object* v_fallback_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(v_m_78_, v_a_79_, v_fallback_80_);
lean_dec(v_fallback_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_m_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7___redArg(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
return v_x_82_;
}
else
{
lean_object* v_key_84_; lean_object* v_value_85_; lean_object* v_tail_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_109_; 
v_key_84_ = lean_ctor_get(v_x_83_, 0);
v_value_85_ = lean_ctor_get(v_x_83_, 1);
v_tail_86_ = lean_ctor_get(v_x_83_, 2);
v_isSharedCheck_109_ = !lean_is_exclusive(v_x_83_);
if (v_isSharedCheck_109_ == 0)
{
v___x_88_ = v_x_83_;
v_isShared_89_ = v_isSharedCheck_109_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_tail_86_);
lean_inc(v_value_85_);
lean_inc(v_key_84_);
lean_dec(v_x_83_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_109_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v_fold_94_; uint64_t v___x_95_; uint64_t v___x_96_; uint64_t v___x_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_90_ = lean_array_get_size(v_x_82_);
v___x_91_ = lean_uint64_of_nat(v_key_84_);
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
v___x_103_ = lean_array_uget_borrowed(v_x_82_, v___x_102_);
lean_inc(v___x_103_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 2, v___x_103_);
v___x_105_ = v___x_88_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_key_84_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_value_85_);
lean_ctor_set(v_reuseFailAlloc_108_, 2, v___x_103_);
v___x_105_ = v_reuseFailAlloc_108_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; 
v___x_106_ = lean_array_uset(v_x_82_, v___x_102_, v___x_105_);
v_x_82_ = v___x_106_;
v_x_83_ = v_tail_86_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4___redArg(lean_object* v_i_110_, lean_object* v_source_111_, lean_object* v_target_112_){
_start:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_array_get_size(v_source_111_);
v___x_114_ = lean_nat_dec_lt(v_i_110_, v___x_113_);
if (v___x_114_ == 0)
{
lean_dec_ref(v_source_111_);
lean_dec(v_i_110_);
return v_target_112_;
}
else
{
lean_object* v_es_115_; lean_object* v___x_116_; lean_object* v_source_117_; lean_object* v_target_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_es_115_ = lean_array_fget(v_source_111_, v_i_110_);
v___x_116_ = lean_box(0);
v_source_117_ = lean_array_fset(v_source_111_, v_i_110_, v___x_116_);
v_target_118_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7___redArg(v_target_112_, v_es_115_);
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_i_110_, v___x_119_);
lean_dec(v_i_110_);
v_i_110_ = v___x_120_;
v_source_111_ = v_source_117_;
v_target_112_ = v_target_118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3___redArg(lean_object* v_data_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_nbuckets_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_123_ = lean_array_get_size(v_data_122_);
v___x_124_ = lean_unsigned_to_nat(2u);
v_nbuckets_125_ = lean_nat_mul(v___x_123_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_box(0);
v___x_128_ = lean_mk_array(v_nbuckets_125_, v___x_127_);
v___x_129_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4___redArg(v___x_126_, v_data_122_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(lean_object* v_a_130_, lean_object* v_x_131_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
else
{
lean_object* v_key_133_; lean_object* v_tail_134_; uint8_t v___x_135_; 
v_key_133_ = lean_ctor_get(v_x_131_, 0);
v_tail_134_ = lean_ctor_get(v_x_131_, 2);
v___x_135_ = lean_nat_dec_eq(v_key_133_, v_a_130_);
if (v___x_135_ == 0)
{
v_x_131_ = v_tail_134_;
goto _start;
}
else
{
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg___boxed(lean_object* v_a_137_, lean_object* v_x_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(v_a_137_, v_x_138_);
lean_dec(v_x_138_);
lean_dec(v_a_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(lean_object* v_a_141_, lean_object* v_b_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
lean_dec(v_b_142_);
lean_dec(v_a_141_);
return v_x_143_;
}
else
{
lean_object* v_key_144_; lean_object* v_value_145_; lean_object* v_tail_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_158_; 
v_key_144_ = lean_ctor_get(v_x_143_, 0);
v_value_145_ = lean_ctor_get(v_x_143_, 1);
v_tail_146_ = lean_ctor_get(v_x_143_, 2);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_143_);
if (v_isSharedCheck_158_ == 0)
{
v___x_148_ = v_x_143_;
v_isShared_149_ = v_isSharedCheck_158_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_tail_146_);
lean_inc(v_value_145_);
lean_inc(v_key_144_);
lean_dec(v_x_143_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_158_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_eq(v_key_144_, v_a_141_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(v_a_141_, v_b_142_, v_tail_146_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 2, v___x_151_);
v___x_153_ = v___x_148_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_key_144_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_value_145_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
else
{
lean_object* v___x_156_; 
lean_dec(v_value_145_);
lean_dec(v_key_144_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v_b_142_);
lean_ctor_set(v___x_148_, 0, v_a_141_);
v___x_156_ = v___x_148_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_141_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_b_142_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_tail_146_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(lean_object* v_m_159_, lean_object* v_a_160_, lean_object* v_b_161_){
_start:
{
lean_object* v_size_162_; lean_object* v_buckets_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_206_; 
v_size_162_ = lean_ctor_get(v_m_159_, 0);
v_buckets_163_ = lean_ctor_get(v_m_159_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_m_159_);
if (v_isSharedCheck_206_ == 0)
{
v___x_165_ = v_m_159_;
v_isShared_166_ = v_isSharedCheck_206_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_buckets_163_);
lean_inc(v_size_162_);
lean_dec(v_m_159_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_206_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v_fold_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; lean_object* v_bkt_180_; uint8_t v___x_181_; 
v___x_167_ = lean_array_get_size(v_buckets_163_);
v___x_168_ = lean_uint64_of_nat(v_a_160_);
v___x_169_ = 32ULL;
v___x_170_ = lean_uint64_shift_right(v___x_168_, v___x_169_);
v_fold_171_ = lean_uint64_xor(v___x_168_, v___x_170_);
v___x_172_ = 16ULL;
v___x_173_ = lean_uint64_shift_right(v_fold_171_, v___x_172_);
v___x_174_ = lean_uint64_xor(v_fold_171_, v___x_173_);
v___x_175_ = lean_uint64_to_usize(v___x_174_);
v___x_176_ = lean_usize_of_nat(v___x_167_);
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_sub(v___x_176_, v___x_177_);
v___x_179_ = lean_usize_land(v___x_175_, v___x_178_);
v_bkt_180_ = lean_array_uget_borrowed(v_buckets_163_, v___x_179_);
v___x_181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(v_a_160_, v_bkt_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v_size_x27_183_; lean_object* v___x_184_; lean_object* v_buckets_x27_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v_size_x27_183_ = lean_nat_add(v_size_162_, v___x_182_);
lean_dec(v_size_162_);
lean_inc(v_bkt_180_);
v___x_184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_184_, 0, v_a_160_);
lean_ctor_set(v___x_184_, 1, v_b_161_);
lean_ctor_set(v___x_184_, 2, v_bkt_180_);
v_buckets_x27_185_ = lean_array_uset(v_buckets_163_, v___x_179_, v___x_184_);
v___x_186_ = lean_unsigned_to_nat(4u);
v___x_187_ = lean_nat_mul(v_size_x27_183_, v___x_186_);
v___x_188_ = lean_unsigned_to_nat(3u);
v___x_189_ = lean_nat_div(v___x_187_, v___x_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_array_get_size(v_buckets_x27_185_);
v___x_191_ = lean_nat_dec_le(v___x_189_, v___x_190_);
lean_dec(v___x_189_);
if (v___x_191_ == 0)
{
lean_object* v_val_192_; lean_object* v___x_194_; 
v_val_192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3___redArg(v_buckets_x27_185_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v_val_192_);
lean_ctor_set(v___x_165_, 0, v_size_x27_183_);
v___x_194_ = v___x_165_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_size_x27_183_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_val_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
else
{
lean_object* v___x_197_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v_buckets_x27_185_);
lean_ctor_set(v___x_165_, 0, v_size_x27_183_);
v___x_197_ = v___x_165_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_size_x27_183_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_buckets_x27_185_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
else
{
lean_object* v___x_199_; lean_object* v_buckets_x27_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
lean_inc(v_bkt_180_);
v___x_199_ = lean_box(0);
v_buckets_x27_200_ = lean_array_uset(v_buckets_163_, v___x_179_, v___x_199_);
v___x_201_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(v_a_160_, v_b_161_, v_bkt_180_);
v___x_202_ = lean_array_uset(v_buckets_x27_200_, v___x_179_, v___x_201_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v___x_202_);
v___x_204_ = v___x_165_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_size_162_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(lean_object* v___x_209_, lean_object* v___x_210_, lean_object* v_c_211_, size_t v_sz_212_, size_t v_i_213_, lean_object* v_b_214_){
_start:
{
lean_object* v_a_216_; uint8_t v___x_220_; 
v___x_220_ = lean_usize_dec_lt(v_i_213_, v_sz_212_);
if (v___x_220_ == 0)
{
lean_dec_ref(v_c_211_);
return v_b_214_;
}
else
{
lean_object* v_snd_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_301_; 
v_snd_221_ = lean_ctor_get(v_b_214_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v_b_214_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v_b_214_, 0);
lean_dec(v_unused_302_);
v___x_223_ = v_b_214_;
v_isShared_224_ = v_isSharedCheck_301_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_snd_221_);
lean_dec(v_b_214_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_301_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_atoms_225_; lean_object* v_polarities_226_; lean_object* v_fst_227_; lean_object* v_snd_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_300_; 
v_atoms_225_ = lean_ctor_get(v_c_211_, 0);
v_polarities_226_ = lean_ctor_get(v_c_211_, 1);
v_fst_227_ = lean_ctor_get(v_snd_221_, 0);
v_snd_228_ = lean_ctor_get(v_snd_221_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v_snd_221_);
if (v_isSharedCheck_300_ == 0)
{
v___x_230_ = v_snd_221_;
v_isShared_231_ = v_isSharedCheck_300_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_snd_228_);
lean_inc(v_fst_227_);
lean_dec(v_snd_221_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_300_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___y_235_; uint8_t v___y_236_; uint8_t v___x_263_; uint8_t v___x_264_; uint8_t v___x_265_; uint8_t v___x_266_; uint8_t v___y_268_; uint8_t v___y_269_; uint8_t v_val_271_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_232_ = lean_array_uget_borrowed(v_atoms_225_, v_i_213_);
v___x_233_ = lean_box(0);
v___x_263_ = lean_nat_dec_lt(v___x_209_, v___x_210_);
v___x_264_ = lean_byte_array_uget(v_polarities_226_, v_i_213_);
v___x_265_ = 1;
v___x_266_ = lean_uint8_dec_eq(v___x_264_, v___x_265_);
v___x_275_ = 0;
v___x_276_ = lean_box(v___x_275_);
v___x_277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(v_fst_227_, v___x_232_, v___x_276_);
lean_dec(v___x_276_);
v___x_278_ = lean_unbox(v___x_277_);
lean_dec(v___x_277_);
switch(v___x_278_)
{
case 0:
{
lean_del_object(v___x_230_);
lean_del_object(v___x_223_);
if (lean_obj_tag(v_snd_228_) == 0)
{
lean_object* v___x_279_; uint8_t v___y_281_; 
lean_inc(v___x_232_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_232_);
if (v___x_266_ == 0)
{
uint8_t v___x_286_; 
v___x_286_ = 2;
v___y_281_ = v___x_286_;
goto v___jp_280_;
}
else
{
uint8_t v___x_287_; 
v___x_287_ = 1;
v___y_281_ = v___x_287_;
goto v___jp_280_;
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_282_ = lean_box(v___y_281_);
lean_inc(v___x_232_);
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(v_fst_227_, v___x_232_, v___x_282_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_279_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_233_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v_a_216_ = v___x_285_;
goto v___jp_215_;
}
}
else
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_296_; 
v_isSharedCheck_296_ = !lean_is_exclusive(v_c_211_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_297_ = lean_ctor_get(v_c_211_, 1);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_c_211_, 0);
lean_dec(v_unused_298_);
v___x_289_ = v_c_211_;
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
else
{
lean_dec(v_c_211_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v_snd_228_);
lean_ctor_set(v___x_289_, 0, v_fst_227_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_snd_228_);
v___x_293_ = v_reuseFailAlloc_295_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_291_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
return v___x_294_;
}
}
}
}
case 1:
{
v_val_271_ = v___x_263_;
goto v___jp_270_;
}
default: 
{
uint8_t v___x_299_; 
v___x_299_ = 0;
v_val_271_ = v___x_299_;
goto v___jp_270_;
}
}
v___jp_234_:
{
if (v___y_236_ == 0)
{
if (v___y_235_ == 0)
{
lean_object* v___x_238_; 
if (v_isShared_231_ == 0)
{
v___x_238_ = v___x_230_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_snd_228_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_238_);
lean_ctor_set(v___x_223_, 0, v___x_233_);
v___x_240_ = v___x_223_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
v_a_216_ = v___x_240_;
goto v___jp_215_;
}
}
}
else
{
lean_object* v___x_243_; lean_object* v___x_245_; 
lean_dec_ref(v_c_211_);
v___x_243_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_231_ == 0)
{
v___x_245_ = v___x_230_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_snd_228_);
v___x_245_ = v_reuseFailAlloc_249_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_245_);
lean_ctor_set(v___x_223_, 0, v___x_243_);
v___x_247_ = v___x_223_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
if (v___y_235_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_252_; 
lean_dec_ref(v_c_211_);
v___x_250_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_231_ == 0)
{
v___x_252_ = v___x_230_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_snd_228_);
v___x_252_ = v_reuseFailAlloc_256_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_252_);
lean_ctor_set(v___x_223_, 0, v___x_250_);
v___x_254_ = v___x_223_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
else
{
lean_object* v___x_258_; 
if (v_isShared_231_ == 0)
{
v___x_258_ = v___x_230_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_snd_228_);
v___x_258_ = v_reuseFailAlloc_262_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_258_);
lean_ctor_set(v___x_223_, 0, v___x_233_);
v___x_260_ = v___x_223_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
v_a_216_ = v___x_260_;
goto v___jp_215_;
}
}
}
}
}
v___jp_267_:
{
if (v___x_266_ == 0)
{
if (v___y_268_ == 0)
{
v___y_235_ = v___y_269_;
v___y_236_ = v___x_263_;
goto v___jp_234_;
}
else
{
v___y_235_ = v___y_269_;
v___y_236_ = v___x_266_;
goto v___jp_234_;
}
}
else
{
v___y_235_ = v___y_269_;
v___y_236_ = v___y_268_;
goto v___jp_234_;
}
}
v___jp_270_:
{
if (lean_obj_tag(v_snd_228_) == 0)
{
uint8_t v___x_272_; 
v___x_272_ = 0;
v___y_268_ = v_val_271_;
v___y_269_ = v___x_272_;
goto v___jp_267_;
}
else
{
lean_object* v_val_273_; uint8_t v___x_274_; 
v_val_273_ = lean_ctor_get(v_snd_228_, 0);
v___x_274_ = lean_nat_dec_eq(v_val_273_, v___x_232_);
v___y_268_ = v_val_271_;
v___y_269_ = v___x_274_;
goto v___jp_267_;
}
}
}
}
}
v___jp_215_:
{
size_t v___x_217_; size_t v___x_218_; 
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_add(v_i_213_, v___x_217_);
v_i_213_ = v___x_218_;
v_b_214_ = v_a_216_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___boxed(lean_object* v___x_303_, lean_object* v___x_304_, lean_object* v_c_305_, lean_object* v_sz_306_, lean_object* v_i_307_, lean_object* v_b_308_){
_start:
{
size_t v_sz_boxed_309_; size_t v_i_boxed_310_; lean_object* v_res_311_; 
v_sz_boxed_309_ = lean_unbox_usize(v_sz_306_);
lean_dec(v_sz_306_);
v_i_boxed_310_ = lean_unbox_usize(v_i_307_);
lean_dec(v_i_307_);
v_res_311_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(v___x_303_, v___x_304_, v_c_305_, v_sz_boxed_309_, v_i_boxed_310_, v_b_308_);
lean_dec(v___x_304_);
lean_dec(v___x_303_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(lean_object* v_s_314_, lean_object* v_as_315_, size_t v_sz_316_, size_t v_i_317_, lean_object* v_b_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = lean_usize_dec_lt(v_i_317_, v_sz_316_);
if (v___x_319_ == 0)
{
return v_b_318_;
}
else
{
lean_object* v_snd_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_377_; 
v_snd_320_ = lean_ctor_get(v_b_318_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v_b_318_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v_b_318_, 0);
lean_dec(v_unused_378_);
v___x_322_ = v_b_318_;
v_isShared_323_ = v_isSharedCheck_377_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_snd_320_);
lean_dec(v_b_318_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_377_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_a_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_a_329_ = lean_array_uget_borrowed(v_as_315_, v_i_317_);
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_sub(v_a_329_, v___x_330_);
v___x_332_ = lean_array_get_size(v_s_314_);
v___x_333_ = lean_nat_dec_lt(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_dec(v___x_331_);
goto v___jp_324_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = lean_array_fget_borrowed(v_s_314_, v___x_331_);
if (lean_obj_tag(v___x_334_) == 1)
{
lean_object* v_val_335_; lean_object* v_atoms_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; size_t v_sz_340_; size_t v___x_341_; lean_object* v___x_342_; lean_object* v_snd_343_; lean_object* v_fst_344_; 
lean_del_object(v___x_322_);
v_val_335_ = lean_ctor_get(v___x_334_, 0);
v_atoms_336_ = lean_ctor_get(v_val_335_, 0);
v___x_337_ = lean_box(0);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v_snd_320_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v_sz_340_ = lean_array_size(v_atoms_336_);
v___x_341_ = ((size_t)0ULL);
lean_inc(v_val_335_);
v___x_342_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(v___x_331_, v___x_332_, v_val_335_, v_sz_340_, v___x_341_, v___x_339_);
lean_dec(v___x_331_);
v_snd_343_ = lean_ctor_get(v___x_342_, 1);
lean_inc(v_snd_343_);
v_fst_344_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_fst_344_);
lean_dec_ref(v___x_342_);
if (lean_obj_tag(v_fst_344_) == 0)
{
lean_object* v_snd_345_; 
v_snd_345_ = lean_ctor_get(v_snd_343_, 1);
if (lean_obj_tag(v_snd_345_) == 0)
{
lean_object* v_fst_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_354_; 
v_fst_346_ = lean_ctor_get(v_snd_343_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v_snd_343_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v_snd_343_, 1);
lean_dec(v_unused_355_);
v___x_348_ = v_snd_343_;
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_fst_346_);
lean_dec(v_snd_343_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___closed__0));
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v_fst_346_);
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_fst_346_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v_fst_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_366_; 
v_fst_356_ = lean_ctor_get(v_snd_343_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_snd_343_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v_snd_343_, 1);
lean_dec(v_unused_367_);
v___x_358_ = v_snd_343_;
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_fst_356_);
lean_dec(v_snd_343_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v_fst_356_);
lean_ctor_set(v___x_358_, 0, v___x_337_);
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_fst_356_);
v___x_361_ = v_reuseFailAlloc_365_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
size_t v___x_362_; size_t v___x_363_; 
v___x_362_ = ((size_t)1ULL);
v___x_363_ = lean_usize_add(v_i_317_, v___x_362_);
v_i_317_ = v___x_363_;
v_b_318_ = v___x_361_;
goto _start;
}
}
}
}
else
{
lean_object* v_fst_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
v_fst_368_ = lean_ctor_get(v_snd_343_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v_snd_343_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v_snd_343_, 1);
lean_dec(v_unused_376_);
v___x_370_ = v_snd_343_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_fst_368_);
lean_dec(v_snd_343_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 1, v_fst_368_);
lean_ctor_set(v___x_370_, 0, v_fst_344_);
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_fst_344_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_fst_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_dec(v___x_331_);
goto v___jp_324_;
}
}
v___jp_324_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_325_);
v___x_327_ = v___x_322_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_snd_320_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___boxed(lean_object* v_s_379_, lean_object* v_as_380_, lean_object* v_sz_381_, lean_object* v_i_382_, lean_object* v_b_383_){
_start:
{
size_t v_sz_boxed_384_; size_t v_i_boxed_385_; lean_object* v_res_386_; 
v_sz_boxed_384_ = lean_unbox_usize(v_sz_381_);
lean_dec(v_sz_381_);
v_i_boxed_385_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(v_s_379_, v_as_380_, v_sz_boxed_384_, v_i_boxed_385_, v_b_383_);
lean_dec_ref(v_as_380_);
lean_dec_ref(v_s_379_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(lean_object* v_s_387_, lean_object* v_assign_388_, lean_object* v_hints_389_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; size_t v_sz_392_; size_t v___x_393_; lean_object* v___x_394_; lean_object* v_fst_395_; 
v___x_390_ = lean_box(0);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v_assign_388_);
v_sz_392_ = lean_array_size(v_hints_389_);
v___x_393_ = ((size_t)0ULL);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(v_s_387_, v_hints_389_, v_sz_392_, v___x_393_, v___x_391_);
v_fst_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_fst_395_);
if (lean_obj_tag(v_fst_395_) == 0)
{
lean_object* v_snd_396_; lean_object* v___x_397_; 
v_snd_396_ = lean_ctor_get(v___x_394_, 1);
lean_inc(v_snd_396_);
lean_dec_ref(v___x_394_);
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v_snd_396_);
return v___x_397_;
}
else
{
lean_object* v_val_398_; 
lean_dec_ref(v___x_394_);
v_val_398_ = lean_ctor_get(v_fst_395_, 0);
lean_inc(v_val_398_);
lean_dec_ref_known(v_fst_395_, 1);
return v_val_398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints___boxed(lean_object* v_s_399_, lean_object* v_assign_400_, lean_object* v_hints_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(v_s_399_, v_assign_400_, v_hints_401_);
lean_dec_ref(v_hints_401_);
lean_dec_ref(v_s_399_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0(lean_object* v_00_u03b2_403_, lean_object* v_m_404_, lean_object* v_a_405_, lean_object* v_fallback_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(v_m_404_, v_a_405_, v_fallback_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___boxed(lean_object* v_00_u03b2_408_, lean_object* v_m_409_, lean_object* v_a_410_, lean_object* v_fallback_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0(v_00_u03b2_408_, v_m_409_, v_a_410_, v_fallback_411_);
lean_dec(v_fallback_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_m_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1(lean_object* v_00_u03b2_413_, lean_object* v_m_414_, lean_object* v_a_415_, lean_object* v_b_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(v_m_414_, v_a_415_, v_b_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0(lean_object* v_00_u03b2_418_, lean_object* v_a_419_, lean_object* v_fallback_420_, lean_object* v_x_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg(v_a_419_, v_fallback_420_, v_x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___boxed(lean_object* v_00_u03b2_423_, lean_object* v_a_424_, lean_object* v_fallback_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0(v_00_u03b2_423_, v_a_424_, v_fallback_425_, v_x_426_);
lean_dec(v_x_426_);
lean_dec(v_fallback_425_);
lean_dec(v_a_424_);
return v_res_427_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2(lean_object* v_00_u03b2_428_, lean_object* v_a_429_, lean_object* v_x_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(v_a_429_, v_x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___boxed(lean_object* v_00_u03b2_432_, lean_object* v_a_433_, lean_object* v_x_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2(v_00_u03b2_432_, v_a_433_, v_x_434_);
lean_dec(v_x_434_);
lean_dec(v_a_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3(lean_object* v_00_u03b2_437_, lean_object* v_data_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3___redArg(v_data_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4(lean_object* v_00_u03b2_440_, lean_object* v_a_441_, lean_object* v_b_442_, lean_object* v_x_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(v_a_441_, v_b_442_, v_x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_445_, lean_object* v_i_446_, lean_object* v_source_447_, lean_object* v_target_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4___redArg(v_i_446_, v_source_447_, v_target_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7___redArg(v_x_451_, v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(lean_object* v_s_454_, lean_object* v_assign_455_, lean_object* v_rupHints_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(v_s_454_, v_assign_455_, v_rupHints_456_);
if (lean_obj_tag(v___x_457_) == 0)
{
uint8_t v___x_458_; 
v___x_458_ = 1;
return v___x_458_;
}
else
{
uint8_t v___x_459_; 
lean_dec(v___x_457_);
v___x_459_ = 0;
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate___boxed(lean_object* v_s_460_, lean_object* v_assign_461_, lean_object* v_rupHints_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_460_, v_assign_461_, v_rupHints_462_);
lean_dec_ref(v_rupHints_462_);
lean_dec_ref(v_s_460_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(lean_object* v_s_465_, lean_object* v_clause_466_, lean_object* v_rupHints_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(v_clause_466_);
if (lean_obj_tag(v___x_468_) == 1)
{
lean_object* v_val_469_; uint8_t v___x_470_; 
v_val_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_465_, v_val_469_, v_rupHints_467_);
return v___x_470_;
}
else
{
uint8_t v___x_471_; 
lean_dec(v___x_468_);
v___x_471_ = 1;
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup___boxed(lean_object* v_s_472_, lean_object* v_clause_473_, lean_object* v_rupHints_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(v_s_472_, v_clause_473_, v_rupHints_474_);
lean_dec_ref(v_rupHints_474_);
lean_dec_ref(v_clause_473_);
lean_dec_ref(v_s_472_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__7_splitter___redArg(lean_object* v_x_477_, lean_object* v_h__1_478_, lean_object* v_h__2_479_){
_start:
{
if (lean_obj_tag(v_x_477_) == 1)
{
lean_object* v_val_480_; lean_object* v___x_481_; 
lean_dec(v_h__2_479_);
v_val_480_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_val_480_);
lean_dec_ref_known(v_x_477_, 1);
v___x_481_ = lean_apply_1(v_h__1_478_, v_val_480_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; 
lean_dec(v_h__1_478_);
v___x_482_ = lean_apply_2(v_h__2_479_, v_x_477_, lean_box(0));
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__7_splitter(lean_object* v_motive_483_, lean_object* v_x_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_){
_start:
{
if (lean_obj_tag(v_x_484_) == 1)
{
lean_object* v_val_487_; lean_object* v___x_488_; 
lean_dec(v_h__2_486_);
v_val_487_ = lean_ctor_get(v_x_484_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v_x_484_, 1);
v___x_488_ = lean_apply_1(v_h__1_485_, v_val_487_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; 
lean_dec(v_h__1_485_);
v___x_489_ = lean_apply_2(v_h__2_486_, v_x_484_, lean_box(0));
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter___redArg(lean_object* v_x_490_, lean_object* v_h__1_491_, lean_object* v_h__2_492_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v_h__1_491_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_apply_1(v_h__2_492_, v___x_493_);
return v___x_494_;
}
else
{
lean_object* v_val_495_; lean_object* v___x_496_; 
lean_dec(v_h__2_492_);
v_val_495_ = lean_ctor_get(v_x_490_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v_x_490_, 1);
v___x_496_ = lean_apply_1(v_h__1_491_, v_val_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter(lean_object* v_motive_497_, lean_object* v_x_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec(v_h__1_499_);
v___x_501_ = lean_box(0);
v___x_502_ = lean_apply_1(v_h__2_500_, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_504_; 
lean_dec(v_h__2_500_);
v_val_503_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_x_498_, 1);
v___x_504_ = lean_apply_1(v_h__1_499_, v_val_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter___redArg(lean_object* v_unit_505_, lean_object* v_h__1_506_, lean_object* v_h__2_507_){
_start:
{
if (lean_obj_tag(v_unit_505_) == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_h__2_507_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_apply_1(v_h__1_506_, v___x_508_);
return v___x_509_;
}
else
{
lean_object* v_val_510_; lean_object* v___x_511_; 
lean_dec(v_h__1_506_);
v_val_510_ = lean_ctor_get(v_unit_505_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v_unit_505_, 1);
v___x_511_ = lean_apply_1(v_h__2_507_, v_val_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter(lean_object* v_motive_512_, lean_object* v_unit_513_, lean_object* v_h__1_514_, lean_object* v_h__2_515_){
_start:
{
if (lean_obj_tag(v_unit_513_) == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v_h__2_515_);
v___x_516_ = lean_box(0);
v___x_517_ = lean_apply_1(v_h__1_514_, v___x_516_);
return v___x_517_;
}
else
{
lean_object* v_val_518_; lean_object* v___x_519_; 
lean_dec(v_h__1_514_);
v_val_518_ = lean_ctor_get(v_unit_513_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v_unit_513_, 1);
v___x_519_ = lean_apply_1(v_h__2_515_, v_val_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_520_, lean_object* v_h__1_521_, lean_object* v_h__2_522_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec(v_h__1_521_);
v___x_523_ = lean_box(0);
v___x_524_ = lean_apply_1(v_h__2_522_, v___x_523_);
return v___x_524_;
}
else
{
lean_object* v_val_525_; lean_object* v___x_526_; 
lean_dec(v_h__2_522_);
v_val_525_ = lean_ctor_get(v_x_520_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v_x_520_, 1);
v___x_526_ = lean_apply_1(v_h__1_521_, v_val_525_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_527_, lean_object* v_motive_528_, lean_object* v_x_529_, lean_object* v_h__1_530_, lean_object* v_h__2_531_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v_h__1_530_);
v___x_532_ = lean_box(0);
v___x_533_ = lean_apply_1(v_h__2_531_, v___x_532_);
return v___x_533_;
}
else
{
lean_object* v_val_534_; lean_object* v___x_535_; 
lean_dec(v_h__2_531_);
v_val_534_ = lean_ctor_get(v_x_529_, 0);
lean_inc(v_val_534_);
lean_dec_ref_known(v_x_529_, 1);
v___x_535_ = lean_apply_1(v_h__1_530_, v_val_534_);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__28_splitter___redArg(lean_object* v_ret_536_, lean_object* v_h__1_537_, lean_object* v_h__2_538_, lean_object* v_h__3_539_){
_start:
{
switch(lean_obj_tag(v_ret_536_))
{
case 0:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec(v_h__3_539_);
lean_dec(v_h__1_537_);
v___x_540_ = lean_box(0);
v___x_541_ = lean_apply_1(v_h__2_538_, v___x_540_);
return v___x_541_;
}
case 1:
{
lean_object* v_assign_542_; lean_object* v___x_543_; 
lean_dec(v_h__2_538_);
lean_dec(v_h__1_537_);
v_assign_542_ = lean_ctor_get(v_ret_536_, 0);
lean_inc_ref(v_assign_542_);
lean_dec_ref_known(v_ret_536_, 1);
v___x_543_ = lean_apply_1(v_h__3_539_, v_assign_542_);
return v___x_543_;
}
default: 
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_h__3_539_);
lean_dec(v_h__2_538_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_apply_1(v_h__1_537_, v___x_544_);
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__28_splitter(lean_object* v_motive_546_, lean_object* v_ret_547_, lean_object* v_h__1_548_, lean_object* v_h__2_549_, lean_object* v_h__3_550_){
_start:
{
switch(lean_obj_tag(v_ret_547_))
{
case 0:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
lean_dec(v_h__3_550_);
lean_dec(v_h__1_548_);
v___x_551_ = lean_box(0);
v___x_552_ = lean_apply_1(v_h__2_549_, v___x_551_);
return v___x_552_;
}
case 1:
{
lean_object* v_assign_553_; lean_object* v___x_554_; 
lean_dec(v_h__2_549_);
lean_dec(v_h__1_548_);
v_assign_553_ = lean_ctor_get(v_ret_547_, 0);
lean_inc_ref(v_assign_553_);
lean_dec_ref_known(v_ret_547_, 1);
v___x_554_ = lean_apply_1(v_h__3_550_, v_assign_553_);
return v___x_554_;
}
default: 
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v_h__3_550_);
lean_dec(v_h__2_549_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_apply_1(v_h__1_548_, v___x_555_);
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__10_splitter___redArg(lean_object* v_unit_557_, lean_object* v_h__1_558_, lean_object* v_h__2_559_){
_start:
{
if (lean_obj_tag(v_unit_557_) == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_h__1_558_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_apply_1(v_h__2_559_, v___x_560_);
return v___x_561_;
}
else
{
lean_object* v_val_562_; lean_object* v___x_563_; 
lean_dec(v_h__2_559_);
v_val_562_ = lean_ctor_get(v_unit_557_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v_unit_557_, 1);
v___x_563_ = lean_apply_1(v_h__1_558_, v_val_562_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__10_splitter(lean_object* v_motive_564_, lean_object* v_unit_565_, lean_object* v_h__1_566_, lean_object* v_h__2_567_){
_start:
{
if (lean_obj_tag(v_unit_565_) == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v_h__1_566_);
v___x_568_ = lean_box(0);
v___x_569_ = lean_apply_1(v_h__2_567_, v___x_568_);
return v___x_569_;
}
else
{
lean_object* v_val_570_; lean_object* v___x_571_; 
lean_dec(v_h__2_567_);
v_val_570_ = lean_ctor_get(v_unit_565_, 0);
lean_inc(v_val_570_);
lean_dec_ref_known(v_unit_565_, 1);
v___x_571_ = lean_apply_1(v_h__1_566_, v_val_570_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter___redArg(lean_object* v_x_572_, lean_object* v_h__1_573_, lean_object* v_h__2_574_, lean_object* v_h__3_575_){
_start:
{
switch(lean_obj_tag(v_x_572_))
{
case 0:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_h__3_575_);
lean_dec(v_h__2_574_);
v___x_576_ = lean_box(0);
v___x_577_ = lean_apply_1(v_h__1_573_, v___x_576_);
return v___x_577_;
}
case 1:
{
lean_object* v_assign_578_; lean_object* v___x_579_; 
lean_dec(v_h__3_575_);
lean_dec(v_h__1_573_);
v_assign_578_ = lean_ctor_get(v_x_572_, 0);
lean_inc_ref(v_assign_578_);
lean_dec_ref_known(v_x_572_, 1);
v___x_579_ = lean_apply_1(v_h__2_574_, v_assign_578_);
return v___x_579_;
}
default: 
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_h__2_574_);
lean_dec(v_h__1_573_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_apply_1(v_h__3_575_, v___x_580_);
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter(lean_object* v_motive_582_, lean_object* v_x_583_, lean_object* v_h__1_584_, lean_object* v_h__2_585_, lean_object* v_h__3_586_){
_start:
{
switch(lean_obj_tag(v_x_583_))
{
case 0:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_h__3_586_);
lean_dec(v_h__2_585_);
v___x_587_ = lean_box(0);
v___x_588_ = lean_apply_1(v_h__1_584_, v___x_587_);
return v___x_588_;
}
case 1:
{
lean_object* v_assign_589_; lean_object* v___x_590_; 
lean_dec(v_h__3_586_);
lean_dec(v_h__1_584_);
v_assign_589_ = lean_ctor_get(v_x_583_, 0);
lean_inc_ref(v_assign_589_);
lean_dec_ref_known(v_x_583_, 1);
v___x_590_ = lean_apply_1(v_h__2_585_, v_assign_589_);
return v___x_590_;
}
default: 
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec(v_h__2_585_);
lean_dec(v_h__1_584_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_apply_1(v_h__3_586_, v___x_591_);
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter___redArg(lean_object* v_x_593_, lean_object* v_h__1_594_, lean_object* v_h__2_595_){
_start:
{
if (lean_obj_tag(v_x_593_) == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v_h__2_595_);
v___x_596_ = lean_box(0);
v___x_597_ = lean_apply_1(v_h__1_594_, v___x_596_);
return v___x_597_;
}
else
{
lean_object* v___x_598_; 
lean_dec(v_h__1_594_);
v___x_598_ = lean_apply_2(v_h__2_595_, v_x_593_, lean_box(0));
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter(lean_object* v_motive_599_, lean_object* v_x_600_, lean_object* v_h__1_601_, lean_object* v_h__2_602_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v_h__2_602_);
v___x_603_ = lean_box(0);
v___x_604_ = lean_apply_1(v_h__1_601_, v___x_603_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; 
lean_dec(v_h__1_601_);
v___x_605_ = lean_apply_2(v_h__2_602_, v_x_600_, lean_box(0));
return v___x_605_;
}
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_SpecLemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_SpecLemmas(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(builtin);
}
#ifdef __cplusplus
}
#endif
