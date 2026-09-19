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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_byte_array_uget(lean_object*, size_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__9_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__9_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__30_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__30_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_nbuckets_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_123_ = lean_array_get_size(v_data_122_);
v___x_124_ = lean_unsigned_to_nat(2u);
v_nbuckets_125_ = lean_nat_mul(v___x_123_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_box(0);
v___x_128_ = lean_mk_array(v_nbuckets_125_, v___x_127_);
v___x_129_ = lean_array_propagate_mark(v_data_122_, v___x_128_);
v___x_130_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4___redArg(v___x_126_, v_data_122_, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(lean_object* v_a_131_, lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
else
{
lean_object* v_key_134_; lean_object* v_tail_135_; uint8_t v___x_136_; 
v_key_134_ = lean_ctor_get(v_x_132_, 0);
v_tail_135_ = lean_ctor_get(v_x_132_, 2);
v___x_136_ = lean_nat_dec_eq(v_key_134_, v_a_131_);
if (v___x_136_ == 0)
{
v_x_132_ = v_tail_135_;
goto _start;
}
else
{
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg___boxed(lean_object* v_a_138_, lean_object* v_x_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(v_a_138_, v_x_139_);
lean_dec(v_x_139_);
lean_dec(v_a_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(lean_object* v_a_142_, lean_object* v_b_143_, lean_object* v_x_144_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_dec(v_b_143_);
lean_dec(v_a_142_);
return v_x_144_;
}
else
{
lean_object* v_key_145_; lean_object* v_value_146_; lean_object* v_tail_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_159_; 
v_key_145_ = lean_ctor_get(v_x_144_, 0);
v_value_146_ = lean_ctor_get(v_x_144_, 1);
v_tail_147_ = lean_ctor_get(v_x_144_, 2);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_144_);
if (v_isSharedCheck_159_ == 0)
{
v___x_149_ = v_x_144_;
v_isShared_150_ = v_isSharedCheck_159_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_tail_147_);
lean_inc(v_value_146_);
lean_inc(v_key_145_);
lean_dec(v_x_144_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_159_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_eq(v_key_145_, v_a_142_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(v_a_142_, v_b_143_, v_tail_147_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 2, v___x_152_);
v___x_154_ = v___x_149_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_key_145_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_value_146_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
else
{
lean_object* v___x_157_; 
lean_dec(v_value_146_);
lean_dec(v_key_145_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v_b_143_);
lean_ctor_set(v___x_149_, 0, v_a_142_);
v___x_157_ = v___x_149_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_142_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_b_143_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_tail_147_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(lean_object* v_m_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v_size_163_; lean_object* v_buckets_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_207_; 
v_size_163_ = lean_ctor_get(v_m_160_, 0);
v_buckets_164_ = lean_ctor_get(v_m_160_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_m_160_);
if (v_isSharedCheck_207_ == 0)
{
v___x_166_ = v_m_160_;
v_isShared_167_ = v_isSharedCheck_207_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_buckets_164_);
lean_inc(v_size_163_);
lean_dec(v_m_160_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_207_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; uint64_t v_fold_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v___x_180_; lean_object* v_bkt_181_; uint8_t v___x_182_; 
v___x_168_ = lean_array_get_size(v_buckets_164_);
v___x_169_ = lean_uint64_of_nat(v_a_161_);
v___x_170_ = 32ULL;
v___x_171_ = lean_uint64_shift_right(v___x_169_, v___x_170_);
v_fold_172_ = lean_uint64_xor(v___x_169_, v___x_171_);
v___x_173_ = 16ULL;
v___x_174_ = lean_uint64_shift_right(v_fold_172_, v___x_173_);
v___x_175_ = lean_uint64_xor(v_fold_172_, v___x_174_);
v___x_176_ = lean_uint64_to_usize(v___x_175_);
v___x_177_ = lean_usize_of_nat(v___x_168_);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_sub(v___x_177_, v___x_178_);
v___x_180_ = lean_usize_land(v___x_176_, v___x_179_);
v_bkt_181_ = lean_array_uget_borrowed(v_buckets_164_, v___x_180_);
v___x_182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(v_a_161_, v_bkt_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v_size_x27_184_; lean_object* v___x_185_; lean_object* v_buckets_x27_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v_size_x27_184_ = lean_nat_add(v_size_163_, v___x_183_);
lean_dec(v_size_163_);
lean_inc(v_bkt_181_);
v___x_185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_185_, 0, v_a_161_);
lean_ctor_set(v___x_185_, 1, v_b_162_);
lean_ctor_set(v___x_185_, 2, v_bkt_181_);
v_buckets_x27_186_ = lean_array_uset(v_buckets_164_, v___x_180_, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(4u);
v___x_188_ = lean_nat_mul(v_size_x27_184_, v___x_187_);
v___x_189_ = lean_unsigned_to_nat(3u);
v___x_190_ = lean_nat_div(v___x_188_, v___x_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_array_get_size(v_buckets_x27_186_);
v___x_192_ = lean_nat_dec_le(v___x_190_, v___x_191_);
lean_dec(v___x_190_);
if (v___x_192_ == 0)
{
lean_object* v_val_193_; lean_object* v___x_195_; 
v_val_193_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3___redArg(v_buckets_x27_186_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_val_193_);
lean_ctor_set(v___x_166_, 0, v_size_x27_184_);
v___x_195_ = v___x_166_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_size_x27_184_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_val_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
else
{
lean_object* v___x_198_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_buckets_x27_186_);
lean_ctor_set(v___x_166_, 0, v_size_x27_184_);
v___x_198_ = v___x_166_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_size_x27_184_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_buckets_x27_186_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
else
{
lean_object* v___x_200_; lean_object* v_buckets_x27_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
lean_inc(v_bkt_181_);
v___x_200_ = lean_box(0);
v_buckets_x27_201_ = lean_array_uset(v_buckets_164_, v___x_180_, v___x_200_);
v___x_202_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(v_a_161_, v_b_162_, v_bkt_181_);
v___x_203_ = lean_array_uset(v_buckets_x27_201_, v___x_180_, v___x_202_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_203_);
v___x_205_ = v___x_166_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_size_163_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(lean_object* v___x_210_, lean_object* v___x_211_, lean_object* v_c_212_, size_t v_sz_213_, size_t v_i_214_, lean_object* v_b_215_){
_start:
{
lean_object* v_a_217_; uint8_t v___x_221_; 
v___x_221_ = lean_usize_dec_lt(v_i_214_, v_sz_213_);
if (v___x_221_ == 0)
{
lean_dec_ref(v_c_212_);
return v_b_215_;
}
else
{
lean_object* v_snd_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_307_; 
v_snd_222_ = lean_ctor_get(v_b_215_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_b_215_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v_b_215_, 0);
lean_dec(v_unused_308_);
v___x_224_ = v_b_215_;
v_isShared_225_ = v_isSharedCheck_307_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_snd_222_);
lean_dec(v_b_215_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_307_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v_atoms_226_; lean_object* v_polarities_227_; lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_306_; 
v_atoms_226_ = lean_ctor_get(v_c_212_, 0);
v_polarities_227_ = lean_ctor_get(v_c_212_, 1);
v_fst_228_ = lean_ctor_get(v_snd_222_, 0);
v_snd_229_ = lean_ctor_get(v_snd_222_, 1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_snd_222_);
if (v_isSharedCheck_306_ == 0)
{
v___x_231_ = v_snd_222_;
v_isShared_232_ = v_isSharedCheck_306_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_snd_229_);
lean_inc(v_fst_228_);
lean_dec(v_snd_222_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_306_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___y_243_; uint8_t v___x_275_; uint8_t v___x_276_; uint8_t v___x_277_; uint8_t v___x_278_; uint8_t v_val_280_; uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_233_ = lean_array_uget_borrowed(v_atoms_226_, v_i_214_);
v___x_234_ = lean_box(0);
v___x_275_ = lean_nat_dec_lt(v___x_210_, v___x_211_);
v___x_276_ = lean_byte_array_uget(v_polarities_227_, v_i_214_);
v___x_277_ = 1;
v___x_278_ = lean_uint8_dec_eq(v___x_276_, v___x_277_);
v___x_281_ = 0;
v___x_282_ = lean_box(v___x_281_);
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(v_fst_228_, v___x_233_, v___x_282_);
lean_dec(v___x_282_);
v___x_284_ = lean_unbox(v___x_283_);
lean_dec(v___x_283_);
switch(v___x_284_)
{
case 0:
{
lean_del_object(v___x_231_);
lean_del_object(v___x_224_);
if (lean_obj_tag(v_snd_229_) == 0)
{
lean_object* v___x_285_; uint8_t v___y_287_; 
lean_inc(v___x_233_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_233_);
if (v___x_278_ == 0)
{
uint8_t v___x_292_; 
v___x_292_ = 2;
v___y_287_ = v___x_292_;
goto v___jp_286_;
}
else
{
uint8_t v___x_293_; 
v___x_293_ = 1;
v___y_287_ = v___x_293_;
goto v___jp_286_;
}
v___jp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_288_ = lean_box(v___y_287_);
lean_inc(v___x_233_);
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(v_fst_228_, v___x_233_, v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_285_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_234_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v_a_217_ = v___x_291_;
goto v___jp_216_;
}
}
else
{
lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_302_; 
v_isSharedCheck_302_ = !lean_is_exclusive(v_c_212_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; lean_object* v_unused_304_; 
v_unused_303_ = lean_ctor_get(v_c_212_, 1);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_c_212_, 0);
lean_dec(v_unused_304_);
v___x_295_ = v_c_212_;
v_isShared_296_ = v_isSharedCheck_302_;
goto v_resetjp_294_;
}
else
{
lean_dec(v_c_212_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_302_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v_snd_229_);
lean_ctor_set(v___x_295_, 0, v_fst_228_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_fst_228_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_snd_229_);
v___x_299_ = v_reuseFailAlloc_301_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; 
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_297_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
return v___x_300_;
}
}
}
}
case 1:
{
v_val_280_ = v___x_275_;
goto v___jp_279_;
}
default: 
{
uint8_t v___x_305_; 
v___x_305_ = 0;
v_val_280_ = v___x_305_;
goto v___jp_279_;
}
}
v___jp_235_:
{
lean_object* v___x_237_; 
if (v_isShared_232_ == 0)
{
v___x_237_ = v___x_231_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_fst_228_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_snd_229_);
v___x_237_ = v_reuseFailAlloc_241_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_239_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v___x_237_);
lean_ctor_set(v___x_224_, 0, v___x_234_);
v___x_239_ = v___x_224_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
v_a_217_ = v___x_239_;
goto v___jp_216_;
}
}
}
v___jp_242_:
{
if (v___y_243_ == 0)
{
if (lean_obj_tag(v_snd_229_) == 0)
{
goto v___jp_235_;
}
else
{
lean_object* v_val_244_; uint8_t v___x_245_; 
v_val_244_ = lean_ctor_get(v_snd_229_, 0);
v___x_245_ = lean_nat_dec_eq(v_val_244_, v___x_233_);
if (v___x_245_ == 0)
{
goto v___jp_235_;
}
else
{
lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_254_; 
lean_del_object(v___x_231_);
lean_del_object(v___x_224_);
v_isSharedCheck_254_ = !lean_is_exclusive(v_c_212_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; lean_object* v_unused_256_; 
v_unused_255_ = lean_ctor_get(v_c_212_, 1);
lean_dec(v_unused_255_);
v_unused_256_ = lean_ctor_get(v_c_212_, 0);
lean_dec(v_unused_256_);
v___x_247_ = v_c_212_;
v_isShared_248_ = v_isSharedCheck_254_;
goto v_resetjp_246_;
}
else
{
lean_dec(v_c_212_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_254_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v_snd_229_);
lean_ctor_set(v___x_247_, 0, v_fst_228_);
v___x_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_fst_228_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_snd_229_);
v___x_251_ = v_reuseFailAlloc_253_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_249_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
return v___x_252_;
}
}
}
}
}
else
{
lean_del_object(v___x_231_);
lean_del_object(v___x_224_);
if (lean_obj_tag(v_snd_229_) == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
lean_inc(v___x_233_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_233_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_fst_228_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_234_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v_a_217_ = v___x_259_;
goto v___jp_216_;
}
else
{
lean_object* v_val_260_; uint8_t v___x_261_; 
v_val_260_ = lean_ctor_get(v_snd_229_, 0);
v___x_261_ = lean_nat_dec_eq(v_val_260_, v___x_233_);
if (v___x_261_ == 0)
{
lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_270_; 
v_isSharedCheck_270_ = !lean_is_exclusive(v_c_212_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; lean_object* v_unused_272_; 
v_unused_271_ = lean_ctor_get(v_c_212_, 1);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_c_212_, 0);
lean_dec(v_unused_272_);
v___x_263_ = v_c_212_;
v_isShared_264_ = v_isSharedCheck_270_;
goto v_resetjp_262_;
}
else
{
lean_dec(v_c_212_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_270_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v_snd_229_);
lean_ctor_set(v___x_263_, 0, v_fst_228_);
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_fst_228_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_snd_229_);
v___x_267_ = v_reuseFailAlloc_269_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_265_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
return v___x_268_;
}
}
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_fst_228_);
lean_ctor_set(v___x_273_, 1, v_snd_229_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_234_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v_a_217_ = v___x_274_;
goto v___jp_216_;
}
}
}
}
v___jp_279_:
{
if (v___x_278_ == 0)
{
if (v_val_280_ == 0)
{
v___y_243_ = v___x_275_;
goto v___jp_242_;
}
else
{
v___y_243_ = v___x_278_;
goto v___jp_242_;
}
}
else
{
v___y_243_ = v_val_280_;
goto v___jp_242_;
}
}
}
}
}
v___jp_216_:
{
size_t v___x_218_; size_t v___x_219_; 
v___x_218_ = ((size_t)1ULL);
v___x_219_ = lean_usize_add(v_i_214_, v___x_218_);
v_i_214_ = v___x_219_;
v_b_215_ = v_a_217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___boxed(lean_object* v___x_309_, lean_object* v___x_310_, lean_object* v_c_311_, lean_object* v_sz_312_, lean_object* v_i_313_, lean_object* v_b_314_){
_start:
{
size_t v_sz_boxed_315_; size_t v_i_boxed_316_; lean_object* v_res_317_; 
v_sz_boxed_315_ = lean_unbox_usize(v_sz_312_);
lean_dec(v_sz_312_);
v_i_boxed_316_ = lean_unbox_usize(v_i_313_);
lean_dec(v_i_313_);
v_res_317_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(v___x_309_, v___x_310_, v_c_311_, v_sz_boxed_315_, v_i_boxed_316_, v_b_314_);
lean_dec(v___x_310_);
lean_dec(v___x_309_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(lean_object* v_s_320_, lean_object* v_as_321_, size_t v_sz_322_, size_t v_i_323_, lean_object* v_b_324_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_usize_dec_lt(v_i_323_, v_sz_322_);
if (v___x_325_ == 0)
{
return v_b_324_;
}
else
{
lean_object* v_snd_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_383_; 
v_snd_326_ = lean_ctor_get(v_b_324_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_b_324_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_b_324_, 0);
lean_dec(v_unused_384_);
v___x_328_ = v_b_324_;
v_isShared_329_ = v_isSharedCheck_383_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_snd_326_);
lean_dec(v_b_324_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_383_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_a_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_a_335_ = lean_array_uget_borrowed(v_as_321_, v_i_323_);
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_sub(v_a_335_, v___x_336_);
v___x_338_ = lean_array_get_size(v_s_320_);
v___x_339_ = lean_nat_dec_lt(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_dec(v___x_337_);
goto v___jp_330_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = lean_array_fget_borrowed(v_s_320_, v___x_337_);
if (lean_obj_tag(v___x_340_) == 1)
{
lean_object* v_val_341_; lean_object* v_atoms_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; size_t v_sz_346_; size_t v___x_347_; lean_object* v___x_348_; lean_object* v_snd_349_; lean_object* v_fst_350_; 
lean_del_object(v___x_328_);
v_val_341_ = lean_ctor_get(v___x_340_, 0);
v_atoms_342_ = lean_ctor_get(v_val_341_, 0);
v___x_343_ = lean_box(0);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_snd_326_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v_sz_346_ = lean_array_size(v_atoms_342_);
v___x_347_ = ((size_t)0ULL);
lean_inc(v_val_341_);
v___x_348_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(v___x_337_, v___x_338_, v_val_341_, v_sz_346_, v___x_347_, v___x_345_);
lean_dec(v___x_337_);
v_snd_349_ = lean_ctor_get(v___x_348_, 1);
lean_inc(v_snd_349_);
v_fst_350_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_fst_350_);
lean_dec_ref(v___x_348_);
if (lean_obj_tag(v_fst_350_) == 0)
{
lean_object* v_snd_351_; 
v_snd_351_ = lean_ctor_get(v_snd_349_, 1);
if (lean_obj_tag(v_snd_351_) == 0)
{
lean_object* v_fst_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_360_; 
v_fst_352_ = lean_ctor_get(v_snd_349_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v_snd_349_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; 
v_unused_361_ = lean_ctor_get(v_snd_349_, 1);
lean_dec(v_unused_361_);
v___x_354_ = v_snd_349_;
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_fst_352_);
lean_dec(v_snd_349_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___closed__0));
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_fst_352_);
lean_ctor_set(v___x_354_, 0, v___x_356_);
v___x_358_ = v___x_354_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_fst_352_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
else
{
lean_object* v_fst_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_372_; 
v_fst_362_ = lean_ctor_get(v_snd_349_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v_snd_349_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v_snd_349_, 1);
lean_dec(v_unused_373_);
v___x_364_ = v_snd_349_;
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_fst_362_);
lean_dec(v_snd_349_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v_fst_362_);
lean_ctor_set(v___x_364_, 0, v___x_343_);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_fst_362_);
v___x_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
size_t v___x_368_; size_t v___x_369_; 
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_add(v_i_323_, v___x_368_);
v_i_323_ = v___x_369_;
v_b_324_ = v___x_367_;
goto _start;
}
}
}
}
else
{
lean_object* v_fst_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_fst_374_ = lean_ctor_get(v_snd_349_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v_snd_349_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v_snd_349_, 1);
lean_dec(v_unused_382_);
v___x_376_ = v_snd_349_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_fst_374_);
lean_dec(v_snd_349_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 1, v_fst_374_);
lean_ctor_set(v___x_376_, 0, v_fst_350_);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_fst_350_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_fst_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_dec(v___x_337_);
goto v___jp_330_;
}
}
v___jp_330_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_331_);
v___x_333_ = v___x_328_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_snd_326_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___boxed(lean_object* v_s_385_, lean_object* v_as_386_, lean_object* v_sz_387_, lean_object* v_i_388_, lean_object* v_b_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_387_);
lean_dec(v_sz_387_);
v_i_boxed_391_ = lean_unbox_usize(v_i_388_);
lean_dec(v_i_388_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(v_s_385_, v_as_386_, v_sz_boxed_390_, v_i_boxed_391_, v_b_389_);
lean_dec_ref(v_as_386_);
lean_dec_ref(v_s_385_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(lean_object* v_s_393_, lean_object* v_assign_394_, lean_object* v_hints_395_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; size_t v_sz_398_; size_t v___x_399_; lean_object* v___x_400_; lean_object* v_fst_401_; 
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_assign_394_);
v_sz_398_ = lean_array_size(v_hints_395_);
v___x_399_ = ((size_t)0ULL);
v___x_400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(v_s_393_, v_hints_395_, v_sz_398_, v___x_399_, v___x_397_);
v_fst_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_fst_401_);
if (lean_obj_tag(v_fst_401_) == 0)
{
lean_object* v_snd_402_; lean_object* v___x_403_; 
v_snd_402_ = lean_ctor_get(v___x_400_, 1);
lean_inc(v_snd_402_);
lean_dec_ref(v___x_400_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v_snd_402_);
return v___x_403_;
}
else
{
lean_object* v_val_404_; 
lean_dec_ref(v___x_400_);
v_val_404_ = lean_ctor_get(v_fst_401_, 0);
lean_inc(v_val_404_);
lean_dec_ref_known(v_fst_401_, 1);
return v_val_404_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints___boxed(lean_object* v_s_405_, lean_object* v_assign_406_, lean_object* v_hints_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(v_s_405_, v_assign_406_, v_hints_407_);
lean_dec_ref(v_hints_407_);
lean_dec_ref(v_s_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0(lean_object* v_00_u03b2_409_, lean_object* v_m_410_, lean_object* v_a_411_, lean_object* v_fallback_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(v_m_410_, v_a_411_, v_fallback_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___boxed(lean_object* v_00_u03b2_414_, lean_object* v_m_415_, lean_object* v_a_416_, lean_object* v_fallback_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0(v_00_u03b2_414_, v_m_415_, v_a_416_, v_fallback_417_);
lean_dec(v_fallback_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_m_415_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1(lean_object* v_00_u03b2_419_, lean_object* v_m_420_, lean_object* v_a_421_, lean_object* v_b_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(v_m_420_, v_a_421_, v_b_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0(lean_object* v_00_u03b2_424_, lean_object* v_a_425_, lean_object* v_fallback_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg(v_a_425_, v_fallback_426_, v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___boxed(lean_object* v_00_u03b2_429_, lean_object* v_a_430_, lean_object* v_fallback_431_, lean_object* v_x_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0(v_00_u03b2_429_, v_a_430_, v_fallback_431_, v_x_432_);
lean_dec(v_x_432_);
lean_dec(v_fallback_431_);
lean_dec(v_a_430_);
return v_res_433_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2(lean_object* v_00_u03b2_434_, lean_object* v_a_435_, lean_object* v_x_436_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(v_a_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___boxed(lean_object* v_00_u03b2_438_, lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2(v_00_u03b2_438_, v_a_439_, v_x_440_);
lean_dec(v_x_440_);
lean_dec(v_a_439_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3(lean_object* v_00_u03b2_443_, lean_object* v_data_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3___redArg(v_data_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4(lean_object* v_00_u03b2_446_, lean_object* v_a_447_, lean_object* v_b_448_, lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(v_a_447_, v_b_448_, v_x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_451_, lean_object* v_i_452_, lean_object* v_source_453_, lean_object* v_target_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4___redArg(v_i_452_, v_source_453_, v_target_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7___redArg(v_x_457_, v_x_458_);
return v___x_459_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(lean_object* v_s_460_, lean_object* v_assign_461_, lean_object* v_rupHints_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(v_s_460_, v_assign_461_, v_rupHints_462_);
if (lean_obj_tag(v___x_463_) == 0)
{
uint8_t v___x_464_; 
v___x_464_ = 1;
return v___x_464_;
}
else
{
uint8_t v___x_465_; 
lean_dec(v___x_463_);
v___x_465_ = 0;
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate___boxed(lean_object* v_s_466_, lean_object* v_assign_467_, lean_object* v_rupHints_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_466_, v_assign_467_, v_rupHints_468_);
lean_dec_ref(v_rupHints_468_);
lean_dec_ref(v_s_466_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(lean_object* v_s_471_, lean_object* v_clause_472_, lean_object* v_rupHints_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(v_clause_472_);
if (lean_obj_tag(v___x_474_) == 1)
{
lean_object* v_val_475_; uint8_t v___x_476_; 
v_val_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_471_, v_val_475_, v_rupHints_473_);
return v___x_476_;
}
else
{
uint8_t v___x_477_; 
lean_dec(v___x_474_);
v___x_477_ = 1;
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup___boxed(lean_object* v_s_478_, lean_object* v_clause_479_, lean_object* v_rupHints_480_){
_start:
{
uint8_t v_res_481_; lean_object* v_r_482_; 
v_res_481_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(v_s_478_, v_clause_479_, v_rupHints_480_);
lean_dec_ref(v_rupHints_480_);
lean_dec_ref(v_clause_479_);
lean_dec_ref(v_s_478_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__9_splitter___redArg(lean_object* v_x_483_, lean_object* v_h__1_484_, lean_object* v_h__2_485_){
_start:
{
if (lean_obj_tag(v_x_483_) == 1)
{
lean_object* v_val_486_; lean_object* v___x_487_; 
lean_dec(v_h__2_485_);
v_val_486_ = lean_ctor_get(v_x_483_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v_x_483_, 1);
v___x_487_ = lean_apply_1(v_h__1_484_, v_val_486_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; 
lean_dec(v_h__1_484_);
v___x_488_ = lean_apply_2(v_h__2_485_, v_x_483_, lean_box(0));
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__9_splitter(lean_object* v_motive_489_, lean_object* v_x_490_, lean_object* v_h__1_491_, lean_object* v_h__2_492_){
_start:
{
if (lean_obj_tag(v_x_490_) == 1)
{
lean_object* v_val_493_; lean_object* v___x_494_; 
lean_dec(v_h__2_492_);
v_val_493_ = lean_ctor_get(v_x_490_, 0);
lean_inc(v_val_493_);
lean_dec_ref_known(v_x_490_, 1);
v___x_494_ = lean_apply_1(v_h__1_491_, v_val_493_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; 
lean_dec(v_h__1_491_);
v___x_495_ = lean_apply_2(v_h__2_492_, v_x_490_, lean_box(0));
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__5_splitter___redArg(lean_object* v_x_496_, lean_object* v_h__1_497_, lean_object* v_h__2_498_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec(v_h__1_497_);
v___x_499_ = lean_box(0);
v___x_500_ = lean_apply_1(v_h__2_498_, v___x_499_);
return v___x_500_;
}
else
{
lean_object* v_val_501_; lean_object* v___x_502_; 
lean_dec(v_h__2_498_);
v_val_501_ = lean_ctor_get(v_x_496_, 0);
lean_inc(v_val_501_);
lean_dec_ref_known(v_x_496_, 1);
v___x_502_ = lean_apply_1(v_h__1_497_, v_val_501_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__5_splitter(lean_object* v_motive_503_, lean_object* v_x_504_, lean_object* v_h__1_505_, lean_object* v_h__2_506_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v_h__1_505_);
v___x_507_ = lean_box(0);
v___x_508_ = lean_apply_1(v_h__2_506_, v___x_507_);
return v___x_508_;
}
else
{
lean_object* v_val_509_; lean_object* v___x_510_; 
lean_dec(v_h__2_506_);
v_val_509_ = lean_ctor_get(v_x_504_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v_x_504_, 1);
v___x_510_ = lean_apply_1(v_h__1_505_, v_val_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter___redArg(lean_object* v_unit_511_, lean_object* v_h__1_512_, lean_object* v_h__2_513_){
_start:
{
if (lean_obj_tag(v_unit_511_) == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v_h__1_512_);
v___x_514_ = lean_box(0);
v___x_515_ = lean_apply_1(v_h__2_513_, v___x_514_);
return v___x_515_;
}
else
{
lean_object* v_val_516_; lean_object* v___x_517_; 
lean_dec(v_h__2_513_);
v_val_516_ = lean_ctor_get(v_unit_511_, 0);
lean_inc(v_val_516_);
lean_dec_ref_known(v_unit_511_, 1);
v___x_517_ = lean_apply_1(v_h__1_512_, v_val_516_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter(lean_object* v_motive_518_, lean_object* v_unit_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_){
_start:
{
if (lean_obj_tag(v_unit_519_) == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v_h__1_520_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_apply_1(v_h__2_521_, v___x_522_);
return v___x_523_;
}
else
{
lean_object* v_val_524_; lean_object* v___x_525_; 
lean_dec(v_h__2_521_);
v_val_524_ = lean_ctor_get(v_unit_519_, 0);
lean_inc(v_val_524_);
lean_dec_ref_known(v_unit_519_, 1);
v___x_525_ = lean_apply_1(v_h__1_520_, v_val_524_);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter___redArg(lean_object* v_unit_526_, lean_object* v_h__1_527_, lean_object* v_h__2_528_){
_start:
{
if (lean_obj_tag(v_unit_526_) == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_h__2_528_);
v___x_529_ = lean_box(0);
v___x_530_ = lean_apply_1(v_h__1_527_, v___x_529_);
return v___x_530_;
}
else
{
lean_object* v_val_531_; lean_object* v___x_532_; 
lean_dec(v_h__1_527_);
v_val_531_ = lean_ctor_get(v_unit_526_, 0);
lean_inc(v_val_531_);
lean_dec_ref_known(v_unit_526_, 1);
v___x_532_ = lean_apply_1(v_h__2_528_, v_val_531_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter(lean_object* v_motive_533_, lean_object* v_unit_534_, lean_object* v_h__1_535_, lean_object* v_h__2_536_){
_start:
{
if (lean_obj_tag(v_unit_534_) == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_h__2_536_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_apply_1(v_h__1_535_, v___x_537_);
return v___x_538_;
}
else
{
lean_object* v_val_539_; lean_object* v___x_540_; 
lean_dec(v_h__1_535_);
v_val_539_ = lean_ctor_get(v_unit_534_, 0);
lean_inc(v_val_539_);
lean_dec_ref_known(v_unit_534_, 1);
v___x_540_ = lean_apply_1(v_h__2_536_, v_val_539_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_541_, lean_object* v_h__1_542_, lean_object* v_h__2_543_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_h__1_542_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_apply_1(v_h__2_543_, v___x_544_);
return v___x_545_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_547_; 
lean_dec(v_h__2_543_);
v_val_546_ = lean_ctor_get(v_x_541_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v_x_541_, 1);
v___x_547_ = lean_apply_1(v_h__1_542_, v_val_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_548_, lean_object* v_motive_549_, lean_object* v_x_550_, lean_object* v_h__1_551_, lean_object* v_h__2_552_){
_start:
{
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v_h__1_551_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_apply_1(v_h__2_552_, v___x_553_);
return v___x_554_;
}
else
{
lean_object* v_val_555_; lean_object* v___x_556_; 
lean_dec(v_h__2_552_);
v_val_555_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v_x_550_, 1);
v___x_556_ = lean_apply_1(v_h__1_551_, v_val_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__30_splitter___redArg(lean_object* v_ret_557_, lean_object* v_h__1_558_, lean_object* v_h__2_559_, lean_object* v_h__3_560_){
_start:
{
switch(lean_obj_tag(v_ret_557_))
{
case 0:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v_h__3_560_);
lean_dec(v_h__1_558_);
v___x_561_ = lean_box(0);
v___x_562_ = lean_apply_1(v_h__2_559_, v___x_561_);
return v___x_562_;
}
case 1:
{
lean_object* v_assign_563_; lean_object* v___x_564_; 
lean_dec(v_h__2_559_);
lean_dec(v_h__1_558_);
v_assign_563_ = lean_ctor_get(v_ret_557_, 0);
lean_inc_ref(v_assign_563_);
lean_dec_ref_known(v_ret_557_, 1);
v___x_564_ = lean_apply_1(v_h__3_560_, v_assign_563_);
return v___x_564_;
}
default: 
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v_h__3_560_);
lean_dec(v_h__2_559_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_apply_1(v_h__1_558_, v___x_565_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__30_splitter(lean_object* v_motive_567_, lean_object* v_ret_568_, lean_object* v_h__1_569_, lean_object* v_h__2_570_, lean_object* v_h__3_571_){
_start:
{
switch(lean_obj_tag(v_ret_568_))
{
case 0:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_h__3_571_);
lean_dec(v_h__1_569_);
v___x_572_ = lean_box(0);
v___x_573_ = lean_apply_1(v_h__2_570_, v___x_572_);
return v___x_573_;
}
case 1:
{
lean_object* v_assign_574_; lean_object* v___x_575_; 
lean_dec(v_h__2_570_);
lean_dec(v_h__1_569_);
v_assign_574_ = lean_ctor_get(v_ret_568_, 0);
lean_inc_ref(v_assign_574_);
lean_dec_ref_known(v_ret_568_, 1);
v___x_575_ = lean_apply_1(v_h__3_571_, v_assign_574_);
return v___x_575_;
}
default: 
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_h__3_571_);
lean_dec(v_h__2_570_);
v___x_576_ = lean_box(0);
v___x_577_ = lean_apply_1(v_h__1_569_, v___x_576_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter___redArg(lean_object* v_x_578_, lean_object* v_h__1_579_, lean_object* v_h__2_580_, lean_object* v_h__3_581_){
_start:
{
switch(lean_obj_tag(v_x_578_))
{
case 0:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_h__3_581_);
lean_dec(v_h__2_580_);
v___x_582_ = lean_box(0);
v___x_583_ = lean_apply_1(v_h__1_579_, v___x_582_);
return v___x_583_;
}
case 1:
{
lean_object* v_assign_584_; lean_object* v___x_585_; 
lean_dec(v_h__3_581_);
lean_dec(v_h__1_579_);
v_assign_584_ = lean_ctor_get(v_x_578_, 0);
lean_inc_ref(v_assign_584_);
lean_dec_ref_known(v_x_578_, 1);
v___x_585_ = lean_apply_1(v_h__2_580_, v_assign_584_);
return v___x_585_;
}
default: 
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_h__2_580_);
lean_dec(v_h__1_579_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_apply_1(v_h__3_581_, v___x_586_);
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter(lean_object* v_motive_588_, lean_object* v_x_589_, lean_object* v_h__1_590_, lean_object* v_h__2_591_, lean_object* v_h__3_592_){
_start:
{
switch(lean_obj_tag(v_x_589_))
{
case 0:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_h__3_592_);
lean_dec(v_h__2_591_);
v___x_593_ = lean_box(0);
v___x_594_ = lean_apply_1(v_h__1_590_, v___x_593_);
return v___x_594_;
}
case 1:
{
lean_object* v_assign_595_; lean_object* v___x_596_; 
lean_dec(v_h__3_592_);
lean_dec(v_h__1_590_);
v_assign_595_ = lean_ctor_get(v_x_589_, 0);
lean_inc_ref(v_assign_595_);
lean_dec_ref_known(v_x_589_, 1);
v___x_596_ = lean_apply_1(v_h__2_591_, v_assign_595_);
return v___x_596_;
}
default: 
{
lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v_h__2_591_);
lean_dec(v_h__1_590_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_apply_1(v_h__3_592_, v___x_597_);
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter___redArg(lean_object* v_x_599_, lean_object* v_h__1_600_, lean_object* v_h__2_601_){
_start:
{
if (lean_obj_tag(v_x_599_) == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_h__2_601_);
v___x_602_ = lean_box(0);
v___x_603_ = lean_apply_1(v_h__1_600_, v___x_602_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; 
lean_dec(v_h__1_600_);
v___x_604_ = lean_apply_2(v_h__2_601_, v_x_599_, lean_box(0));
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter(lean_object* v_motive_605_, lean_object* v_x_606_, lean_object* v_h__1_607_, lean_object* v_h__2_608_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v_h__2_608_);
v___x_609_ = lean_box(0);
v___x_610_ = lean_apply_1(v_h__1_607_, v___x_609_);
return v___x_610_;
}
else
{
lean_object* v___x_611_; 
lean_dec(v_h__1_607_);
v___x_611_ = lean_apply_2(v_h__2_608_, v_x_606_, lean_box(0));
return v___x_611_;
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
