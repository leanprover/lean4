// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Rup
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Basic public import Std.Tactic.BVDecide.LRAT.Internal.Assignment import Init.Omega import Init.ByCases import Std.Internal.Sat.CNF.SpecLemmas import Std.Tactic.Do
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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorIdx___impl___boxed(lean_object*);
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
static const lean_ctor_object l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0 = (const lean_object*)&l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__36_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__36_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 1)
{
lean_object* v_assign_7_; lean_object* v___x_8_; 
v_assign_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_assign_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_assign_7_);
return v___x_8_;
}
else
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_conflict_elim___redArg(lean_object* v_t_21_, lean_object* v_conflict_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_21_, v_conflict_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_conflict_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_conflict_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_25_, v_conflict_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_extended_elim___redArg(lean_object* v_t_29_, lean_object* v_extended_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_29_, v_extended_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_extended_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_extended_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_33_, v_extended_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_error_elim___redArg(lean_object* v_t_37_, lean_object* v_error_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_37_, v_error_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_error_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_error_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_Tactic_BVDecide_LRAT_Internal_PropagateResult_ctorElim___redArg(v_t_41_, v_error_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg(lean_object* v_a_45_, lean_object* v_fallback_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_47_) == 0)
{
lean_inc(v_fallback_46_);
return v_fallback_46_;
}
else
{
lean_object* v_key_48_; lean_object* v_value_49_; lean_object* v_tail_50_; uint8_t v___x_51_; 
v_key_48_ = lean_ctor_get(v_x_47_, 0);
v_value_49_ = lean_ctor_get(v_x_47_, 1);
v_tail_50_ = lean_ctor_get(v_x_47_, 2);
v___x_51_ = lean_nat_dec_eq(v_key_48_, v_a_45_);
if (v___x_51_ == 0)
{
v_x_47_ = v_tail_50_;
goto _start;
}
else
{
lean_inc(v_value_49_);
return v_value_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg___boxed(lean_object* v_a_53_, lean_object* v_fallback_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg(v_a_53_, v_fallback_54_, v_x_55_);
lean_dec(v_x_55_);
lean_dec(v_fallback_54_);
lean_dec(v_a_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(lean_object* v_m_57_, lean_object* v_a_58_, lean_object* v_fallback_59_){
_start:
{
lean_object* v_buckets_60_; lean_object* v___x_61_; uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v_fold_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; size_t v___x_69_; size_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_buckets_60_ = lean_ctor_get(v_m_57_, 1);
v___x_61_ = lean_array_get_size(v_buckets_60_);
v___x_62_ = lean_uint64_of_nat(v_a_58_);
v___x_63_ = 32ULL;
v___x_64_ = lean_uint64_shift_right(v___x_62_, v___x_63_);
v_fold_65_ = lean_uint64_xor(v___x_62_, v___x_64_);
v___x_66_ = 16ULL;
v___x_67_ = lean_uint64_shift_right(v_fold_65_, v___x_66_);
v___x_68_ = lean_uint64_xor(v_fold_65_, v___x_67_);
v___x_69_ = lean_uint64_to_usize(v___x_68_);
v___x_70_ = lean_usize_of_nat(v___x_61_);
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_sub(v___x_70_, v___x_71_);
v___x_73_ = lean_usize_land(v___x_69_, v___x_72_);
v___x_74_ = lean_array_uget_borrowed(v_buckets_60_, v___x_73_);
v___x_75_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg(v_a_58_, v_fallback_59_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg___boxed(lean_object* v_m_76_, lean_object* v_a_77_, lean_object* v_fallback_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(v_m_76_, v_a_77_, v_fallback_78_);
lean_dec(v_fallback_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_m_76_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7___redArg(lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
return v_x_80_;
}
else
{
lean_object* v_key_82_; lean_object* v_value_83_; lean_object* v_tail_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_107_; 
v_key_82_ = lean_ctor_get(v_x_81_, 0);
v_value_83_ = lean_ctor_get(v_x_81_, 1);
v_tail_84_ = lean_ctor_get(v_x_81_, 2);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_81_);
if (v_isSharedCheck_107_ == 0)
{
v___x_86_ = v_x_81_;
v_isShared_87_ = v_isSharedCheck_107_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_tail_84_);
lean_inc(v_value_83_);
lean_inc(v_key_82_);
lean_dec(v_x_81_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_107_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; uint64_t v___x_89_; uint64_t v___x_90_; uint64_t v___x_91_; uint64_t v_fold_92_; uint64_t v___x_93_; uint64_t v___x_94_; uint64_t v___x_95_; size_t v___x_96_; size_t v___x_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_88_ = lean_array_get_size(v_x_80_);
v___x_89_ = lean_uint64_of_nat(v_key_82_);
v___x_90_ = 32ULL;
v___x_91_ = lean_uint64_shift_right(v___x_89_, v___x_90_);
v_fold_92_ = lean_uint64_xor(v___x_89_, v___x_91_);
v___x_93_ = 16ULL;
v___x_94_ = lean_uint64_shift_right(v_fold_92_, v___x_93_);
v___x_95_ = lean_uint64_xor(v_fold_92_, v___x_94_);
v___x_96_ = lean_uint64_to_usize(v___x_95_);
v___x_97_ = lean_usize_of_nat(v___x_88_);
v___x_98_ = ((size_t)1ULL);
v___x_99_ = lean_usize_sub(v___x_97_, v___x_98_);
v___x_100_ = lean_usize_land(v___x_96_, v___x_99_);
v___x_101_ = lean_array_uget_borrowed(v_x_80_, v___x_100_);
lean_inc(v___x_101_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 2, v___x_101_);
v___x_103_ = v___x_86_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_key_82_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_value_83_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v___x_101_);
v___x_103_ = v_reuseFailAlloc_106_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = lean_array_uset(v_x_80_, v___x_100_, v___x_103_);
v_x_80_ = v___x_104_;
v_x_81_ = v_tail_84_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4___redArg(lean_object* v_i_108_, lean_object* v_source_109_, lean_object* v_target_110_){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_array_get_size(v_source_109_);
v___x_112_ = lean_nat_dec_lt(v_i_108_, v___x_111_);
if (v___x_112_ == 0)
{
lean_dec_ref(v_source_109_);
lean_dec(v_i_108_);
return v_target_110_;
}
else
{
lean_object* v_es_113_; lean_object* v___x_114_; lean_object* v_source_115_; lean_object* v_target_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_es_113_ = lean_array_fget(v_source_109_, v_i_108_);
v___x_114_ = lean_box(0);
v_source_115_ = lean_array_fset(v_source_109_, v_i_108_, v___x_114_);
v_target_116_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7___redArg(v_target_110_, v_es_113_);
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v_i_108_, v___x_117_);
lean_dec(v_i_108_);
v_i_108_ = v___x_118_;
v_source_109_ = v_source_115_;
v_target_110_ = v_target_116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3___redArg(lean_object* v_data_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_nbuckets_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_121_ = lean_array_get_size(v_data_120_);
v___x_122_ = lean_unsigned_to_nat(2u);
v_nbuckets_123_ = lean_nat_mul(v___x_121_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_box(0);
v___x_126_ = lean_mk_array(v_nbuckets_123_, v___x_125_);
v___x_127_ = lean_array_propagate_mark(v_data_120_, v___x_126_);
v___x_128_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4___redArg(v___x_124_, v_data_120_, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(lean_object* v_a_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
else
{
lean_object* v_key_132_; lean_object* v_tail_133_; uint8_t v___x_134_; 
v_key_132_ = lean_ctor_get(v_x_130_, 0);
v_tail_133_ = lean_ctor_get(v_x_130_, 2);
v___x_134_ = lean_nat_dec_eq(v_key_132_, v_a_129_);
if (v___x_134_ == 0)
{
v_x_130_ = v_tail_133_;
goto _start;
}
else
{
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg___boxed(lean_object* v_a_136_, lean_object* v_x_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(v_a_136_, v_x_137_);
lean_dec(v_x_137_);
lean_dec(v_a_136_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(lean_object* v_a_140_, lean_object* v_b_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_dec(v_b_141_);
lean_dec(v_a_140_);
return v_x_142_;
}
else
{
lean_object* v_key_143_; lean_object* v_value_144_; lean_object* v_tail_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_157_; 
v_key_143_ = lean_ctor_get(v_x_142_, 0);
v_value_144_ = lean_ctor_get(v_x_142_, 1);
v_tail_145_ = lean_ctor_get(v_x_142_, 2);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_157_ == 0)
{
v___x_147_ = v_x_142_;
v_isShared_148_ = v_isSharedCheck_157_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_tail_145_);
lean_inc(v_value_144_);
lean_inc(v_key_143_);
lean_dec(v_x_142_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_157_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_eq(v_key_143_, v_a_140_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_150_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(v_a_140_, v_b_141_, v_tail_145_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 2, v___x_150_);
v___x_152_ = v___x_147_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_key_143_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_value_144_);
lean_ctor_set(v_reuseFailAlloc_153_, 2, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
else
{
lean_object* v___x_155_; 
lean_dec(v_value_144_);
lean_dec(v_key_143_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v_b_141_);
lean_ctor_set(v___x_147_, 0, v_a_140_);
v___x_155_ = v___x_147_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_140_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_b_141_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_tail_145_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(lean_object* v_m_158_, lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
lean_object* v_size_161_; lean_object* v_buckets_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_205_; 
v_size_161_ = lean_ctor_get(v_m_158_, 0);
v_buckets_162_ = lean_ctor_get(v_m_158_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_m_158_);
if (v_isSharedCheck_205_ == 0)
{
v___x_164_ = v_m_158_;
v_isShared_165_ = v_isSharedCheck_205_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_buckets_162_);
lean_inc(v_size_161_);
lean_dec(v_m_158_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_205_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v_fold_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; lean_object* v_bkt_179_; uint8_t v___x_180_; 
v___x_166_ = lean_array_get_size(v_buckets_162_);
v___x_167_ = lean_uint64_of_nat(v_a_159_);
v___x_168_ = 32ULL;
v___x_169_ = lean_uint64_shift_right(v___x_167_, v___x_168_);
v_fold_170_ = lean_uint64_xor(v___x_167_, v___x_169_);
v___x_171_ = 16ULL;
v___x_172_ = lean_uint64_shift_right(v_fold_170_, v___x_171_);
v___x_173_ = lean_uint64_xor(v_fold_170_, v___x_172_);
v___x_174_ = lean_uint64_to_usize(v___x_173_);
v___x_175_ = lean_usize_of_nat(v___x_166_);
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_sub(v___x_175_, v___x_176_);
v___x_178_ = lean_usize_land(v___x_174_, v___x_177_);
v_bkt_179_ = lean_array_uget_borrowed(v_buckets_162_, v___x_178_);
v___x_180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(v_a_159_, v_bkt_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v_size_x27_182_; lean_object* v___x_183_; lean_object* v_buckets_x27_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v_size_x27_182_ = lean_nat_add(v_size_161_, v___x_181_);
lean_dec(v_size_161_);
lean_inc(v_bkt_179_);
v___x_183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_183_, 0, v_a_159_);
lean_ctor_set(v___x_183_, 1, v_b_160_);
lean_ctor_set(v___x_183_, 2, v_bkt_179_);
v_buckets_x27_184_ = lean_array_uset(v_buckets_162_, v___x_178_, v___x_183_);
v___x_185_ = lean_unsigned_to_nat(4u);
v___x_186_ = lean_nat_mul(v_size_x27_182_, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(3u);
v___x_188_ = lean_nat_div(v___x_186_, v___x_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_array_get_size(v_buckets_x27_184_);
v___x_190_ = lean_nat_dec_le(v___x_188_, v___x_189_);
lean_dec(v___x_188_);
if (v___x_190_ == 0)
{
lean_object* v_val_191_; lean_object* v___x_193_; 
v_val_191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3___redArg(v_buckets_x27_184_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v_val_191_);
lean_ctor_set(v___x_164_, 0, v_size_x27_182_);
v___x_193_ = v___x_164_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_size_x27_182_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_val_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
else
{
lean_object* v___x_196_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v_buckets_x27_184_);
lean_ctor_set(v___x_164_, 0, v_size_x27_182_);
v___x_196_ = v___x_164_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_size_x27_182_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_buckets_x27_184_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
else
{
lean_object* v___x_198_; lean_object* v_buckets_x27_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
lean_inc(v_bkt_179_);
v___x_198_ = lean_box(0);
v_buckets_x27_199_ = lean_array_uset(v_buckets_162_, v___x_178_, v___x_198_);
v___x_200_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(v_a_159_, v_b_160_, v_bkt_179_);
v___x_201_ = lean_array_uset(v_buckets_x27_199_, v___x_178_, v___x_200_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v___x_201_);
v___x_203_ = v___x_164_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_size_161_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(lean_object* v___x_208_, lean_object* v___x_209_, lean_object* v_c_210_, size_t v_sz_211_, size_t v_i_212_, lean_object* v_b_213_){
_start:
{
lean_object* v_a_215_; uint8_t v___x_219_; 
v___x_219_ = lean_usize_dec_lt(v_i_212_, v_sz_211_);
if (v___x_219_ == 0)
{
lean_dec_ref(v_c_210_);
return v_b_213_;
}
else
{
lean_object* v_snd_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_306_; 
v_snd_220_ = lean_ctor_get(v_b_213_, 1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_b_213_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v_b_213_, 0);
lean_dec(v_unused_307_);
v___x_222_ = v_b_213_;
v_isShared_223_ = v_isSharedCheck_306_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_snd_220_);
lean_dec(v_b_213_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_306_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_atoms_224_; lean_object* v_polarities_225_; lean_object* v_fst_226_; lean_object* v_snd_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_305_; 
v_atoms_224_ = lean_ctor_get(v_c_210_, 0);
v_polarities_225_ = lean_ctor_get(v_c_210_, 1);
v_fst_226_ = lean_ctor_get(v_snd_220_, 0);
v_snd_227_ = lean_ctor_get(v_snd_220_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_snd_220_);
if (v_isSharedCheck_305_ == 0)
{
v___x_229_ = v_snd_220_;
v_isShared_230_ = v_isSharedCheck_305_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_snd_227_);
lean_inc(v_fst_226_);
lean_dec(v_snd_220_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_305_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___y_255_; uint8_t v___x_274_; uint8_t v___x_275_; uint8_t v___x_276_; uint8_t v___x_277_; uint8_t v_val_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_231_ = lean_array_uget_borrowed(v_atoms_224_, v_i_212_);
v___x_232_ = lean_box(0);
v___x_274_ = lean_nat_dec_lt(v___x_208_, v___x_209_);
v___x_275_ = lean_byte_array_uget(v_polarities_225_, v_i_212_);
v___x_276_ = 1;
v___x_277_ = lean_uint8_dec_eq(v___x_275_, v___x_276_);
v___x_280_ = 0;
v___x_281_ = lean_box(v___x_280_);
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(v_fst_226_, v___x_231_, v___x_281_);
lean_dec(v___x_281_);
v___x_283_ = lean_unbox(v___x_282_);
lean_dec(v___x_282_);
switch(v___x_283_)
{
case 0:
{
lean_del_object(v___x_229_);
lean_del_object(v___x_222_);
if (lean_obj_tag(v_snd_227_) == 0)
{
lean_object* v___x_284_; uint8_t v___y_286_; 
lean_inc(v___x_231_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_231_);
if (v___x_277_ == 0)
{
uint8_t v___x_291_; 
v___x_291_ = 2;
v___y_286_ = v___x_291_;
goto v___jp_285_;
}
else
{
uint8_t v___x_292_; 
v___x_292_ = 1;
v___y_286_ = v___x_292_;
goto v___jp_285_;
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_287_ = lean_box(v___y_286_);
lean_inc(v___x_231_);
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(v_fst_226_, v___x_231_, v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_284_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_232_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v_a_215_ = v___x_290_;
goto v___jp_214_;
}
}
else
{
lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_301_; 
v_isSharedCheck_301_ = !lean_is_exclusive(v_c_210_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; lean_object* v_unused_303_; 
v_unused_302_ = lean_ctor_get(v_c_210_, 1);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_c_210_, 0);
lean_dec(v_unused_303_);
v___x_294_ = v_c_210_;
v_isShared_295_ = v_isSharedCheck_301_;
goto v_resetjp_293_;
}
else
{
lean_dec(v_c_210_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_301_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = ((lean_object*)(l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v_snd_227_);
lean_ctor_set(v___x_294_, 0, v_fst_226_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_fst_226_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_snd_227_);
v___x_298_ = v_reuseFailAlloc_300_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; 
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_296_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
return v___x_299_;
}
}
}
}
case 1:
{
v_val_279_ = v___x_274_;
goto v___jp_278_;
}
default: 
{
uint8_t v___x_304_; 
v___x_304_ = 0;
v_val_279_ = v___x_304_;
goto v___jp_278_;
}
}
v___jp_233_:
{
lean_object* v___x_235_; 
if (v_isShared_230_ == 0)
{
v___x_235_ = v___x_229_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_fst_226_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_snd_227_);
v___x_235_ = v_reuseFailAlloc_239_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___x_235_);
lean_ctor_set(v___x_222_, 0, v___x_232_);
v___x_237_ = v___x_222_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
v_a_215_ = v___x_237_;
goto v___jp_214_;
}
}
}
v___jp_240_:
{
if (lean_obj_tag(v_snd_227_) == 0)
{
goto v___jp_233_;
}
else
{
lean_object* v_val_241_; uint8_t v___x_242_; 
v_val_241_ = lean_ctor_get(v_snd_227_, 0);
v___x_242_ = lean_nat_dec_eq(v_val_241_, v___x_231_);
if (v___x_242_ == 0)
{
goto v___jp_233_;
}
else
{
lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_251_; 
lean_del_object(v___x_229_);
lean_del_object(v___x_222_);
v_isSharedCheck_251_ = !lean_is_exclusive(v_c_210_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; lean_object* v_unused_253_; 
v_unused_252_ = lean_ctor_get(v_c_210_, 1);
lean_dec(v_unused_252_);
v_unused_253_ = lean_ctor_get(v_c_210_, 0);
lean_dec(v_unused_253_);
v___x_244_ = v_c_210_;
v_isShared_245_ = v_isSharedCheck_251_;
goto v_resetjp_243_;
}
else
{
lean_dec(v_c_210_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_251_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = ((lean_object*)(l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v_snd_227_);
lean_ctor_set(v___x_244_, 0, v_fst_226_);
v___x_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_fst_226_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_snd_227_);
v___x_248_ = v_reuseFailAlloc_250_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_246_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
return v___x_249_;
}
}
}
}
}
v___jp_254_:
{
if (v___y_255_ == 0)
{
goto v___jp_240_;
}
else
{
lean_del_object(v___x_229_);
lean_del_object(v___x_222_);
if (lean_obj_tag(v_snd_227_) == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_inc(v___x_231_);
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_231_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_fst_226_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_232_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v_a_215_ = v___x_258_;
goto v___jp_214_;
}
else
{
lean_object* v_val_259_; uint8_t v___x_260_; 
v_val_259_ = lean_ctor_get(v_snd_227_, 0);
v___x_260_ = lean_nat_dec_eq(v_val_259_, v___x_231_);
if (v___x_260_ == 0)
{
lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_269_; 
v_isSharedCheck_269_ = !lean_is_exclusive(v_c_210_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; lean_object* v_unused_271_; 
v_unused_270_ = lean_ctor_get(v_c_210_, 1);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_c_210_, 0);
lean_dec(v_unused_271_);
v___x_262_ = v_c_210_;
v_isShared_263_ = v_isSharedCheck_269_;
goto v_resetjp_261_;
}
else
{
lean_dec(v_c_210_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_269_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = ((lean_object*)(l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v_snd_227_);
lean_ctor_set(v___x_262_, 0, v_fst_226_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_fst_226_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_snd_227_);
v___x_266_ = v_reuseFailAlloc_268_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_264_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
return v___x_267_;
}
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_fst_226_);
lean_ctor_set(v___x_272_, 1, v_snd_227_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_232_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v_a_215_ = v___x_273_;
goto v___jp_214_;
}
}
}
}
v___jp_278_:
{
if (v___x_277_ == 0)
{
if (v_val_279_ == 0)
{
v___y_255_ = v___x_274_;
goto v___jp_254_;
}
else
{
goto v___jp_240_;
}
}
else
{
v___y_255_ = v_val_279_;
goto v___jp_254_;
}
}
}
}
}
v___jp_214_:
{
size_t v___x_216_; size_t v___x_217_; 
v___x_216_ = ((size_t)1ULL);
v___x_217_ = lean_usize_add(v_i_212_, v___x_216_);
v_i_212_ = v___x_217_;
v_b_213_ = v_a_215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___boxed(lean_object* v___x_308_, lean_object* v___x_309_, lean_object* v_c_310_, lean_object* v_sz_311_, lean_object* v_i_312_, lean_object* v_b_313_){
_start:
{
size_t v_sz_boxed_314_; size_t v_i_boxed_315_; lean_object* v_res_316_; 
v_sz_boxed_314_ = lean_unbox_usize(v_sz_311_);
lean_dec(v_sz_311_);
v_i_boxed_315_ = lean_unbox_usize(v_i_312_);
lean_dec(v_i_312_);
v_res_316_ = l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(v___x_308_, v___x_309_, v_c_310_, v_sz_boxed_314_, v_i_boxed_315_, v_b_313_);
lean_dec(v___x_309_);
lean_dec(v___x_308_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(lean_object* v_s_319_, lean_object* v_as_320_, size_t v_sz_321_, size_t v_i_322_, lean_object* v_b_323_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = lean_usize_dec_lt(v_i_322_, v_sz_321_);
if (v___x_324_ == 0)
{
return v_b_323_;
}
else
{
lean_object* v_snd_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_383_; 
v_snd_325_ = lean_ctor_get(v_b_323_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_b_323_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_b_323_, 0);
lean_dec(v_unused_384_);
v___x_327_ = v_b_323_;
v_isShared_328_ = v_isSharedCheck_383_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_snd_325_);
lean_dec(v_b_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_383_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_a_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_a_334_ = lean_array_uget_borrowed(v_as_320_, v_i_322_);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_sub(v_a_334_, v___x_335_);
v___x_337_ = lean_array_get_size(v_s_319_);
v___x_338_ = lean_nat_dec_lt(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec(v___x_336_);
goto v___jp_329_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = lean_array_fget_borrowed(v_s_319_, v___x_336_);
if (lean_obj_tag(v___x_339_) == 1)
{
lean_object* v_val_340_; lean_object* v_atoms_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; size_t v_sz_345_; size_t v___x_346_; lean_object* v___x_347_; lean_object* v_fst_348_; 
lean_del_object(v___x_327_);
v_val_340_ = lean_ctor_get(v___x_339_, 0);
v_atoms_341_ = lean_ctor_get(v_val_340_, 0);
v___x_342_ = lean_box(0);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_snd_325_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v_sz_345_ = lean_array_size(v_atoms_341_);
v___x_346_ = ((size_t)0ULL);
lean_inc(v_val_340_);
v___x_347_ = l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(v___x_336_, v___x_337_, v_val_340_, v_sz_345_, v___x_346_, v___x_344_);
lean_dec(v___x_336_);
v_fst_348_ = lean_ctor_get(v___x_347_, 0);
if (lean_obj_tag(v_fst_348_) == 0)
{
lean_object* v_snd_349_; lean_object* v_snd_350_; 
v_snd_349_ = lean_ctor_get(v___x_347_, 1);
lean_inc(v_snd_349_);
lean_dec_ref(v___x_347_);
v_snd_350_ = lean_ctor_get(v_snd_349_, 1);
if (lean_obj_tag(v_snd_350_) == 0)
{
lean_object* v_fst_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_359_; 
v_fst_351_ = lean_ctor_get(v_snd_349_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v_snd_349_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; 
v_unused_360_ = lean_ctor_get(v_snd_349_, 1);
lean_dec(v_unused_360_);
v___x_353_ = v_snd_349_;
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_fst_351_);
lean_dec(v_snd_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___closed__0));
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v_fst_351_);
lean_ctor_set(v___x_353_, 0, v___x_355_);
v___x_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_fst_351_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
else
{
lean_object* v_fst_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_fst_361_ = lean_ctor_get(v_snd_349_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v_snd_349_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v_snd_349_, 1);
lean_dec(v_unused_372_);
v___x_363_ = v_snd_349_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_fst_361_);
lean_dec(v_snd_349_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 1, v_fst_361_);
lean_ctor_set(v___x_363_, 0, v___x_342_);
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_fst_361_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
size_t v___x_367_; size_t v___x_368_; 
v___x_367_ = ((size_t)1ULL);
v___x_368_ = lean_usize_add(v_i_322_, v___x_367_);
v_i_322_ = v___x_368_;
v_b_323_ = v___x_366_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_373_; lean_object* v_fst_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_inc_ref(v_fst_348_);
v_snd_373_ = lean_ctor_get(v___x_347_, 1);
lean_inc(v_snd_373_);
lean_dec_ref(v___x_347_);
v_fst_374_ = lean_ctor_get(v_snd_373_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v_snd_373_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v_snd_373_, 1);
lean_dec(v_unused_382_);
v___x_376_ = v_snd_373_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_fst_374_);
lean_dec(v_snd_373_);
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
lean_ctor_set(v___x_376_, 0, v_fst_348_);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_fst_348_);
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
lean_dec(v___x_336_);
goto v___jp_329_;
}
}
v___jp_329_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = ((lean_object*)(l___private_Std_Internal_Sat_CNF_Basic_0__Std_Internal_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_330_);
v___x_332_ = v___x_327_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_snd_325_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
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
lean_inc_ref(v_fst_401_);
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__36_splitter___redArg(lean_object* v_ret_557_, lean_object* v_h__1_558_, lean_object* v_h__2_559_, lean_object* v_h__3_560_){
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__36_splitter(lean_object* v_motive_567_, lean_object* v_ret_568_, lean_object* v_h__1_569_, lean_object* v_h__2_570_, lean_object* v_h__3_571_){
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
lean_object* runtime_initialize_Std_Internal_Sat_CNF_SpecLemmas(uint8_t builtin);
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
res = runtime_initialize_Std_Internal_Sat_CNF_SpecLemmas(builtin);
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
lean_object* initialize_Std_Internal_Sat_CNF_SpecLemmas(uint8_t builtin);
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
res = initialize_Std_Internal_Sat_CNF_SpecLemmas(builtin);
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
