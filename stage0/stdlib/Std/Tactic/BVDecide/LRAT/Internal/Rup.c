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
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(lean_object* v___x_208_, lean_object* v___x_209_, lean_object* v_c_210_, size_t v_sz_211_, size_t v_i_212_, lean_object* v_b_213_){
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
lean_object* v_snd_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_305_; 
v_snd_220_ = lean_ctor_get(v_b_213_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_b_213_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v_b_213_, 0);
lean_dec(v_unused_306_);
v___x_222_ = v_b_213_;
v_isShared_223_ = v_isSharedCheck_305_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_snd_220_);
lean_dec(v_b_213_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_305_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_atoms_224_; lean_object* v_polarities_225_; lean_object* v_fst_226_; lean_object* v_snd_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_304_; 
v_atoms_224_ = lean_ctor_get(v_c_210_, 0);
v_polarities_225_ = lean_ctor_get(v_c_210_, 1);
v_fst_226_ = lean_ctor_get(v_snd_220_, 0);
v_snd_227_ = lean_ctor_get(v_snd_220_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_snd_220_);
if (v_isSharedCheck_304_ == 0)
{
v___x_229_ = v_snd_220_;
v_isShared_230_ = v_isSharedCheck_304_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_snd_227_);
lean_inc(v_fst_226_);
lean_dec(v_snd_220_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_304_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___y_241_; uint8_t v___x_273_; uint8_t v___x_274_; uint8_t v___x_275_; uint8_t v___x_276_; uint8_t v_val_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_231_ = lean_array_uget_borrowed(v_atoms_224_, v_i_212_);
v___x_232_ = lean_box(0);
v___x_273_ = lean_nat_dec_lt(v___x_208_, v___x_209_);
v___x_274_ = lean_byte_array_uget(v_polarities_225_, v_i_212_);
v___x_275_ = 1;
v___x_276_ = lean_uint8_dec_eq(v___x_274_, v___x_275_);
v___x_279_ = 0;
v___x_280_ = lean_box(v___x_279_);
v___x_281_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(v_fst_226_, v___x_231_, v___x_280_);
lean_dec(v___x_280_);
v___x_282_ = lean_unbox(v___x_281_);
lean_dec(v___x_281_);
switch(v___x_282_)
{
case 0:
{
lean_del_object(v___x_229_);
lean_del_object(v___x_222_);
if (lean_obj_tag(v_snd_227_) == 0)
{
lean_object* v___x_283_; uint8_t v___y_285_; 
lean_inc(v___x_231_);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_231_);
if (v___x_276_ == 0)
{
uint8_t v___x_290_; 
v___x_290_ = 2;
v___y_285_ = v___x_290_;
goto v___jp_284_;
}
else
{
uint8_t v___x_291_; 
v___x_291_ = 1;
v___y_285_ = v___x_291_;
goto v___jp_284_;
}
v___jp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_286_ = lean_box(v___y_285_);
lean_inc(v___x_231_);
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(v_fst_226_, v___x_231_, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_283_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_232_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v_a_215_ = v___x_289_;
goto v___jp_214_;
}
}
else
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_300_; 
v_isSharedCheck_300_ = !lean_is_exclusive(v_c_210_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; lean_object* v_unused_302_; 
v_unused_301_ = lean_ctor_get(v_c_210_, 1);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_c_210_, 0);
lean_dec(v_unused_302_);
v___x_293_ = v_c_210_;
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
else
{
lean_dec(v_c_210_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_snd_227_);
lean_ctor_set(v___x_293_, 0, v_fst_226_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_fst_226_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_snd_227_);
v___x_297_ = v_reuseFailAlloc_299_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; 
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_295_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
}
}
}
case 1:
{
v_val_278_ = v___x_273_;
goto v___jp_277_;
}
default: 
{
uint8_t v___x_303_; 
v___x_303_ = 0;
v_val_278_ = v___x_303_;
goto v___jp_277_;
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
if (v___y_241_ == 0)
{
if (lean_obj_tag(v_snd_227_) == 0)
{
goto v___jp_233_;
}
else
{
lean_object* v_val_242_; uint8_t v___x_243_; 
v_val_242_ = lean_ctor_get(v_snd_227_, 0);
v___x_243_ = lean_nat_dec_eq(v_val_242_, v___x_231_);
if (v___x_243_ == 0)
{
goto v___jp_233_;
}
else
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_252_; 
lean_del_object(v___x_229_);
lean_del_object(v___x_222_);
v_isSharedCheck_252_ = !lean_is_exclusive(v_c_210_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; lean_object* v_unused_254_; 
v_unused_253_ = lean_ctor_get(v_c_210_, 1);
lean_dec(v_unused_253_);
v_unused_254_ = lean_ctor_get(v_c_210_, 0);
lean_dec(v_unused_254_);
v___x_245_ = v_c_210_;
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_c_210_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v_snd_227_);
lean_ctor_set(v___x_245_, 0, v_fst_226_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_fst_226_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_snd_227_);
v___x_249_ = v_reuseFailAlloc_251_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; 
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_247_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
return v___x_250_;
}
}
}
}
}
else
{
lean_del_object(v___x_229_);
lean_del_object(v___x_222_);
if (lean_obj_tag(v_snd_227_) == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_inc(v___x_231_);
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_231_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_fst_226_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_232_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v_a_215_ = v___x_257_;
goto v___jp_214_;
}
else
{
lean_object* v_val_258_; uint8_t v___x_259_; 
v_val_258_ = lean_ctor_get(v_snd_227_, 0);
v___x_259_ = lean_nat_dec_eq(v_val_258_, v___x_231_);
if (v___x_259_ == 0)
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_268_; 
v_isSharedCheck_268_ = !lean_is_exclusive(v_c_210_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; lean_object* v_unused_270_; 
v_unused_269_ = lean_ctor_get(v_c_210_, 1);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_c_210_, 0);
lean_dec(v_unused_270_);
v___x_261_ = v_c_210_;
v_isShared_262_ = v_isSharedCheck_268_;
goto v_resetjp_260_;
}
else
{
lean_dec(v_c_210_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_268_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v_snd_227_);
lean_ctor_set(v___x_261_, 0, v_fst_226_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_fst_226_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_snd_227_);
v___x_265_ = v_reuseFailAlloc_267_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_263_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
return v___x_266_;
}
}
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v_fst_226_);
lean_ctor_set(v___x_271_, 1, v_snd_227_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_232_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v_a_215_ = v___x_272_;
goto v___jp_214_;
}
}
}
}
v___jp_277_:
{
if (v___x_276_ == 0)
{
if (v_val_278_ == 0)
{
v___y_241_ = v___x_273_;
goto v___jp_240_;
}
else
{
v___y_241_ = v___x_276_;
goto v___jp_240_;
}
}
else
{
v___y_241_ = v_val_278_;
goto v___jp_240_;
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
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___boxed(lean_object* v___x_307_, lean_object* v___x_308_, lean_object* v_c_309_, lean_object* v_sz_310_, lean_object* v_i_311_, lean_object* v_b_312_){
_start:
{
size_t v_sz_boxed_313_; size_t v_i_boxed_314_; lean_object* v_res_315_; 
v_sz_boxed_313_ = lean_unbox_usize(v_sz_310_);
lean_dec(v_sz_310_);
v_i_boxed_314_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_res_315_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(v___x_307_, v___x_308_, v_c_309_, v_sz_boxed_313_, v_i_boxed_314_, v_b_312_);
lean_dec(v___x_308_);
lean_dec(v___x_307_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(lean_object* v_s_318_, lean_object* v_as_319_, size_t v_sz_320_, size_t v_i_321_, lean_object* v_b_322_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = lean_usize_dec_lt(v_i_321_, v_sz_320_);
if (v___x_323_ == 0)
{
return v_b_322_;
}
else
{
lean_object* v_snd_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_381_; 
v_snd_324_ = lean_ctor_get(v_b_322_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_b_322_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v_b_322_, 0);
lean_dec(v_unused_382_);
v___x_326_ = v_b_322_;
v_isShared_327_ = v_isSharedCheck_381_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_snd_324_);
lean_dec(v_b_322_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_381_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_a_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_a_333_ = lean_array_uget_borrowed(v_as_319_, v_i_321_);
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_sub(v_a_333_, v___x_334_);
v___x_336_ = lean_array_get_size(v_s_318_);
v___x_337_ = lean_nat_dec_lt(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_dec(v___x_335_);
goto v___jp_328_;
}
else
{
lean_object* v___x_338_; 
v___x_338_ = lean_array_fget_borrowed(v_s_318_, v___x_335_);
if (lean_obj_tag(v___x_338_) == 1)
{
lean_object* v_val_339_; lean_object* v_atoms_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; size_t v_sz_344_; size_t v___x_345_; lean_object* v___x_346_; lean_object* v_snd_347_; lean_object* v_fst_348_; 
lean_del_object(v___x_326_);
v_val_339_ = lean_ctor_get(v___x_338_, 0);
v_atoms_340_ = lean_ctor_get(v_val_339_, 0);
v___x_341_ = lean_box(0);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_snd_324_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v_sz_344_ = lean_array_size(v_atoms_340_);
v___x_345_ = ((size_t)0ULL);
lean_inc(v_val_339_);
v___x_346_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(v___x_335_, v___x_336_, v_val_339_, v_sz_344_, v___x_345_, v___x_343_);
lean_dec(v___x_335_);
v_snd_347_ = lean_ctor_get(v___x_346_, 1);
lean_inc(v_snd_347_);
v_fst_348_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_fst_348_);
lean_dec_ref(v___x_346_);
if (lean_obj_tag(v_fst_348_) == 0)
{
lean_object* v_snd_349_; 
v_snd_349_ = lean_ctor_get(v_snd_347_, 1);
if (lean_obj_tag(v_snd_349_) == 0)
{
lean_object* v_fst_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_fst_350_ = lean_ctor_get(v_snd_347_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v_snd_347_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v_snd_347_, 1);
lean_dec(v_unused_359_);
v___x_352_ = v_snd_347_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_fst_350_);
lean_dec(v_snd_347_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___closed__0));
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v_fst_350_);
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_fst_350_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_fst_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_370_; 
v_fst_360_ = lean_ctor_get(v_snd_347_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v_snd_347_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v_snd_347_, 1);
lean_dec(v_unused_371_);
v___x_362_ = v_snd_347_;
v_isShared_363_ = v_isSharedCheck_370_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_fst_360_);
lean_dec(v_snd_347_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_370_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v_fst_360_);
lean_ctor_set(v___x_362_, 0, v___x_341_);
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_fst_360_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
size_t v___x_366_; size_t v___x_367_; 
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_321_, v___x_366_);
v_i_321_ = v___x_367_;
v_b_322_ = v___x_365_;
goto _start;
}
}
}
}
else
{
lean_object* v_fst_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_fst_372_ = lean_ctor_get(v_snd_347_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_snd_347_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v_snd_347_, 1);
lean_dec(v_unused_380_);
v___x_374_ = v_snd_347_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_fst_372_);
lean_dec(v_snd_347_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 1, v_fst_372_);
lean_ctor_set(v___x_374_, 0, v_fst_348_);
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_fst_348_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_fst_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
else
{
lean_dec(v___x_335_);
goto v___jp_328_;
}
}
v___jp_328_:
{
lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_329_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_329_);
v___x_331_ = v___x_326_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_snd_324_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___boxed(lean_object* v_s_383_, lean_object* v_as_384_, lean_object* v_sz_385_, lean_object* v_i_386_, lean_object* v_b_387_){
_start:
{
size_t v_sz_boxed_388_; size_t v_i_boxed_389_; lean_object* v_res_390_; 
v_sz_boxed_388_ = lean_unbox_usize(v_sz_385_);
lean_dec(v_sz_385_);
v_i_boxed_389_ = lean_unbox_usize(v_i_386_);
lean_dec(v_i_386_);
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(v_s_383_, v_as_384_, v_sz_boxed_388_, v_i_boxed_389_, v_b_387_);
lean_dec_ref(v_as_384_);
lean_dec_ref(v_s_383_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(lean_object* v_s_391_, lean_object* v_assign_392_, lean_object* v_hints_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; size_t v_sz_396_; size_t v___x_397_; lean_object* v___x_398_; lean_object* v_fst_399_; 
v___x_394_ = lean_box(0);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v_assign_392_);
v_sz_396_ = lean_array_size(v_hints_393_);
v___x_397_ = ((size_t)0ULL);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(v_s_391_, v_hints_393_, v_sz_396_, v___x_397_, v___x_395_);
v_fst_399_ = lean_ctor_get(v___x_398_, 0);
if (lean_obj_tag(v_fst_399_) == 0)
{
lean_object* v_snd_400_; lean_object* v___x_401_; 
v_snd_400_ = lean_ctor_get(v___x_398_, 1);
lean_inc(v_snd_400_);
lean_dec_ref(v___x_398_);
v___x_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_401_, 0, v_snd_400_);
return v___x_401_;
}
else
{
lean_object* v_val_402_; 
lean_inc_ref(v_fst_399_);
lean_dec_ref(v___x_398_);
v_val_402_ = lean_ctor_get(v_fst_399_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v_fst_399_, 1);
return v_val_402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints___boxed(lean_object* v_s_403_, lean_object* v_assign_404_, lean_object* v_hints_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(v_s_403_, v_assign_404_, v_hints_405_);
lean_dec_ref(v_hints_405_);
lean_dec_ref(v_s_403_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0(lean_object* v_00_u03b2_407_, lean_object* v_m_408_, lean_object* v_a_409_, lean_object* v_fallback_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(v_m_408_, v_a_409_, v_fallback_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___boxed(lean_object* v_00_u03b2_412_, lean_object* v_m_413_, lean_object* v_a_414_, lean_object* v_fallback_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0(v_00_u03b2_412_, v_m_413_, v_a_414_, v_fallback_415_);
lean_dec(v_fallback_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_m_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1(lean_object* v_00_u03b2_417_, lean_object* v_m_418_, lean_object* v_a_419_, lean_object* v_b_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(v_m_418_, v_a_419_, v_b_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0(lean_object* v_00_u03b2_422_, lean_object* v_a_423_, lean_object* v_fallback_424_, lean_object* v_x_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg(v_a_423_, v_fallback_424_, v_x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___boxed(lean_object* v_00_u03b2_427_, lean_object* v_a_428_, lean_object* v_fallback_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0(v_00_u03b2_427_, v_a_428_, v_fallback_429_, v_x_430_);
lean_dec(v_x_430_);
lean_dec(v_fallback_429_);
lean_dec(v_a_428_);
return v_res_431_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2(lean_object* v_00_u03b2_432_, lean_object* v_a_433_, lean_object* v_x_434_){
_start:
{
uint8_t v___x_435_; 
v___x_435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(v_a_433_, v_x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___boxed(lean_object* v_00_u03b2_436_, lean_object* v_a_437_, lean_object* v_x_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2(v_00_u03b2_436_, v_a_437_, v_x_438_);
lean_dec(v_x_438_);
lean_dec(v_a_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3(lean_object* v_00_u03b2_441_, lean_object* v_data_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3___redArg(v_data_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4(lean_object* v_00_u03b2_444_, lean_object* v_a_445_, lean_object* v_b_446_, lean_object* v_x_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(v_a_445_, v_b_446_, v_x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_449_, lean_object* v_i_450_, lean_object* v_source_451_, lean_object* v_target_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4___redArg(v_i_450_, v_source_451_, v_target_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7___redArg(v_x_455_, v_x_456_);
return v___x_457_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(lean_object* v_s_458_, lean_object* v_assign_459_, lean_object* v_rupHints_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(v_s_458_, v_assign_459_, v_rupHints_460_);
if (lean_obj_tag(v___x_461_) == 0)
{
uint8_t v___x_462_; 
v___x_462_ = 1;
return v___x_462_;
}
else
{
uint8_t v___x_463_; 
lean_dec(v___x_461_);
v___x_463_ = 0;
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate___boxed(lean_object* v_s_464_, lean_object* v_assign_465_, lean_object* v_rupHints_466_){
_start:
{
uint8_t v_res_467_; lean_object* v_r_468_; 
v_res_467_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_464_, v_assign_465_, v_rupHints_466_);
lean_dec_ref(v_rupHints_466_);
lean_dec_ref(v_s_464_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(lean_object* v_s_469_, lean_object* v_clause_470_, lean_object* v_rupHints_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(v_clause_470_);
if (lean_obj_tag(v___x_472_) == 1)
{
lean_object* v_val_473_; uint8_t v___x_474_; 
v_val_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_val_473_);
lean_dec_ref_known(v___x_472_, 1);
v___x_474_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_469_, v_val_473_, v_rupHints_471_);
return v___x_474_;
}
else
{
uint8_t v___x_475_; 
lean_dec(v___x_472_);
v___x_475_ = 1;
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup___boxed(lean_object* v_s_476_, lean_object* v_clause_477_, lean_object* v_rupHints_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(v_s_476_, v_clause_477_, v_rupHints_478_);
lean_dec_ref(v_rupHints_478_);
lean_dec_ref(v_clause_477_);
lean_dec_ref(v_s_476_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__9_splitter___redArg(lean_object* v_x_481_, lean_object* v_h__1_482_, lean_object* v_h__2_483_){
_start:
{
if (lean_obj_tag(v_x_481_) == 1)
{
lean_object* v_val_484_; lean_object* v___x_485_; 
lean_dec(v_h__2_483_);
v_val_484_ = lean_ctor_get(v_x_481_, 0);
lean_inc(v_val_484_);
lean_dec_ref_known(v_x_481_, 1);
v___x_485_ = lean_apply_1(v_h__1_482_, v_val_484_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; 
lean_dec(v_h__1_482_);
v___x_486_ = lean_apply_2(v_h__2_483_, v_x_481_, lean_box(0));
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__9_splitter(lean_object* v_motive_487_, lean_object* v_x_488_, lean_object* v_h__1_489_, lean_object* v_h__2_490_){
_start:
{
if (lean_obj_tag(v_x_488_) == 1)
{
lean_object* v_val_491_; lean_object* v___x_492_; 
lean_dec(v_h__2_490_);
v_val_491_ = lean_ctor_get(v_x_488_, 0);
lean_inc(v_val_491_);
lean_dec_ref_known(v_x_488_, 1);
v___x_492_ = lean_apply_1(v_h__1_489_, v_val_491_);
return v___x_492_;
}
else
{
lean_object* v___x_493_; 
lean_dec(v_h__1_489_);
v___x_493_ = lean_apply_2(v_h__2_490_, v_x_488_, lean_box(0));
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__5_splitter___redArg(lean_object* v_x_494_, lean_object* v_h__1_495_, lean_object* v_h__2_496_){
_start:
{
if (lean_obj_tag(v_x_494_) == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_h__1_495_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_apply_1(v_h__2_496_, v___x_497_);
return v___x_498_;
}
else
{
lean_object* v_val_499_; lean_object* v___x_500_; 
lean_dec(v_h__2_496_);
v_val_499_ = lean_ctor_get(v_x_494_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v_x_494_, 1);
v___x_500_ = lean_apply_1(v_h__1_495_, v_val_499_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__5_splitter(lean_object* v_motive_501_, lean_object* v_x_502_, lean_object* v_h__1_503_, lean_object* v_h__2_504_){
_start:
{
if (lean_obj_tag(v_x_502_) == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v_h__1_503_);
v___x_505_ = lean_box(0);
v___x_506_ = lean_apply_1(v_h__2_504_, v___x_505_);
return v___x_506_;
}
else
{
lean_object* v_val_507_; lean_object* v___x_508_; 
lean_dec(v_h__2_504_);
v_val_507_ = lean_ctor_get(v_x_502_, 0);
lean_inc(v_val_507_);
lean_dec_ref_known(v_x_502_, 1);
v___x_508_ = lean_apply_1(v_h__1_503_, v_val_507_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter___redArg(lean_object* v_unit_509_, lean_object* v_h__1_510_, lean_object* v_h__2_511_){
_start:
{
if (lean_obj_tag(v_unit_509_) == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v_h__1_510_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_apply_1(v_h__2_511_, v___x_512_);
return v___x_513_;
}
else
{
lean_object* v_val_514_; lean_object* v___x_515_; 
lean_dec(v_h__2_511_);
v_val_514_ = lean_ctor_get(v_unit_509_, 0);
lean_inc(v_val_514_);
lean_dec_ref_known(v_unit_509_, 1);
v___x_515_ = lean_apply_1(v_h__1_510_, v_val_514_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter(lean_object* v_motive_516_, lean_object* v_unit_517_, lean_object* v_h__1_518_, lean_object* v_h__2_519_){
_start:
{
if (lean_obj_tag(v_unit_517_) == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_h__1_518_);
v___x_520_ = lean_box(0);
v___x_521_ = lean_apply_1(v_h__2_519_, v___x_520_);
return v___x_521_;
}
else
{
lean_object* v_val_522_; lean_object* v___x_523_; 
lean_dec(v_h__2_519_);
v_val_522_ = lean_ctor_get(v_unit_517_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v_unit_517_, 1);
v___x_523_ = lean_apply_1(v_h__1_518_, v_val_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter___redArg(lean_object* v_unit_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_){
_start:
{
if (lean_obj_tag(v_unit_524_) == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_h__2_526_);
v___x_527_ = lean_box(0);
v___x_528_ = lean_apply_1(v_h__1_525_, v___x_527_);
return v___x_528_;
}
else
{
lean_object* v_val_529_; lean_object* v___x_530_; 
lean_dec(v_h__1_525_);
v_val_529_ = lean_ctor_get(v_unit_524_, 0);
lean_inc(v_val_529_);
lean_dec_ref_known(v_unit_524_, 1);
v___x_530_ = lean_apply_1(v_h__2_526_, v_val_529_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter(lean_object* v_motive_531_, lean_object* v_unit_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
if (lean_obj_tag(v_unit_532_) == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_h__2_534_);
v___x_535_ = lean_box(0);
v___x_536_ = lean_apply_1(v_h__1_533_, v___x_535_);
return v___x_536_;
}
else
{
lean_object* v_val_537_; lean_object* v___x_538_; 
lean_dec(v_h__1_533_);
v_val_537_ = lean_ctor_get(v_unit_532_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v_unit_532_, 1);
v___x_538_ = lean_apply_1(v_h__2_534_, v_val_537_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_539_, lean_object* v_h__1_540_, lean_object* v_h__2_541_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v_h__1_540_);
v___x_542_ = lean_box(0);
v___x_543_ = lean_apply_1(v_h__2_541_, v___x_542_);
return v___x_543_;
}
else
{
lean_object* v_val_544_; lean_object* v___x_545_; 
lean_dec(v_h__2_541_);
v_val_544_ = lean_ctor_get(v_x_539_, 0);
lean_inc(v_val_544_);
lean_dec_ref_known(v_x_539_, 1);
v___x_545_ = lean_apply_1(v_h__1_540_, v_val_544_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_546_, lean_object* v_motive_547_, lean_object* v_x_548_, lean_object* v_h__1_549_, lean_object* v_h__2_550_){
_start:
{
if (lean_obj_tag(v_x_548_) == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
lean_dec(v_h__1_549_);
v___x_551_ = lean_box(0);
v___x_552_ = lean_apply_1(v_h__2_550_, v___x_551_);
return v___x_552_;
}
else
{
lean_object* v_val_553_; lean_object* v___x_554_; 
lean_dec(v_h__2_550_);
v_val_553_ = lean_ctor_get(v_x_548_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v_x_548_, 1);
v___x_554_ = lean_apply_1(v_h__1_549_, v_val_553_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__30_splitter___redArg(lean_object* v_ret_555_, lean_object* v_h__1_556_, lean_object* v_h__2_557_, lean_object* v_h__3_558_){
_start:
{
switch(lean_obj_tag(v_ret_555_))
{
case 0:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v_h__3_558_);
lean_dec(v_h__1_556_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_apply_1(v_h__2_557_, v___x_559_);
return v___x_560_;
}
case 1:
{
lean_object* v_assign_561_; lean_object* v___x_562_; 
lean_dec(v_h__2_557_);
lean_dec(v_h__1_556_);
v_assign_561_ = lean_ctor_get(v_ret_555_, 0);
lean_inc_ref(v_assign_561_);
lean_dec_ref_known(v_ret_555_, 1);
v___x_562_ = lean_apply_1(v_h__3_558_, v_assign_561_);
return v___x_562_;
}
default: 
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v_h__3_558_);
lean_dec(v_h__2_557_);
v___x_563_ = lean_box(0);
v___x_564_ = lean_apply_1(v_h__1_556_, v___x_563_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__30_splitter(lean_object* v_motive_565_, lean_object* v_ret_566_, lean_object* v_h__1_567_, lean_object* v_h__2_568_, lean_object* v_h__3_569_){
_start:
{
switch(lean_obj_tag(v_ret_566_))
{
case 0:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_h__3_569_);
lean_dec(v_h__1_567_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_apply_1(v_h__2_568_, v___x_570_);
return v___x_571_;
}
case 1:
{
lean_object* v_assign_572_; lean_object* v___x_573_; 
lean_dec(v_h__2_568_);
lean_dec(v_h__1_567_);
v_assign_572_ = lean_ctor_get(v_ret_566_, 0);
lean_inc_ref(v_assign_572_);
lean_dec_ref_known(v_ret_566_, 1);
v___x_573_ = lean_apply_1(v_h__3_569_, v_assign_572_);
return v___x_573_;
}
default: 
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v_h__3_569_);
lean_dec(v_h__2_568_);
v___x_574_ = lean_box(0);
v___x_575_ = lean_apply_1(v_h__1_567_, v___x_574_);
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter___redArg(lean_object* v_x_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_, lean_object* v_h__3_579_){
_start:
{
switch(lean_obj_tag(v_x_576_))
{
case 0:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_h__3_579_);
lean_dec(v_h__2_578_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_apply_1(v_h__1_577_, v___x_580_);
return v___x_581_;
}
case 1:
{
lean_object* v_assign_582_; lean_object* v___x_583_; 
lean_dec(v_h__3_579_);
lean_dec(v_h__1_577_);
v_assign_582_ = lean_ctor_get(v_x_576_, 0);
lean_inc_ref(v_assign_582_);
lean_dec_ref_known(v_x_576_, 1);
v___x_583_ = lean_apply_1(v_h__2_578_, v_assign_582_);
return v___x_583_;
}
default: 
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_h__2_578_);
lean_dec(v_h__1_577_);
v___x_584_ = lean_box(0);
v___x_585_ = lean_apply_1(v_h__3_579_, v___x_584_);
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter(lean_object* v_motive_586_, lean_object* v_x_587_, lean_object* v_h__1_588_, lean_object* v_h__2_589_, lean_object* v_h__3_590_){
_start:
{
switch(lean_obj_tag(v_x_587_))
{
case 0:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec(v_h__3_590_);
lean_dec(v_h__2_589_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_apply_1(v_h__1_588_, v___x_591_);
return v___x_592_;
}
case 1:
{
lean_object* v_assign_593_; lean_object* v___x_594_; 
lean_dec(v_h__3_590_);
lean_dec(v_h__1_588_);
v_assign_593_ = lean_ctor_get(v_x_587_, 0);
lean_inc_ref(v_assign_593_);
lean_dec_ref_known(v_x_587_, 1);
v___x_594_ = lean_apply_1(v_h__2_589_, v_assign_593_);
return v___x_594_;
}
default: 
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v_h__2_589_);
lean_dec(v_h__1_588_);
v___x_595_ = lean_box(0);
v___x_596_ = lean_apply_1(v_h__3_590_, v___x_595_);
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter___redArg(lean_object* v_x_597_, lean_object* v_h__1_598_, lean_object* v_h__2_599_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v_h__2_599_);
v___x_600_ = lean_box(0);
v___x_601_ = lean_apply_1(v_h__1_598_, v___x_600_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; 
lean_dec(v_h__1_598_);
v___x_602_ = lean_apply_2(v_h__2_599_, v_x_597_, lean_box(0));
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter(lean_object* v_motive_603_, lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_h__2_606_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_apply_1(v_h__1_605_, v___x_607_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; 
lean_dec(v_h__1_605_);
v___x_609_ = lean_apply_2(v_h__2_606_, v_x_604_, lean_box(0));
return v___x_609_;
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
