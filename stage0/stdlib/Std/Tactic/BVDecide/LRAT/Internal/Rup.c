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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__32_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__32_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(lean_object* v_a_129_, lean_object* v_x_130_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_129_ = stack[0].m_obj;
lean_object* v_x_130_ = stack[1].m_obj;
uint8_t v_res_136_;
v_res_136_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(v_a_129_, v_x_130_);
stack->m_num = v_res_136_;
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
lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(lean_object* v___x_209_, lean_object* v___x_210_, lean_object* v_c_211_, size_t v_sz_212_, size_t v_i_213_, lean_object* v_b_214_){
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
lean_object* v_snd_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_306_; 
v_snd_221_ = lean_ctor_get(v_b_214_, 1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_b_214_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v_b_214_, 0);
lean_dec(v_unused_307_);
v___x_223_ = v_b_214_;
v_isShared_224_ = v_isSharedCheck_306_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_snd_221_);
lean_dec(v_b_214_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_306_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_atoms_225_; lean_object* v_polarities_226_; lean_object* v_fst_227_; lean_object* v_snd_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_305_; 
v_atoms_225_ = lean_ctor_get(v_c_211_, 0);
v_polarities_226_ = lean_ctor_get(v_c_211_, 1);
v_fst_227_ = lean_ctor_get(v_snd_221_, 0);
v_snd_228_ = lean_ctor_get(v_snd_221_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_snd_221_);
if (v_isSharedCheck_305_ == 0)
{
v___x_230_ = v_snd_221_;
v_isShared_231_ = v_isSharedCheck_305_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_snd_228_);
lean_inc(v_fst_227_);
lean_dec(v_snd_221_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_305_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___y_242_; uint8_t v___x_274_; uint8_t v___x_275_; uint8_t v___x_276_; uint8_t v___x_277_; uint8_t v_val_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_232_ = lean_array_uget_borrowed(v_atoms_225_, v_i_213_);
v___x_233_ = lean_box(0);
v___x_274_ = lean_nat_dec_lt(v___x_209_, v___x_210_);
v___x_275_ = lean_byte_array_uget(v_polarities_226_, v_i_213_);
v___x_276_ = 1;
v___x_277_ = lean_uint8_dec_eq(v___x_275_, v___x_276_);
v___x_280_ = 0;
v___x_281_ = lean_box(v___x_280_);
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(v_fst_227_, v___x_232_, v___x_281_);
lean_dec(v___x_281_);
v___x_283_ = lean_unbox(v___x_282_);
lean_dec(v___x_282_);
switch(v___x_283_)
{
case 0:
{
lean_del_object(v___x_230_);
lean_del_object(v___x_223_);
if (lean_obj_tag(v_snd_228_) == 0)
{
lean_object* v___x_284_; uint8_t v___y_286_; 
lean_inc(v___x_232_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_232_);
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
lean_inc(v___x_232_);
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(v_fst_227_, v___x_232_, v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_284_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_233_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v_a_216_ = v___x_290_;
goto v___jp_215_;
}
}
else
{
lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_301_; 
v_isSharedCheck_301_ = !lean_is_exclusive(v_c_211_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; lean_object* v_unused_303_; 
v_unused_302_ = lean_ctor_get(v_c_211_, 1);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_c_211_, 0);
lean_dec(v_unused_303_);
v___x_294_ = v_c_211_;
v_isShared_295_ = v_isSharedCheck_301_;
goto v_resetjp_293_;
}
else
{
lean_dec(v_c_211_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_301_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v_snd_228_);
lean_ctor_set(v___x_294_, 0, v_fst_227_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_snd_228_);
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
v___jp_234_:
{
lean_object* v___x_236_; 
if (v_isShared_231_ == 0)
{
v___x_236_ = v___x_230_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_snd_228_);
v___x_236_ = v_reuseFailAlloc_240_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_236_);
lean_ctor_set(v___x_223_, 0, v___x_233_);
v___x_238_ = v___x_223_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
v_a_216_ = v___x_238_;
goto v___jp_215_;
}
}
}
v___jp_241_:
{
if (v___y_242_ == 0)
{
if (lean_obj_tag(v_snd_228_) == 0)
{
goto v___jp_234_;
}
else
{
lean_object* v_val_243_; uint8_t v___x_244_; 
v_val_243_ = lean_ctor_get(v_snd_228_, 0);
v___x_244_ = lean_nat_dec_eq(v_val_243_, v___x_232_);
if (v___x_244_ == 0)
{
goto v___jp_234_;
}
else
{
lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_253_; 
lean_del_object(v___x_230_);
lean_del_object(v___x_223_);
v_isSharedCheck_253_ = !lean_is_exclusive(v_c_211_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; lean_object* v_unused_255_; 
v_unused_254_ = lean_ctor_get(v_c_211_, 1);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_c_211_, 0);
lean_dec(v_unused_255_);
v___x_246_ = v_c_211_;
v_isShared_247_ = v_isSharedCheck_253_;
goto v_resetjp_245_;
}
else
{
lean_dec(v_c_211_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_253_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v_snd_228_);
lean_ctor_set(v___x_246_, 0, v_fst_227_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_snd_228_);
v___x_250_ = v_reuseFailAlloc_252_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; 
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_248_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
return v___x_251_;
}
}
}
}
}
else
{
lean_del_object(v___x_230_);
lean_del_object(v___x_223_);
if (lean_obj_tag(v_snd_228_) == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_inc(v___x_232_);
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_232_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_fst_227_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_233_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v_a_216_ = v___x_258_;
goto v___jp_215_;
}
else
{
lean_object* v_val_259_; uint8_t v___x_260_; 
v_val_259_ = lean_ctor_get(v_snd_228_, 0);
v___x_260_ = lean_nat_dec_eq(v_val_259_, v___x_232_);
if (v___x_260_ == 0)
{
lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_269_; 
v_isSharedCheck_269_ = !lean_is_exclusive(v_c_211_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; lean_object* v_unused_271_; 
v_unused_270_ = lean_ctor_get(v_c_211_, 1);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_c_211_, 0);
lean_dec(v_unused_271_);
v___x_262_ = v_c_211_;
v_isShared_263_ = v_isSharedCheck_269_;
goto v_resetjp_261_;
}
else
{
lean_dec(v_c_211_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_269_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2___closed__0));
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v_snd_228_);
lean_ctor_set(v___x_262_, 0, v_fst_227_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_snd_228_);
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
lean_ctor_set(v___x_272_, 0, v_fst_227_);
lean_ctor_set(v___x_272_, 1, v_snd_228_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_233_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v_a_216_ = v___x_273_;
goto v___jp_215_;
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
v___y_242_ = v___x_274_;
goto v___jp_241_;
}
else
{
v___y_242_ = v___x_277_;
goto v___jp_241_;
}
}
else
{
v___y_242_ = v_val_279_;
goto v___jp_241_;
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
LEAN_EXPORT void l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_209_ = stack[0].m_obj;
lean_object* v___x_210_ = stack[1].m_obj;
lean_object* v_c_211_ = stack[2].m_obj;
size_t v_sz_212_ = stack[3].m_num;
size_t v_i_213_ = stack[4].m_num;
lean_object* v_b_214_ = stack[5].m_obj;
lean_object* v_res_308_;
v_res_308_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__2(v___x_209_, v___x_210_, v_c_211_, v_sz_212_, v_i_213_, v_b_214_);
stack->m_obj
 = v_res_308_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(lean_object* v_s_320_, lean_object* v_as_321_, size_t v_sz_322_, size_t v_i_323_, lean_object* v_b_324_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_320_ = stack[0].m_obj;
lean_object* v_as_321_ = stack[1].m_obj;
size_t v_sz_322_ = stack[2].m_num;
size_t v_i_323_ = stack[3].m_num;
lean_object* v_b_324_ = stack[4].m_obj;
lean_object* v_res_385_;
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(v_s_320_, v_as_321_, v_sz_322_, v_i_323_, v_b_324_);
stack->m_obj
 = v_res_385_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3___boxed(lean_object* v_s_386_, lean_object* v_as_387_, lean_object* v_sz_388_, lean_object* v_i_389_, lean_object* v_b_390_){
_start:
{
size_t v_sz_boxed_391_; size_t v_i_boxed_392_; lean_object* v_res_393_; 
v_sz_boxed_391_ = lean_unbox_usize(v_sz_388_);
lean_dec(v_sz_388_);
v_i_boxed_392_ = lean_unbox_usize(v_i_389_);
lean_dec(v_i_389_);
v_res_393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(v_s_386_, v_as_387_, v_sz_boxed_391_, v_i_boxed_392_, v_b_390_);
lean_dec_ref(v_as_387_);
lean_dec_ref(v_s_386_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(lean_object* v_s_394_, lean_object* v_assign_395_, lean_object* v_hints_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; size_t v_sz_399_; size_t v___x_400_; lean_object* v___x_401_; lean_object* v_fst_402_; 
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_assign_395_);
v_sz_399_ = lean_array_size(v_hints_396_);
v___x_400_ = ((size_t)0ULL);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__3(v_s_394_, v_hints_396_, v_sz_399_, v___x_400_, v___x_398_);
v_fst_402_ = lean_ctor_get(v___x_401_, 0);
if (lean_obj_tag(v_fst_402_) == 0)
{
lean_object* v_snd_403_; lean_object* v___x_404_; 
v_snd_403_ = lean_ctor_get(v___x_401_, 1);
lean_inc(v_snd_403_);
lean_dec_ref(v___x_401_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v_snd_403_);
return v___x_404_;
}
else
{
lean_object* v_val_405_; 
lean_inc_ref(v_fst_402_);
lean_dec_ref(v___x_401_);
v_val_405_ = lean_ctor_get(v_fst_402_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v_fst_402_, 1);
return v_val_405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints___boxed(lean_object* v_s_406_, lean_object* v_assign_407_, lean_object* v_hints_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(v_s_406_, v_assign_407_, v_hints_408_);
lean_dec_ref(v_hints_408_);
lean_dec_ref(v_s_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0(lean_object* v_00_u03b2_410_, lean_object* v_m_411_, lean_object* v_a_412_, lean_object* v_fallback_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___redArg(v_m_411_, v_a_412_, v_fallback_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0___boxed(lean_object* v_00_u03b2_415_, lean_object* v_m_416_, lean_object* v_a_417_, lean_object* v_fallback_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0(v_00_u03b2_415_, v_m_416_, v_a_417_, v_fallback_418_);
lean_dec(v_fallback_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_m_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1(lean_object* v_00_u03b2_420_, lean_object* v_m_421_, lean_object* v_a_422_, lean_object* v_b_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1___redArg(v_m_421_, v_a_422_, v_b_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0(lean_object* v_00_u03b2_425_, lean_object* v_a_426_, lean_object* v_fallback_427_, lean_object* v_x_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___redArg(v_a_426_, v_fallback_427_, v_x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0___boxed(lean_object* v_00_u03b2_430_, lean_object* v_a_431_, lean_object* v_fallback_432_, lean_object* v_x_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__0_spec__0(v_00_u03b2_430_, v_a_431_, v_fallback_432_, v_x_433_);
lean_dec(v_x_433_);
lean_dec(v_fallback_432_);
lean_dec(v_a_431_);
return v_res_434_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2(lean_object* v_00_u03b2_435_, lean_object* v_a_436_, lean_object* v_x_437_){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___redArg(v_a_436_, v_x_437_);
return v___x_438_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_436_ = stack[1].m_obj;
lean_object* v_x_437_ = stack[2].m_obj;
uint8_t v_res_439_;
v_res_439_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2(lean_box(0), v_a_436_, v_x_437_);
stack->m_num = v_res_439_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2___boxed(lean_object* v_00_u03b2_440_, lean_object* v_a_441_, lean_object* v_x_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__2(v_00_u03b2_440_, v_a_441_, v_x_442_);
lean_dec(v_x_442_);
lean_dec(v_a_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3(lean_object* v_00_u03b2_445_, lean_object* v_data_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3___redArg(v_data_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4(lean_object* v_00_u03b2_448_, lean_object* v_a_449_, lean_object* v_b_450_, lean_object* v_x_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__4___redArg(v_a_449_, v_b_450_, v_x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_453_, lean_object* v_i_454_, lean_object* v_source_455_, lean_object* v_target_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4___redArg(v_i_454_, v_source_455_, v_target_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_spec__1_spec__3_spec__4_spec__7___redArg(v_x_459_, v_x_460_);
return v___x_461_;
}
}
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(lean_object* v_s_462_, lean_object* v_assign_463_, lean_object* v_rupHints_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints(v_s_462_, v_assign_463_, v_rupHints_464_);
if (lean_obj_tag(v___x_465_) == 0)
{
uint8_t v___x_466_; 
v___x_466_ = 1;
return v___x_466_;
}
else
{
uint8_t v___x_467_; 
lean_dec(v___x_465_);
v___x_467_ = 0;
return v___x_467_;
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_462_ = stack[0].m_obj;
lean_object* v_assign_463_ = stack[1].m_obj;
lean_object* v_rupHints_464_ = stack[2].m_obj;
uint8_t v_res_468_;
v_res_468_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_462_, v_assign_463_, v_rupHints_464_);
stack->m_num = v_res_468_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate___boxed(lean_object* v_s_469_, lean_object* v_assign_470_, lean_object* v_rupHints_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_469_, v_assign_470_, v_rupHints_471_);
lean_dec_ref(v_rupHints_471_);
lean_dec_ref(v_s_469_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(lean_object* v_s_474_, lean_object* v_clause_475_, lean_object* v_rupHints_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofClause(v_clause_475_);
if (lean_obj_tag(v___x_477_) == 1)
{
lean_object* v_val_478_; uint8_t v___x_479_; 
v_val_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_val_478_);
lean_dec_ref_known(v___x_477_, 1);
v___x_479_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate(v_s_474_, v_val_478_, v_rupHints_476_);
return v___x_479_;
}
else
{
uint8_t v___x_480_; 
lean_dec(v___x_477_);
v___x_480_ = 1;
return v___x_480_;
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_474_ = stack[0].m_obj;
lean_object* v_clause_475_ = stack[1].m_obj;
lean_object* v_rupHints_476_ = stack[2].m_obj;
uint8_t v_res_481_;
v_res_481_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(v_s_474_, v_clause_475_, v_rupHints_476_);
stack->m_num = v_res_481_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup___boxed(lean_object* v_s_482_, lean_object* v_clause_483_, lean_object* v_rupHints_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(v_s_482_, v_clause_483_, v_rupHints_484_);
lean_dec_ref(v_rupHints_484_);
lean_dec_ref(v_clause_483_);
lean_dec_ref(v_s_482_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__9_splitter___redArg(lean_object* v_x_487_, lean_object* v_h__1_488_, lean_object* v_h__2_489_){
_start:
{
if (lean_obj_tag(v_x_487_) == 1)
{
lean_object* v_val_490_; lean_object* v___x_491_; 
lean_dec(v_h__2_489_);
v_val_490_ = lean_ctor_get(v_x_487_, 0);
lean_inc(v_val_490_);
lean_dec_ref_known(v_x_487_, 1);
v___x_491_ = lean_apply_1(v_h__1_488_, v_val_490_);
return v___x_491_;
}
else
{
lean_object* v___x_492_; 
lean_dec(v_h__1_488_);
v___x_492_ = lean_apply_2(v_h__2_489_, v_x_487_, lean_box(0));
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__9_splitter(lean_object* v_motive_493_, lean_object* v_x_494_, lean_object* v_h__1_495_, lean_object* v_h__2_496_){
_start:
{
if (lean_obj_tag(v_x_494_) == 1)
{
lean_object* v_val_497_; lean_object* v___x_498_; 
lean_dec(v_h__2_496_);
v_val_497_ = lean_ctor_get(v_x_494_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v_x_494_, 1);
v___x_498_ = lean_apply_1(v_h__1_495_, v_val_497_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
lean_dec(v_h__1_495_);
v___x_499_ = lean_apply_2(v_h__2_496_, v_x_494_, lean_box(0));
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__5_splitter___redArg(lean_object* v_x_500_, lean_object* v_h__1_501_, lean_object* v_h__2_502_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_h__1_501_);
v___x_503_ = lean_box(0);
v___x_504_ = lean_apply_1(v_h__2_502_, v___x_503_);
return v___x_504_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_506_; 
lean_dec(v_h__2_502_);
v_val_505_ = lean_ctor_get(v_x_500_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v_x_500_, 1);
v___x_506_ = lean_apply_1(v_h__1_501_, v_val_505_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__5_splitter(lean_object* v_motive_507_, lean_object* v_x_508_, lean_object* v_h__1_509_, lean_object* v_h__2_510_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_h__1_509_);
v___x_511_ = lean_box(0);
v___x_512_ = lean_apply_1(v_h__2_510_, v___x_511_);
return v___x_512_;
}
else
{
lean_object* v_val_513_; lean_object* v___x_514_; 
lean_dec(v_h__2_510_);
v_val_513_ = lean_ctor_get(v_x_508_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v_x_508_, 1);
v___x_514_ = lean_apply_1(v_h__1_509_, v_val_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter___redArg(lean_object* v_unit_515_, lean_object* v_h__1_516_, lean_object* v_h__2_517_){
_start:
{
if (lean_obj_tag(v_unit_515_) == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec(v_h__1_516_);
v___x_518_ = lean_box(0);
v___x_519_ = lean_apply_1(v_h__2_517_, v___x_518_);
return v___x_519_;
}
else
{
lean_object* v_val_520_; lean_object* v___x_521_; 
lean_dec(v_h__2_517_);
v_val_520_ = lean_ctor_get(v_unit_515_, 0);
lean_inc(v_val_520_);
lean_dec_ref_known(v_unit_515_, 1);
v___x_521_ = lean_apply_1(v_h__1_516_, v_val_520_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__1_splitter(lean_object* v_motive_522_, lean_object* v_unit_523_, lean_object* v_h__1_524_, lean_object* v_h__2_525_){
_start:
{
if (lean_obj_tag(v_unit_523_) == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v_h__1_524_);
v___x_526_ = lean_box(0);
v___x_527_ = lean_apply_1(v_h__2_525_, v___x_526_);
return v___x_527_;
}
else
{
lean_object* v_val_528_; lean_object* v___x_529_; 
lean_dec(v_h__2_525_);
v_val_528_ = lean_ctor_get(v_unit_523_, 0);
lean_inc(v_val_528_);
lean_dec_ref_known(v_unit_523_, 1);
v___x_529_ = lean_apply_1(v_h__1_524_, v_val_528_);
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter___redArg(lean_object* v_unit_530_, lean_object* v_h__1_531_, lean_object* v_h__2_532_){
_start:
{
if (lean_obj_tag(v_unit_530_) == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v_h__2_532_);
v___x_533_ = lean_box(0);
v___x_534_ = lean_apply_1(v_h__1_531_, v___x_533_);
return v___x_534_;
}
else
{
lean_object* v_val_535_; lean_object* v___x_536_; 
lean_dec(v_h__1_531_);
v_val_535_ = lean_ctor_get(v_unit_530_, 0);
lean_inc(v_val_535_);
lean_dec_ref_known(v_unit_530_, 1);
v___x_536_ = lean_apply_1(v_h__2_532_, v_val_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints_match__3_splitter(lean_object* v_motive_537_, lean_object* v_unit_538_, lean_object* v_h__1_539_, lean_object* v_h__2_540_){
_start:
{
if (lean_obj_tag(v_unit_538_) == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec(v_h__2_540_);
v___x_541_ = lean_box(0);
v___x_542_ = lean_apply_1(v_h__1_539_, v___x_541_);
return v___x_542_;
}
else
{
lean_object* v_val_543_; lean_object* v___x_544_; 
lean_dec(v_h__1_539_);
v_val_543_ = lean_ctor_get(v_unit_538_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v_unit_538_, 1);
v___x_544_ = lean_apply_1(v_h__2_540_, v_val_543_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_545_, lean_object* v_h__1_546_, lean_object* v_h__2_547_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_h__1_546_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_apply_1(v_h__2_547_, v___x_548_);
return v___x_549_;
}
else
{
lean_object* v_val_550_; lean_object* v___x_551_; 
lean_dec(v_h__2_547_);
v_val_550_ = lean_ctor_get(v_x_545_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v_x_545_, 1);
v___x_551_ = lean_apply_1(v_h__1_546_, v_val_550_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_552_, lean_object* v_motive_553_, lean_object* v_x_554_, lean_object* v_h__1_555_, lean_object* v_h__2_556_){
_start:
{
if (lean_obj_tag(v_x_554_) == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v_h__1_555_);
v___x_557_ = lean_box(0);
v___x_558_ = lean_apply_1(v_h__2_556_, v___x_557_);
return v___x_558_;
}
else
{
lean_object* v_val_559_; lean_object* v___x_560_; 
lean_dec(v_h__2_556_);
v_val_559_ = lean_ctor_get(v_x_554_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v_x_554_, 1);
v___x_560_ = lean_apply_1(v_h__1_555_, v_val_559_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__32_splitter___redArg(lean_object* v_ret_561_, lean_object* v_h__1_562_, lean_object* v_h__2_563_, lean_object* v_h__3_564_){
_start:
{
switch(lean_obj_tag(v_ret_561_))
{
case 0:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v_h__3_564_);
lean_dec(v_h__1_562_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_apply_1(v_h__2_563_, v___x_565_);
return v___x_566_;
}
case 1:
{
lean_object* v_assign_567_; lean_object* v___x_568_; 
lean_dec(v_h__2_563_);
lean_dec(v_h__1_562_);
v_assign_567_ = lean_ctor_get(v_ret_561_, 0);
lean_inc_ref(v_assign_567_);
lean_dec_ref_known(v_ret_561_, 1);
v___x_568_ = lean_apply_1(v_h__3_564_, v_assign_567_);
return v___x_568_;
}
default: 
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_h__3_564_);
lean_dec(v_h__2_563_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_apply_1(v_h__1_562_, v___x_569_);
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1__32_splitter(lean_object* v_motive_571_, lean_object* v_ret_572_, lean_object* v_h__1_573_, lean_object* v_h__2_574_, lean_object* v_h__3_575_){
_start:
{
switch(lean_obj_tag(v_ret_572_))
{
case 0:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_h__3_575_);
lean_dec(v_h__1_573_);
v___x_576_ = lean_box(0);
v___x_577_ = lean_apply_1(v_h__2_574_, v___x_576_);
return v___x_577_;
}
case 1:
{
lean_object* v_assign_578_; lean_object* v___x_579_; 
lean_dec(v_h__2_574_);
lean_dec(v_h__1_573_);
v_assign_578_ = lean_ctor_get(v_ret_572_, 0);
lean_inc_ref(v_assign_578_);
lean_dec_ref_known(v_ret_572_, 1);
v___x_579_ = lean_apply_1(v_h__3_575_, v_assign_578_);
return v___x_579_;
}
default: 
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_h__3_575_);
lean_dec(v_h__2_574_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_apply_1(v_h__1_573_, v___x_580_);
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter___redArg(lean_object* v_x_582_, lean_object* v_h__1_583_, lean_object* v_h__2_584_, lean_object* v_h__3_585_){
_start:
{
switch(lean_obj_tag(v_x_582_))
{
case 0:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_h__3_585_);
lean_dec(v_h__2_584_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_apply_1(v_h__1_583_, v___x_586_);
return v___x_587_;
}
case 1:
{
lean_object* v_assign_588_; lean_object* v___x_589_; 
lean_dec(v_h__3_585_);
lean_dec(v_h__1_583_);
v_assign_588_ = lean_ctor_get(v_x_582_, 0);
lean_inc_ref(v_assign_588_);
lean_dec_ref_known(v_x_582_, 1);
v___x_589_ = lean_apply_1(v_h__2_584_, v_assign_588_);
return v___x_589_;
}
default: 
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec(v_h__2_584_);
lean_dec(v_h__1_583_);
v___x_590_ = lean_box(0);
v___x_591_ = lean_apply_1(v_h__3_585_, v___x_590_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_propagateHints__spec_match__1_splitter(lean_object* v_motive_592_, lean_object* v_x_593_, lean_object* v_h__1_594_, lean_object* v_h__2_595_, lean_object* v_h__3_596_){
_start:
{
switch(lean_obj_tag(v_x_593_))
{
case 0:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v_h__3_596_);
lean_dec(v_h__2_595_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_apply_1(v_h__1_594_, v___x_597_);
return v___x_598_;
}
case 1:
{
lean_object* v_assign_599_; lean_object* v___x_600_; 
lean_dec(v_h__3_596_);
lean_dec(v_h__1_594_);
v_assign_599_ = lean_ctor_get(v_x_593_, 0);
lean_inc_ref(v_assign_599_);
lean_dec_ref_known(v_x_593_, 1);
v___x_600_ = lean_apply_1(v_h__2_595_, v_assign_599_);
return v___x_600_;
}
default: 
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_h__2_595_);
lean_dec(v_h__1_594_);
v___x_601_ = lean_box(0);
v___x_602_ = lean_apply_1(v_h__3_596_, v___x_601_);
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter___redArg(lean_object* v_x_603_, lean_object* v_h__1_604_, lean_object* v_h__2_605_){
_start:
{
if (lean_obj_tag(v_x_603_) == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v_h__2_605_);
v___x_606_ = lean_box(0);
v___x_607_ = lean_apply_1(v_h__1_604_, v___x_606_);
return v___x_607_;
}
else
{
lean_object* v___x_608_; 
lean_dec(v_h__1_604_);
v___x_608_ = lean_apply_2(v_h__2_605_, v_x_603_, lean_box(0));
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Rup_0__Std_Tactic_BVDecide_LRAT_Internal_State_checkPropagate_match__1_splitter(lean_object* v_motive_609_, lean_object* v_x_610_, lean_object* v_h__1_611_, lean_object* v_h__2_612_){
_start:
{
if (lean_obj_tag(v_x_610_) == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_h__2_612_);
v___x_613_ = lean_box(0);
v___x_614_ = lean_apply_1(v_h__1_611_, v___x_613_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; 
lean_dec(v_h__1_611_);
v___x_615_ = lean_apply_2(v_h__2_612_, v_x_610_, lean_box(0));
return v___x_615_;
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
