// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic
// Imports: public import Init.Data.String.Basic public import Init.Data.Hashable
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_Gate_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqGate(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqGate___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableGate_hash(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableGate_hash___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_instHashableGate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instHashableGate_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_instHashableGate___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableGate___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_instHashableGate = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableGate___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_Gate_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "&&"};
static const lean_object* l_Std_Tactic_BVDecide_Gate_toString___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_Gate_toString___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_Gate_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "^^"};
static const lean_object* l_Std_Tactic_BVDecide_Gate_toString___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_Gate_toString___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_Gate_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=="};
static const lean_object* l_Std_Tactic_BVDecide_Gate_toString___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_Gate_toString___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_Gate_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "||"};
static const lean_object* l_Std_Tactic_BVDecide_Gate_toString___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_Gate_toString___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toString(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toString___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_Gate_eval(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBoolExpr_hash(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr(lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "(if "};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_Gate_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_Tactic_BVDecide_Gate_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Tactic_BVDecide_Gate_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Tactic_BVDecide_Gate_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_Gate_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_Tactic_BVDecide_Gate_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Tactic_BVDecide_Gate_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___redArg(lean_object* v_and_24_){
_start:
{
lean_inc(v_and_24_);
return v_and_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___redArg___boxed(lean_object* v_and_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Tactic_BVDecide_Gate_and_elim___redArg(v_and_25_);
lean_dec(v_and_25_);
return v_res_26_;
}
}
lean_object* l_Std_Tactic_BVDecide_Gate_and_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_and_30_){
_start:
{
lean_inc(v_and_30_);
return v_and_30_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_Gate_and_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_and_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Tactic_BVDecide_Gate_and_elim(lean_box(0), v_t_28_, lean_box(0), v_and_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_and_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_Tactic_BVDecide_Gate_and_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_and_35_);
lean_dec(v_and_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___redArg(lean_object* v_xor_38_){
_start:
{
lean_inc(v_xor_38_);
return v_xor_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___redArg___boxed(lean_object* v_xor_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Tactic_BVDecide_Gate_xor_elim___redArg(v_xor_39_);
lean_dec(v_xor_39_);
return v_res_40_;
}
}
lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_xor_44_){
_start:
{
lean_inc(v_xor_44_);
return v_xor_44_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_Gate_xor_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_xor_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_Tactic_BVDecide_Gate_xor_elim(lean_box(0), v_t_42_, lean_box(0), v_xor_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_xor_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_Tactic_BVDecide_Gate_xor_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_xor_49_);
lean_dec(v_xor_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___redArg(lean_object* v_beq_52_){
_start:
{
lean_inc(v_beq_52_);
return v_beq_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___redArg___boxed(lean_object* v_beq_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_Tactic_BVDecide_Gate_beq_elim___redArg(v_beq_53_);
lean_dec(v_beq_53_);
return v_res_54_;
}
}
lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_beq_58_){
_start:
{
lean_inc(v_beq_58_);
return v_beq_58_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_Gate_beq_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_beq_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Std_Tactic_BVDecide_Gate_beq_elim(lean_box(0), v_t_56_, lean_box(0), v_beq_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_beq_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Std_Tactic_BVDecide_Gate_beq_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_beq_63_);
lean_dec(v_beq_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___redArg(lean_object* v_or_66_){
_start:
{
lean_inc(v_or_66_);
return v_or_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___redArg___boxed(lean_object* v_or_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_Tactic_BVDecide_Gate_or_elim___redArg(v_or_67_);
lean_dec(v_or_67_);
return v_res_68_;
}
}
lean_object* l_Std_Tactic_BVDecide_Gate_or_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_or_72_){
_start:
{
lean_inc(v_or_72_);
return v_or_72_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_Gate_or_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_70_ = stack[1].m_num;
lean_object* v_or_72_ = stack[3].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Std_Tactic_BVDecide_Gate_or_elim(lean_box(0), v_t_70_, lean_box(0), v_or_72_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_or_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l_Std_Tactic_BVDecide_Gate_or_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_or_77_);
lean_dec(v_or_77_);
return v_res_79_;
}
}
uint8_t l_Std_Tactic_BVDecide_Gate_ofNat(lean_object* v_n_80_){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_dec_le(v_n_80_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(2u);
v___x_84_ = lean_nat_dec_le(v_n_80_, v___x_83_);
if (v___x_84_ == 0)
{
uint8_t v___x_85_; 
v___x_85_ = 3;
return v___x_85_;
}
else
{
uint8_t v___x_86_; 
v___x_86_ = 2;
return v___x_86_;
}
}
else
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_nat_dec_le(v_n_80_, v___x_87_);
if (v___x_88_ == 0)
{
uint8_t v___x_89_; 
v___x_89_ = 1;
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_Gate_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_80_ = stack[0].m_obj;
uint8_t v_res_91_;
v_res_91_ = l_Std_Tactic_BVDecide_Gate_ofNat(v_n_80_);
stack->m_num = v_res_91_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ofNat___boxed(lean_object* v_n_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Std_Tactic_BVDecide_Gate_ofNat(v_n_92_);
lean_dec(v_n_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
uint8_t l_Std_Tactic_BVDecide_instDecidableEqGate(uint8_t v_x_95_, uint8_t v_y_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_97_ = lean_box(v_x_95_);
v___x_98_ = lean_obj_tag_nat(v___x_97_);
lean_dec(v___x_97_);
v___x_99_ = lean_box(v_y_96_);
v___x_100_ = lean_obj_tag_nat(v___x_99_);
lean_dec(v___x_99_);
v___x_101_ = lean_nat_dec_eq(v___x_98_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqGate_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_95_ = stack[0].m_num;
uint8_t v_y_96_ = stack[1].m_num;
uint8_t v_res_102_;
v_res_102_ = l_Std_Tactic_BVDecide_instDecidableEqGate(v_x_95_, v_y_96_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqGate___boxed(lean_object* v_x_103_, lean_object* v_y_104_){
_start:
{
uint8_t v_x_23__boxed_105_; uint8_t v_y_24__boxed_106_; uint8_t v_res_107_; lean_object* v_r_108_; 
v_x_23__boxed_105_ = lean_unbox(v_x_103_);
v_y_24__boxed_106_ = lean_unbox(v_y_104_);
v_res_107_ = l_Std_Tactic_BVDecide_instDecidableEqGate(v_x_23__boxed_105_, v_y_24__boxed_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
uint64_t l_Std_Tactic_BVDecide_instHashableGate_hash(uint8_t v_x_109_){
_start:
{
switch(v_x_109_)
{
case 0:
{
uint64_t v___x_110_; 
v___x_110_ = 0ULL;
return v___x_110_;
}
case 1:
{
uint64_t v___x_111_; 
v___x_111_ = 1ULL;
return v___x_111_;
}
case 2:
{
uint64_t v___x_112_; 
v___x_112_ = 2ULL;
return v___x_112_;
}
default: 
{
uint64_t v___x_113_; 
v___x_113_ = 3ULL;
return v___x_113_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instHashableGate_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_109_ = stack[0].m_num;
uint64_t v_res_114_;
v_res_114_ = l_Std_Tactic_BVDecide_instHashableGate_hash(v_x_109_);
stack->m_num = v_res_114_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableGate_hash___boxed(lean_object* v_x_115_){
_start:
{
uint8_t v_x_52__boxed_116_; uint64_t v_res_117_; lean_object* v_r_118_; 
v_x_52__boxed_116_ = lean_unbox(v_x_115_);
v_res_117_ = l_Std_Tactic_BVDecide_instHashableGate_hash(v_x_52__boxed_116_);
v_r_118_ = lean_box_uint64(v_res_117_);
return v_r_118_;
}
}
lean_object* l_Std_Tactic_BVDecide_Gate_toString(uint8_t v_x_125_){
_start:
{
switch(v_x_125_)
{
case 0:
{
lean_object* v___x_126_; 
v___x_126_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__0));
return v___x_126_;
}
case 1:
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__1));
return v___x_127_;
}
case 2:
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__2));
return v___x_128_;
}
default: 
{
lean_object* v___x_129_; 
v___x_129_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__3));
return v___x_129_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_Gate_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_125_ = stack[0].m_num;
lean_object* v_res_130_;
v_res_130_ = l_Std_Tactic_BVDecide_Gate_toString(v_x_125_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toString___boxed(lean_object* v_x_131_){
_start:
{
uint8_t v_x_40__boxed_132_; lean_object* v_res_133_; 
v_x_40__boxed_132_ = lean_unbox(v_x_131_);
v_res_133_ = l_Std_Tactic_BVDecide_Gate_toString(v_x_40__boxed_132_);
return v_res_133_;
}
}
uint8_t l_Std_Tactic_BVDecide_Gate_eval(uint8_t v_x_134_, uint8_t v_a_135_, uint8_t v_a_136_){
_start:
{
switch(v_x_134_)
{
case 0:
{
if (v_a_135_ == 0)
{
return v_a_135_;
}
else
{
return v_a_136_;
}
}
case 1:
{
if (v_a_136_ == 0)
{
return v_a_135_;
}
else
{
if (v_a_135_ == 0)
{
return v_a_136_;
}
else
{
uint8_t v___x_137_; 
v___x_137_ = 0;
return v___x_137_;
}
}
}
case 2:
{
if (v_a_136_ == 0)
{
if (v_a_135_ == 0)
{
uint8_t v___x_138_; 
v___x_138_ = 1;
return v___x_138_;
}
else
{
return v_a_136_;
}
}
else
{
return v_a_135_;
}
}
default: 
{
if (v_a_135_ == 0)
{
return v_a_136_;
}
else
{
return v_a_135_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_Gate_eval_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_134_ = stack[0].m_num;
uint8_t v_a_135_ = stack[1].m_num;
uint8_t v_a_136_ = stack[2].m_num;
uint8_t v_res_139_;
v_res_139_ = l_Std_Tactic_BVDecide_Gate_eval(v_x_134_, v_a_135_, v_a_136_);
stack->m_num = v_res_139_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_eval___boxed(lean_object* v_x_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
uint8_t v_x_179__boxed_143_; uint8_t v_a_180__boxed_144_; uint8_t v_a_181__boxed_145_; uint8_t v_res_146_; lean_object* v_r_147_; 
v_x_179__boxed_143_ = lean_unbox(v_x_140_);
v_a_180__boxed_144_ = lean_unbox(v_a_141_);
v_a_181__boxed_145_ = lean_unbox(v_a_142_);
v_res_146_ = l_Std_Tactic_BVDecide_Gate_eval(v_x_179__boxed_143_, v_a_180__boxed_144_, v_a_181__boxed_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl___redArg(lean_object* v_x_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_obj_tag_nat(v_x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl___redArg___boxed(lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl___redArg(v_x_150_);
lean_dec_ref(v_x_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl(lean_object* v_00_u03b1_152_, lean_object* v_x_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_tag_nat(v_x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl___boxed(lean_object* v_00_u03b1_155_, lean_object* v_x_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl(v_00_u03b1_155_, v_x_156_);
lean_dec_ref(v_x_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(lean_object* v_t_158_, lean_object* v_k_159_){
_start:
{
switch(lean_obj_tag(v_t_158_))
{
case 0:
{
lean_object* v_a_160_; lean_object* v___x_161_; 
v_a_160_ = lean_ctor_get(v_t_158_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v_t_158_, 1);
v___x_161_ = lean_apply_1(v_k_159_, v_a_160_);
return v___x_161_;
}
case 1:
{
uint8_t v_a_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_a_162_ = lean_ctor_get_uint8(v_t_158_, 0);
lean_dec_ref_known(v_t_158_, 0);
v___x_163_ = lean_box(v_a_162_);
v___x_164_ = lean_apply_1(v_k_159_, v___x_163_);
return v___x_164_;
}
case 2:
{
lean_object* v_a_165_; lean_object* v___x_166_; 
v_a_165_ = lean_ctor_get(v_t_158_, 0);
lean_inc_ref(v_a_165_);
lean_dec_ref_known(v_t_158_, 1);
v___x_166_ = lean_apply_1(v_k_159_, v_a_165_);
return v___x_166_;
}
case 3:
{
uint8_t v_a_167_; lean_object* v_a_168_; lean_object* v_a_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_a_167_ = lean_ctor_get_uint8(v_t_158_, sizeof(void*)*2);
v_a_168_ = lean_ctor_get(v_t_158_, 0);
lean_inc_ref(v_a_168_);
v_a_169_ = lean_ctor_get(v_t_158_, 1);
lean_inc_ref(v_a_169_);
lean_dec_ref_known(v_t_158_, 2);
v___x_170_ = lean_box(v_a_167_);
v___x_171_ = lean_apply_3(v_k_159_, v___x_170_, v_a_168_, v_a_169_);
return v___x_171_;
}
default: 
{
lean_object* v_a_172_; lean_object* v_a_173_; lean_object* v_a_174_; lean_object* v___x_175_; 
v_a_172_ = lean_ctor_get(v_t_158_, 0);
lean_inc_ref(v_a_172_);
v_a_173_ = lean_ctor_get(v_t_158_, 1);
lean_inc_ref(v_a_173_);
v_a_174_ = lean_ctor_get(v_t_158_, 2);
lean_inc_ref(v_a_174_);
lean_dec_ref_known(v_t_158_, 3);
v___x_175_ = lean_apply_3(v_k_159_, v_a_172_, v_a_173_, v_a_174_);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim(lean_object* v_00_u03b1_176_, lean_object* v_motive_177_, lean_object* v_ctorIdx_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_k_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_179_, v_k_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___boxed(lean_object* v_00_u03b1_183_, lean_object* v_motive_184_, lean_object* v_ctorIdx_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_k_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim(v_00_u03b1_183_, v_motive_184_, v_ctorIdx_185_, v_t_186_, v_h_187_, v_k_188_);
lean_dec(v_ctorIdx_185_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim___redArg(lean_object* v_t_190_, lean_object* v_literal_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_190_, v_literal_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim(lean_object* v_00_u03b1_193_, lean_object* v_motive_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_literal_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_195_, v_literal_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim___redArg(lean_object* v_t_199_, lean_object* v_const_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_199_, v_const_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim(lean_object* v_00_u03b1_202_, lean_object* v_motive_203_, lean_object* v_t_204_, lean_object* v_h_205_, lean_object* v_const_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_204_, v_const_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim___redArg(lean_object* v_t_208_, lean_object* v_not_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_208_, v_not_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim(lean_object* v_00_u03b1_211_, lean_object* v_motive_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_not_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_213_, v_not_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim___redArg(lean_object* v_t_217_, lean_object* v_gate_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_217_, v_gate_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim(lean_object* v_00_u03b1_220_, lean_object* v_motive_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_gate_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_222_, v_gate_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim___redArg(lean_object* v_t_226_, lean_object* v_ite_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_226_, v_ite_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim(lean_object* v_00_u03b1_229_, lean_object* v_motive_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_ite_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_231_, v_ite_233_);
return v___x_234_;
}
}
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(lean_object* v_inst_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
switch(lean_obj_tag(v_x_236_))
{
case 0:
{
if (lean_obj_tag(v_x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v_a_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_a_238_ = lean_ctor_get(v_x_236_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v_x_236_, 1);
v_a_239_ = lean_ctor_get(v_x_237_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v_x_237_, 1);
v___x_240_ = lean_apply_2(v_inst_235_, v_a_238_, v_a_239_);
v___x_241_ = lean_unbox(v___x_240_);
return v___x_241_;
}
else
{
uint8_t v___x_242_; 
lean_dec_ref_known(v_x_236_, 1);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_inst_235_);
v___x_242_ = 0;
return v___x_242_;
}
}
case 1:
{
lean_dec_ref(v_inst_235_);
if (lean_obj_tag(v_x_237_) == 1)
{
uint8_t v_a_243_; 
v_a_243_ = lean_ctor_get_uint8(v_x_237_, 0);
lean_dec_ref_known(v_x_237_, 0);
if (v_a_243_ == 0)
{
uint8_t v_a_244_; 
v_a_244_ = lean_ctor_get_uint8(v_x_236_, 0);
lean_dec_ref_known(v_x_236_, 0);
if (v_a_244_ == 0)
{
uint8_t v___x_245_; 
v___x_245_ = 1;
return v___x_245_;
}
else
{
return v_a_243_;
}
}
else
{
uint8_t v_a_246_; 
v_a_246_ = lean_ctor_get_uint8(v_x_236_, 0);
lean_dec_ref_known(v_x_236_, 0);
return v_a_246_;
}
}
else
{
uint8_t v___x_247_; 
lean_dec_ref_known(v_x_236_, 0);
lean_dec_ref(v_x_237_);
v___x_247_ = 0;
return v___x_247_;
}
}
case 2:
{
if (lean_obj_tag(v_x_237_) == 2)
{
lean_object* v_a_248_; lean_object* v_a_249_; 
v_a_248_ = lean_ctor_get(v_x_236_, 0);
lean_inc_ref(v_a_248_);
lean_dec_ref_known(v_x_236_, 1);
v_a_249_ = lean_ctor_get(v_x_237_, 0);
lean_inc_ref(v_a_249_);
lean_dec_ref_known(v_x_237_, 1);
v_x_236_ = v_a_248_;
v_x_237_ = v_a_249_;
goto _start;
}
else
{
uint8_t v___x_251_; 
lean_dec_ref_known(v_x_236_, 1);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_inst_235_);
v___x_251_ = 0;
return v___x_251_;
}
}
case 3:
{
if (lean_obj_tag(v_x_237_) == 3)
{
uint8_t v_a_252_; lean_object* v_a_253_; lean_object* v_a_254_; uint8_t v_a_255_; lean_object* v_a_256_; lean_object* v_a_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_a_252_ = lean_ctor_get_uint8(v_x_236_, sizeof(void*)*2);
v_a_253_ = lean_ctor_get(v_x_236_, 0);
lean_inc_ref(v_a_253_);
v_a_254_ = lean_ctor_get(v_x_236_, 1);
lean_inc_ref(v_a_254_);
lean_dec_ref_known(v_x_236_, 2);
v_a_255_ = lean_ctor_get_uint8(v_x_237_, sizeof(void*)*2);
v_a_256_ = lean_ctor_get(v_x_237_, 0);
lean_inc_ref(v_a_256_);
v_a_257_ = lean_ctor_get(v_x_237_, 1);
lean_inc_ref(v_a_257_);
lean_dec_ref_known(v_x_237_, 2);
v___x_258_ = lean_box(v_a_252_);
v___x_259_ = lean_obj_tag_nat(v___x_258_);
lean_dec(v___x_258_);
v___x_260_ = lean_box(v_a_255_);
v___x_261_ = lean_obj_tag_nat(v___x_260_);
lean_dec(v___x_260_);
v___x_262_ = lean_nat_dec_eq(v___x_259_, v___x_261_);
if (v___x_262_ == 0)
{
lean_dec_ref(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec_ref(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec_ref(v_inst_235_);
return v___x_262_;
}
else
{
uint8_t v_inst_263_; 
lean_inc_ref(v_inst_235_);
v_inst_263_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_235_, v_a_253_, v_a_256_);
if (v_inst_263_ == 0)
{
lean_dec_ref(v_a_257_);
lean_dec_ref(v_a_254_);
lean_dec_ref(v_inst_235_);
return v_inst_263_;
}
else
{
v_x_236_ = v_a_254_;
v_x_237_ = v_a_257_;
goto _start;
}
}
}
else
{
uint8_t v___x_265_; 
lean_dec_ref_known(v_x_236_, 2);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_inst_235_);
v___x_265_ = 0;
return v___x_265_;
}
}
default: 
{
if (lean_obj_tag(v_x_237_) == 4)
{
lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v_a_268_; lean_object* v_a_269_; lean_object* v_a_270_; lean_object* v_a_271_; uint8_t v_inst_272_; 
v_a_266_ = lean_ctor_get(v_x_236_, 0);
lean_inc_ref(v_a_266_);
v_a_267_ = lean_ctor_get(v_x_236_, 1);
lean_inc_ref(v_a_267_);
v_a_268_ = lean_ctor_get(v_x_236_, 2);
lean_inc_ref(v_a_268_);
lean_dec_ref_known(v_x_236_, 3);
v_a_269_ = lean_ctor_get(v_x_237_, 0);
lean_inc_ref(v_a_269_);
v_a_270_ = lean_ctor_get(v_x_237_, 1);
lean_inc_ref(v_a_270_);
v_a_271_ = lean_ctor_get(v_x_237_, 2);
lean_inc_ref(v_a_271_);
lean_dec_ref_known(v_x_237_, 3);
lean_inc_ref(v_inst_235_);
v_inst_272_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_235_, v_a_266_, v_a_269_);
if (v_inst_272_ == 0)
{
lean_dec_ref(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec_ref(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec_ref(v_inst_235_);
return v_inst_272_;
}
else
{
uint8_t v_inst_273_; 
lean_inc_ref(v_inst_235_);
v_inst_273_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_235_, v_a_267_, v_a_270_);
if (v_inst_273_ == 0)
{
lean_dec_ref(v_a_271_);
lean_dec_ref(v_a_268_);
lean_dec_ref(v_inst_235_);
return v_inst_273_;
}
else
{
v_x_236_ = v_a_268_;
v_x_237_ = v_a_271_;
goto _start;
}
}
}
else
{
uint8_t v___x_275_; 
lean_dec_ref_known(v_x_236_, 3);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_inst_235_);
v___x_275_ = 0;
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_235_ = stack[0].m_obj;
lean_object* v_x_236_ = stack[1].m_obj;
lean_object* v_x_237_ = stack[2].m_obj;
uint8_t v_res_276_;
v_res_276_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_235_, v_x_236_, v_x_237_);
stack->m_num = v_res_276_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg___boxed(lean_object* v_inst_277_, lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_277_, v_x_278_, v_x_279_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq(lean_object* v_00_u03b1_282_, lean_object* v_inst_283_, lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_283_, v_x_284_, v_x_285_);
return v___x_286_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_283_ = stack[1].m_obj;
lean_object* v_x_284_ = stack[2].m_obj;
lean_object* v_x_285_ = stack[3].m_obj;
uint8_t v_res_287_;
v_res_287_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq(lean_box(0), v_inst_283_, v_x_284_, v_x_285_);
stack->m_num = v_res_287_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___boxed(lean_object* v_00_u03b1_288_, lean_object* v_inst_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq(v_00_u03b1_288_, v_inst_289_, v_x_290_, v_x_291_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg(lean_object* v_inst_294_, lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_294_, v_x_295_, v_x_296_);
return v___x_297_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_294_ = stack[0].m_obj;
lean_object* v_x_295_ = stack[1].m_obj;
lean_object* v_x_296_ = stack[2].m_obj;
uint8_t v_res_298_;
v_res_298_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg(v_inst_294_, v_x_295_, v_x_296_);
stack->m_num = v_res_298_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg___boxed(lean_object* v_inst_299_, lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg(v_inst_299_, v_x_300_, v_x_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr(lean_object* v_00_u03b1_304_, lean_object* v_inst_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
uint8_t v___x_308_; 
v___x_308_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_305_, v_x_306_, v_x_307_);
return v___x_308_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_305_ = stack[1].m_obj;
lean_object* v_x_306_ = stack[2].m_obj;
lean_object* v_x_307_ = stack[3].m_obj;
uint8_t v_res_309_;
v_res_309_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr(lean_box(0), v_inst_305_, v_x_306_, v_x_307_);
stack->m_num = v_res_309_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___boxed(lean_object* v_00_u03b1_310_, lean_object* v_inst_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr(v_00_u03b1_310_, v_inst_311_, v_x_312_, v_x_313_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
uint64_t l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(lean_object* v_inst_316_, lean_object* v_x_317_){
_start:
{
switch(lean_obj_tag(v_x_317_))
{
case 0:
{
lean_object* v_a_318_; uint64_t v___x_319_; lean_object* v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; 
v_a_318_ = lean_ctor_get(v_x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v_x_317_, 1);
v___x_319_ = 0ULL;
v___x_320_ = lean_apply_1(v_inst_316_, v_a_318_);
v___x_321_ = lean_unbox_uint64(v___x_320_);
lean_dec_ref(v___x_320_);
v___x_322_ = lean_uint64_mix_hash(v___x_319_, v___x_321_);
return v___x_322_;
}
case 1:
{
uint8_t v_a_323_; 
lean_dec_ref(v_inst_316_);
v_a_323_ = lean_ctor_get_uint8(v_x_317_, 0);
lean_dec_ref_known(v_x_317_, 0);
if (v_a_323_ == 0)
{
uint64_t v___x_324_; 
v___x_324_ = 6634225825881527916ULL;
return v___x_324_;
}
else
{
uint64_t v___x_325_; 
v___x_325_ = 5934453574740161273ULL;
return v___x_325_;
}
}
case 2:
{
lean_object* v_a_326_; uint64_t v___x_327_; uint64_t v___x_328_; uint64_t v___x_329_; 
v_a_326_ = lean_ctor_get(v_x_317_, 0);
lean_inc_ref(v_a_326_);
lean_dec_ref_known(v_x_317_, 1);
v___x_327_ = 2ULL;
v___x_328_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_316_, v_a_326_);
v___x_329_ = lean_uint64_mix_hash(v___x_327_, v___x_328_);
return v___x_329_;
}
case 3:
{
uint8_t v_a_330_; lean_object* v_a_331_; lean_object* v_a_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; 
v_a_330_ = lean_ctor_get_uint8(v_x_317_, sizeof(void*)*2);
v_a_331_ = lean_ctor_get(v_x_317_, 0);
lean_inc_ref(v_a_331_);
v_a_332_ = lean_ctor_get(v_x_317_, 1);
lean_inc_ref(v_a_332_);
lean_dec_ref_known(v_x_317_, 2);
v___x_333_ = 3ULL;
v___x_334_ = l_Std_Tactic_BVDecide_instHashableGate_hash(v_a_330_);
v___x_335_ = lean_uint64_mix_hash(v___x_333_, v___x_334_);
lean_inc_ref(v_inst_316_);
v___x_336_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_316_, v_a_331_);
v___x_337_ = lean_uint64_mix_hash(v___x_335_, v___x_336_);
v___x_338_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_316_, v_a_332_);
v___x_339_ = lean_uint64_mix_hash(v___x_337_, v___x_338_);
return v___x_339_;
}
default: 
{
lean_object* v_a_340_; lean_object* v_a_341_; lean_object* v_a_342_; uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v___x_347_; uint64_t v___x_348_; uint64_t v___x_349_; 
v_a_340_ = lean_ctor_get(v_x_317_, 0);
lean_inc_ref(v_a_340_);
v_a_341_ = lean_ctor_get(v_x_317_, 1);
lean_inc_ref(v_a_341_);
v_a_342_ = lean_ctor_get(v_x_317_, 2);
lean_inc_ref(v_a_342_);
lean_dec_ref_known(v_x_317_, 3);
v___x_343_ = 4ULL;
lean_inc_ref_n(v_inst_316_, 2);
v___x_344_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_316_, v_a_340_);
v___x_345_ = lean_uint64_mix_hash(v___x_343_, v___x_344_);
v___x_346_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_316_, v_a_341_);
v___x_347_ = lean_uint64_mix_hash(v___x_345_, v___x_346_);
v___x_348_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_316_, v_a_342_);
v___x_349_ = lean_uint64_mix_hash(v___x_347_, v___x_348_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_316_ = stack[0].m_obj;
lean_object* v_x_317_ = stack[1].m_obj;
uint64_t v_res_350_;
v_res_350_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_316_, v_x_317_);
stack->m_num = v_res_350_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg___boxed(lean_object* v_inst_351_, lean_object* v_x_352_){
_start:
{
uint64_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_351_, v_x_352_);
v_r_354_ = lean_box_uint64(v_res_353_);
return v_r_354_;
}
}
uint64_t l_Std_Tactic_BVDecide_instHashableBoolExpr_hash(lean_object* v_00_u03b1_355_, lean_object* v_inst_356_, lean_object* v_x_357_){
_start:
{
uint64_t v___x_358_; 
v___x_358_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_356_, v_x_357_);
return v___x_358_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instHashableBoolExpr_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_356_ = stack[1].m_obj;
lean_object* v_x_357_ = stack[2].m_obj;
uint64_t v_res_359_;
v_res_359_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash(lean_box(0), v_inst_356_, v_x_357_);
stack->m_num = v_res_359_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___boxed(lean_object* v_00_u03b1_360_, lean_object* v_inst_361_, lean_object* v_x_362_){
_start:
{
uint64_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash(v_00_u03b1_360_, v_inst_361_, v_x_362_);
v_r_364_ = lean_box_uint64(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr___redArg(lean_object* v_inst_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___boxed), 3, 2);
lean_closure_set(v___x_366_, 0, lean_box(0));
lean_closure_set(v___x_366_, 1, v_inst_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr(lean_object* v_00_u03b1_367_, lean_object* v_inst_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___boxed), 3, 2);
lean_closure_set(v___x_369_, 0, lean_box(0));
lean_closure_set(v___x_369_, 1, v_inst_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(lean_object* v_inst_377_, lean_object* v_x_378_){
_start:
{
switch(lean_obj_tag(v_x_378_))
{
case 0:
{
lean_object* v_a_379_; lean_object* v___x_380_; 
v_a_379_ = lean_ctor_get(v_x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v_x_378_, 1);
v___x_380_ = lean_apply_1(v_inst_377_, v_a_379_);
return v___x_380_;
}
case 1:
{
uint8_t v_a_381_; 
lean_dec_ref(v_inst_377_);
v_a_381_ = lean_ctor_get_uint8(v_x_378_, 0);
lean_dec_ref_known(v_x_378_, 0);
if (v_a_381_ == 0)
{
lean_object* v___x_382_; 
v___x_382_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0));
return v___x_382_;
}
else
{
lean_object* v___x_383_; 
v___x_383_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1));
return v___x_383_;
}
}
case 2:
{
lean_object* v_a_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_a_384_ = lean_ctor_get(v_x_378_, 0);
lean_inc_ref(v_a_384_);
lean_dec_ref_known(v_x_378_, 1);
v___x_385_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2));
v___x_386_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_377_, v_a_384_);
v___x_387_ = lean_string_append(v___x_385_, v___x_386_);
lean_dec_ref(v___x_386_);
return v___x_387_;
}
case 3:
{
uint8_t v_a_388_; lean_object* v_a_389_; lean_object* v_a_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_a_388_ = lean_ctor_get_uint8(v_x_378_, sizeof(void*)*2);
v_a_389_ = lean_ctor_get(v_x_378_, 0);
lean_inc_ref(v_a_389_);
v_a_390_ = lean_ctor_get(v_x_378_, 1);
lean_inc_ref(v_a_390_);
lean_dec_ref_known(v_x_378_, 2);
v___x_391_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3));
lean_inc_ref(v_inst_377_);
v___x_392_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_377_, v_a_389_);
v___x_393_ = lean_string_append(v___x_391_, v___x_392_);
lean_dec_ref(v___x_392_);
v___x_394_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4));
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
v___x_396_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_388_);
v___x_397_ = lean_string_append(v___x_395_, v___x_396_);
lean_dec_ref(v___x_396_);
v___x_398_ = lean_string_append(v___x_397_, v___x_394_);
v___x_399_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_377_, v_a_390_);
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
lean_dec_ref(v___x_399_);
v___x_401_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5));
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
return v___x_402_;
}
default: 
{
lean_object* v_a_403_; lean_object* v_a_404_; lean_object* v_a_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_a_403_ = lean_ctor_get(v_x_378_, 0);
lean_inc_ref(v_a_403_);
v_a_404_ = lean_ctor_get(v_x_378_, 1);
lean_inc_ref(v_a_404_);
v_a_405_ = lean_ctor_get(v_x_378_, 2);
lean_inc_ref(v_a_405_);
lean_dec_ref_known(v_x_378_, 3);
v___x_406_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6));
lean_inc_ref_n(v_inst_377_, 2);
v___x_407_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_377_, v_a_403_);
v___x_408_ = lean_string_append(v___x_406_, v___x_407_);
lean_dec_ref(v___x_407_);
v___x_409_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4));
v___x_410_ = lean_string_append(v___x_408_, v___x_409_);
v___x_411_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_377_, v_a_404_);
v___x_412_ = lean_string_append(v___x_410_, v___x_411_);
lean_dec_ref(v___x_411_);
v___x_413_ = lean_string_append(v___x_412_, v___x_409_);
v___x_414_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_377_, v_a_405_);
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
lean_dec_ref(v___x_414_);
v___x_416_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5));
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString(lean_object* v_00_u03b1_418_, lean_object* v_inst_419_, lean_object* v_x_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_419_, v_x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString___redArg(lean_object* v_inst_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BoolExpr_toString), 3, 2);
lean_closure_set(v___x_423_, 0, lean_box(0));
lean_closure_set(v___x_423_, 1, v_inst_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString(lean_object* v_00_u03b1_424_, lean_object* v_inst_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BoolExpr_toString), 3, 2);
lean_closure_set(v___x_426_, 0, lean_box(0));
lean_closure_set(v___x_426_, 1, v_inst_425_);
return v___x_426_;
}
}
uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(lean_object* v_a_427_, lean_object* v_x_428_){
_start:
{
switch(lean_obj_tag(v_x_428_))
{
case 0:
{
lean_object* v_a_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_a_429_ = lean_ctor_get(v_x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v_x_428_, 1);
v___x_430_ = lean_apply_1(v_a_427_, v_a_429_);
v___x_431_ = lean_unbox(v___x_430_);
return v___x_431_;
}
case 1:
{
uint8_t v_a_432_; 
lean_dec_ref(v_a_427_);
v_a_432_ = lean_ctor_get_uint8(v_x_428_, 0);
lean_dec_ref_known(v_x_428_, 0);
return v_a_432_;
}
case 2:
{
lean_object* v_a_433_; uint8_t v___x_434_; 
v_a_433_ = lean_ctor_get(v_x_428_, 0);
lean_inc_ref(v_a_433_);
lean_dec_ref_known(v_x_428_, 1);
v___x_434_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_427_, v_a_433_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; 
v___x_435_ = 1;
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = 0;
return v___x_436_;
}
}
case 3:
{
uint8_t v_a_437_; lean_object* v_a_438_; lean_object* v_a_439_; uint8_t v___x_440_; uint8_t v___x_441_; uint8_t v___x_442_; 
v_a_437_ = lean_ctor_get_uint8(v_x_428_, sizeof(void*)*2);
v_a_438_ = lean_ctor_get(v_x_428_, 0);
lean_inc_ref(v_a_438_);
v_a_439_ = lean_ctor_get(v_x_428_, 1);
lean_inc_ref(v_a_439_);
lean_dec_ref_known(v_x_428_, 2);
lean_inc_ref(v_a_427_);
v___x_440_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_427_, v_a_438_);
v___x_441_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_427_, v_a_439_);
v___x_442_ = l_Std_Tactic_BVDecide_Gate_eval(v_a_437_, v___x_440_, v___x_441_);
return v___x_442_;
}
default: 
{
lean_object* v_a_443_; lean_object* v_a_444_; lean_object* v_a_445_; uint8_t v___x_446_; 
v_a_443_ = lean_ctor_get(v_x_428_, 0);
lean_inc_ref(v_a_443_);
v_a_444_ = lean_ctor_get(v_x_428_, 1);
lean_inc_ref(v_a_444_);
v_a_445_ = lean_ctor_get(v_x_428_, 2);
lean_inc_ref(v_a_445_);
lean_dec_ref_known(v_x_428_, 3);
lean_inc_ref(v_a_427_);
v___x_446_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_427_, v_a_443_);
if (v___x_446_ == 0)
{
lean_dec_ref(v_a_444_);
v_x_428_ = v_a_445_;
goto _start;
}
else
{
lean_dec_ref(v_a_445_);
v_x_428_ = v_a_444_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BoolExpr_eval___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_427_ = stack[0].m_obj;
lean_object* v_x_428_ = stack[1].m_obj;
uint8_t v_res_449_;
v_res_449_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_427_, v_x_428_);
stack->m_num = v_res_449_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___redArg___boxed(lean_object* v_a_450_, lean_object* v_x_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_450_, v_x_451_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval(lean_object* v_00_u03b1_454_, lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_455_, v_x_456_);
return v___x_457_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BoolExpr_eval_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_455_ = stack[1].m_obj;
lean_object* v_x_456_ = stack[2].m_obj;
uint8_t v_res_458_;
v_res_458_ = l_Std_Tactic_BVDecide_BoolExpr_eval(lean_box(0), v_a_455_, v_x_456_);
stack->m_num = v_res_458_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___boxed(lean_object* v_00_u03b1_459_, lean_object* v_a_460_, lean_object* v_x_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Std_Tactic_BVDecide_BoolExpr_eval(v_00_u03b1_459_, v_a_460_, v_x_461_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
