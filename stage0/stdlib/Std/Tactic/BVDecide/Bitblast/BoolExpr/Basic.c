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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Tactic_BVDecide_Gate_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Tactic_BVDecide_Gate_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Tactic_BVDecide_Gate_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___redArg(lean_object* v_and_22_){
_start:
{
lean_inc(v_and_22_);
return v_and_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___redArg___boxed(lean_object* v_and_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Tactic_BVDecide_Gate_and_elim___redArg(v_and_23_);
lean_dec(v_and_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_and_28_){
_start:
{
lean_inc(v_and_28_);
return v_and_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_and_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Tactic_BVDecide_Gate_and_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_and_32_);
lean_dec(v_and_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___redArg(lean_object* v_xor_35_){
_start:
{
lean_inc(v_xor_35_);
return v_xor_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___redArg___boxed(lean_object* v_xor_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Tactic_BVDecide_Gate_xor_elim___redArg(v_xor_36_);
lean_dec(v_xor_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_xor_41_){
_start:
{
lean_inc(v_xor_41_);
return v_xor_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_xor_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Tactic_BVDecide_Gate_xor_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_xor_45_);
lean_dec(v_xor_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___redArg(lean_object* v_beq_48_){
_start:
{
lean_inc(v_beq_48_);
return v_beq_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___redArg___boxed(lean_object* v_beq_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Tactic_BVDecide_Gate_beq_elim___redArg(v_beq_49_);
lean_dec(v_beq_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_beq_54_){
_start:
{
lean_inc(v_beq_54_);
return v_beq_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_beq_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Std_Tactic_BVDecide_Gate_beq_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_beq_58_);
lean_dec(v_beq_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___redArg(lean_object* v_or_61_){
_start:
{
lean_inc(v_or_61_);
return v_or_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___redArg___boxed(lean_object* v_or_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Std_Tactic_BVDecide_Gate_or_elim___redArg(v_or_62_);
lean_dec(v_or_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_or_67_){
_start:
{
lean_inc(v_or_67_);
return v_or_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_or_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Std_Tactic_BVDecide_Gate_or_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_or_71_);
lean_dec(v_or_71_);
return v_res_73_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_Gate_ofNat(lean_object* v_n_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_dec_le(v_n_74_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(2u);
v___x_78_ = lean_nat_dec_le(v_n_74_, v___x_77_);
if (v___x_78_ == 0)
{
uint8_t v___x_79_; 
v___x_79_ = 3;
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 2;
return v___x_80_;
}
}
else
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_nat_dec_le(v_n_74_, v___x_81_);
if (v___x_82_ == 0)
{
uint8_t v___x_83_; 
v___x_83_ = 1;
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ofNat___boxed(lean_object* v_n_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_Tactic_BVDecide_Gate_ofNat(v_n_85_);
lean_dec(v_n_85_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqGate(uint8_t v_x_88_, uint8_t v_y_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_90_ = lean_box(v_x_88_);
v___x_91_ = lean_obj_tag_nat(v___x_90_);
lean_dec(v___x_90_);
v___x_92_ = lean_box(v_y_89_);
v___x_93_ = lean_obj_tag_nat(v___x_92_);
lean_dec(v___x_92_);
v___x_94_ = lean_nat_dec_eq(v___x_91_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqGate___boxed(lean_object* v_x_95_, lean_object* v_y_96_){
_start:
{
uint8_t v_x_23__boxed_97_; uint8_t v_y_24__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_x_23__boxed_97_ = lean_unbox(v_x_95_);
v_y_24__boxed_98_ = lean_unbox(v_y_96_);
v_res_99_ = l_Std_Tactic_BVDecide_instDecidableEqGate(v_x_23__boxed_97_, v_y_24__boxed_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableGate_hash(uint8_t v_x_101_){
_start:
{
switch(v_x_101_)
{
case 0:
{
uint64_t v___x_102_; 
v___x_102_ = 0ULL;
return v___x_102_;
}
case 1:
{
uint64_t v___x_103_; 
v___x_103_ = 1ULL;
return v___x_103_;
}
case 2:
{
uint64_t v___x_104_; 
v___x_104_ = 2ULL;
return v___x_104_;
}
default: 
{
uint64_t v___x_105_; 
v___x_105_ = 3ULL;
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableGate_hash___boxed(lean_object* v_x_106_){
_start:
{
uint8_t v_x_52__boxed_107_; uint64_t v_res_108_; lean_object* v_r_109_; 
v_x_52__boxed_107_ = lean_unbox(v_x_106_);
v_res_108_ = l_Std_Tactic_BVDecide_instHashableGate_hash(v_x_52__boxed_107_);
v_r_109_ = lean_box_uint64(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toString(uint8_t v_x_116_){
_start:
{
switch(v_x_116_)
{
case 0:
{
lean_object* v___x_117_; 
v___x_117_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__0));
return v___x_117_;
}
case 1:
{
lean_object* v___x_118_; 
v___x_118_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__1));
return v___x_118_;
}
case 2:
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__2));
return v___x_119_;
}
default: 
{
lean_object* v___x_120_; 
v___x_120_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__3));
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toString___boxed(lean_object* v_x_121_){
_start:
{
uint8_t v_x_40__boxed_122_; lean_object* v_res_123_; 
v_x_40__boxed_122_ = lean_unbox(v_x_121_);
v_res_123_ = l_Std_Tactic_BVDecide_Gate_toString(v_x_40__boxed_122_);
return v_res_123_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_Gate_eval(uint8_t v_x_124_, uint8_t v_a_125_, uint8_t v_a_126_){
_start:
{
switch(v_x_124_)
{
case 0:
{
if (v_a_125_ == 0)
{
return v_a_125_;
}
else
{
return v_a_126_;
}
}
case 1:
{
if (v_a_126_ == 0)
{
return v_a_125_;
}
else
{
if (v_a_125_ == 0)
{
return v_a_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
}
}
case 2:
{
if (v_a_126_ == 0)
{
if (v_a_125_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = 1;
return v___x_128_;
}
else
{
return v_a_126_;
}
}
else
{
return v_a_125_;
}
}
default: 
{
if (v_a_125_ == 0)
{
return v_a_126_;
}
else
{
return v_a_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_eval___boxed(lean_object* v_x_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
uint8_t v_x_179__boxed_132_; uint8_t v_a_180__boxed_133_; uint8_t v_a_181__boxed_134_; uint8_t v_res_135_; lean_object* v_r_136_; 
v_x_179__boxed_132_ = lean_unbox(v_x_129_);
v_a_180__boxed_133_ = lean_unbox(v_a_130_);
v_a_181__boxed_134_ = lean_unbox(v_a_131_);
v_res_135_ = l_Std_Tactic_BVDecide_Gate_eval(v_x_179__boxed_132_, v_a_180__boxed_133_, v_a_181__boxed_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl___redArg(lean_object* v_x_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_tag_nat(v_x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl___redArg___boxed(lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl___redArg(v_x_139_);
lean_dec_ref(v_x_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl(lean_object* v_00_u03b1_141_, lean_object* v_x_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_tag_nat(v_x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl___boxed(lean_object* v_00_u03b1_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___impl(v_00_u03b1_144_, v_x_145_);
lean_dec_ref(v_x_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(lean_object* v_t_147_, lean_object* v_k_148_){
_start:
{
switch(lean_obj_tag(v_t_147_))
{
case 0:
{
lean_object* v_a_149_; lean_object* v___x_150_; 
v_a_149_ = lean_ctor_get(v_t_147_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v_t_147_, 1);
v___x_150_ = lean_apply_1(v_k_148_, v_a_149_);
return v___x_150_;
}
case 1:
{
uint8_t v_a_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_a_151_ = lean_ctor_get_uint8(v_t_147_, 0);
lean_dec_ref_known(v_t_147_, 0);
v___x_152_ = lean_box(v_a_151_);
v___x_153_ = lean_apply_1(v_k_148_, v___x_152_);
return v___x_153_;
}
case 2:
{
lean_object* v_a_154_; lean_object* v___x_155_; 
v_a_154_ = lean_ctor_get(v_t_147_, 0);
lean_inc_ref(v_a_154_);
lean_dec_ref_known(v_t_147_, 1);
v___x_155_ = lean_apply_1(v_k_148_, v_a_154_);
return v___x_155_;
}
case 3:
{
uint8_t v_a_156_; lean_object* v_a_157_; lean_object* v_a_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_a_156_ = lean_ctor_get_uint8(v_t_147_, sizeof(void*)*2);
v_a_157_ = lean_ctor_get(v_t_147_, 0);
lean_inc_ref(v_a_157_);
v_a_158_ = lean_ctor_get(v_t_147_, 1);
lean_inc_ref(v_a_158_);
lean_dec_ref_known(v_t_147_, 2);
v___x_159_ = lean_box(v_a_156_);
v___x_160_ = lean_apply_3(v_k_148_, v___x_159_, v_a_157_, v_a_158_);
return v___x_160_;
}
default: 
{
lean_object* v_a_161_; lean_object* v_a_162_; lean_object* v_a_163_; lean_object* v___x_164_; 
v_a_161_ = lean_ctor_get(v_t_147_, 0);
lean_inc_ref(v_a_161_);
v_a_162_ = lean_ctor_get(v_t_147_, 1);
lean_inc_ref(v_a_162_);
v_a_163_ = lean_ctor_get(v_t_147_, 2);
lean_inc_ref(v_a_163_);
lean_dec_ref_known(v_t_147_, 3);
v___x_164_ = lean_apply_3(v_k_148_, v_a_161_, v_a_162_, v_a_163_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim(lean_object* v_00_u03b1_165_, lean_object* v_motive_166_, lean_object* v_ctorIdx_167_, lean_object* v_t_168_, lean_object* v_h_169_, lean_object* v_k_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_168_, v_k_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___boxed(lean_object* v_00_u03b1_172_, lean_object* v_motive_173_, lean_object* v_ctorIdx_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_k_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim(v_00_u03b1_172_, v_motive_173_, v_ctorIdx_174_, v_t_175_, v_h_176_, v_k_177_);
lean_dec(v_ctorIdx_174_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim___redArg(lean_object* v_t_179_, lean_object* v_literal_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_179_, v_literal_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim(lean_object* v_00_u03b1_182_, lean_object* v_motive_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_literal_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_184_, v_literal_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim___redArg(lean_object* v_t_188_, lean_object* v_const_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_188_, v_const_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim(lean_object* v_00_u03b1_191_, lean_object* v_motive_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_const_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_193_, v_const_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim___redArg(lean_object* v_t_197_, lean_object* v_not_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_197_, v_not_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim(lean_object* v_00_u03b1_200_, lean_object* v_motive_201_, lean_object* v_t_202_, lean_object* v_h_203_, lean_object* v_not_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_202_, v_not_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim___redArg(lean_object* v_t_206_, lean_object* v_gate_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_206_, v_gate_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim(lean_object* v_00_u03b1_209_, lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_gate_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_211_, v_gate_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim___redArg(lean_object* v_t_215_, lean_object* v_ite_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_215_, v_ite_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim(lean_object* v_00_u03b1_218_, lean_object* v_motive_219_, lean_object* v_t_220_, lean_object* v_h_221_, lean_object* v_ite_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_220_, v_ite_222_);
return v___x_223_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(lean_object* v_inst_224_, lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
switch(lean_obj_tag(v_x_225_))
{
case 0:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v_a_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v_a_227_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v_x_225_, 1);
v_a_228_ = lean_ctor_get(v_x_226_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v_x_226_, 1);
v___x_229_ = lean_apply_2(v_inst_224_, v_a_227_, v_a_228_);
v___x_230_ = lean_unbox(v___x_229_);
return v___x_230_;
}
else
{
uint8_t v___x_231_; 
lean_dec_ref_known(v_x_225_, 1);
lean_dec_ref(v_x_226_);
lean_dec_ref(v_inst_224_);
v___x_231_ = 0;
return v___x_231_;
}
}
case 1:
{
lean_dec_ref(v_inst_224_);
if (lean_obj_tag(v_x_226_) == 1)
{
uint8_t v_a_232_; 
v_a_232_ = lean_ctor_get_uint8(v_x_226_, 0);
lean_dec_ref_known(v_x_226_, 0);
if (v_a_232_ == 0)
{
uint8_t v_a_233_; 
v_a_233_ = lean_ctor_get_uint8(v_x_225_, 0);
lean_dec_ref_known(v_x_225_, 0);
if (v_a_233_ == 0)
{
uint8_t v___x_234_; 
v___x_234_ = 1;
return v___x_234_;
}
else
{
return v_a_232_;
}
}
else
{
uint8_t v_a_235_; 
v_a_235_ = lean_ctor_get_uint8(v_x_225_, 0);
lean_dec_ref_known(v_x_225_, 0);
return v_a_235_;
}
}
else
{
uint8_t v___x_236_; 
lean_dec_ref_known(v_x_225_, 0);
lean_dec_ref(v_x_226_);
v___x_236_ = 0;
return v___x_236_;
}
}
case 2:
{
if (lean_obj_tag(v_x_226_) == 2)
{
lean_object* v_a_237_; lean_object* v_a_238_; 
v_a_237_ = lean_ctor_get(v_x_225_, 0);
lean_inc_ref(v_a_237_);
lean_dec_ref_known(v_x_225_, 1);
v_a_238_ = lean_ctor_get(v_x_226_, 0);
lean_inc_ref(v_a_238_);
lean_dec_ref_known(v_x_226_, 1);
v_x_225_ = v_a_237_;
v_x_226_ = v_a_238_;
goto _start;
}
else
{
uint8_t v___x_240_; 
lean_dec_ref_known(v_x_225_, 1);
lean_dec_ref(v_x_226_);
lean_dec_ref(v_inst_224_);
v___x_240_ = 0;
return v___x_240_;
}
}
case 3:
{
if (lean_obj_tag(v_x_226_) == 3)
{
uint8_t v_a_241_; lean_object* v_a_242_; lean_object* v_a_243_; uint8_t v_a_244_; lean_object* v_a_245_; lean_object* v_a_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_a_241_ = lean_ctor_get_uint8(v_x_225_, sizeof(void*)*2);
v_a_242_ = lean_ctor_get(v_x_225_, 0);
lean_inc_ref(v_a_242_);
v_a_243_ = lean_ctor_get(v_x_225_, 1);
lean_inc_ref(v_a_243_);
lean_dec_ref_known(v_x_225_, 2);
v_a_244_ = lean_ctor_get_uint8(v_x_226_, sizeof(void*)*2);
v_a_245_ = lean_ctor_get(v_x_226_, 0);
lean_inc_ref(v_a_245_);
v_a_246_ = lean_ctor_get(v_x_226_, 1);
lean_inc_ref(v_a_246_);
lean_dec_ref_known(v_x_226_, 2);
v___x_247_ = lean_box(v_a_241_);
v___x_248_ = lean_obj_tag_nat(v___x_247_);
lean_dec(v___x_247_);
v___x_249_ = lean_box(v_a_244_);
v___x_250_ = lean_obj_tag_nat(v___x_249_);
lean_dec(v___x_249_);
v___x_251_ = lean_nat_dec_eq(v___x_248_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec_ref(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec_ref(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec_ref(v_inst_224_);
return v___x_251_;
}
else
{
uint8_t v_inst_252_; 
lean_inc_ref(v_inst_224_);
v_inst_252_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_224_, v_a_242_, v_a_245_);
if (v_inst_252_ == 0)
{
lean_dec_ref(v_a_246_);
lean_dec_ref(v_a_243_);
lean_dec_ref(v_inst_224_);
return v_inst_252_;
}
else
{
v_x_225_ = v_a_243_;
v_x_226_ = v_a_246_;
goto _start;
}
}
}
else
{
uint8_t v___x_254_; 
lean_dec_ref_known(v_x_225_, 2);
lean_dec_ref(v_x_226_);
lean_dec_ref(v_inst_224_);
v___x_254_ = 0;
return v___x_254_;
}
}
default: 
{
if (lean_obj_tag(v_x_226_) == 4)
{
lean_object* v_a_255_; lean_object* v_a_256_; lean_object* v_a_257_; lean_object* v_a_258_; lean_object* v_a_259_; lean_object* v_a_260_; uint8_t v_inst_261_; 
v_a_255_ = lean_ctor_get(v_x_225_, 0);
lean_inc_ref(v_a_255_);
v_a_256_ = lean_ctor_get(v_x_225_, 1);
lean_inc_ref(v_a_256_);
v_a_257_ = lean_ctor_get(v_x_225_, 2);
lean_inc_ref(v_a_257_);
lean_dec_ref_known(v_x_225_, 3);
v_a_258_ = lean_ctor_get(v_x_226_, 0);
lean_inc_ref(v_a_258_);
v_a_259_ = lean_ctor_get(v_x_226_, 1);
lean_inc_ref(v_a_259_);
v_a_260_ = lean_ctor_get(v_x_226_, 2);
lean_inc_ref(v_a_260_);
lean_dec_ref_known(v_x_226_, 3);
lean_inc_ref(v_inst_224_);
v_inst_261_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_224_, v_a_255_, v_a_258_);
if (v_inst_261_ == 0)
{
lean_dec_ref(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec_ref(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec_ref(v_inst_224_);
return v_inst_261_;
}
else
{
uint8_t v_inst_262_; 
lean_inc_ref(v_inst_224_);
v_inst_262_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_224_, v_a_256_, v_a_259_);
if (v_inst_262_ == 0)
{
lean_dec_ref(v_a_260_);
lean_dec_ref(v_a_257_);
lean_dec_ref(v_inst_224_);
return v_inst_262_;
}
else
{
v_x_225_ = v_a_257_;
v_x_226_ = v_a_260_;
goto _start;
}
}
}
else
{
uint8_t v___x_264_; 
lean_dec_ref_known(v_x_225_, 3);
lean_dec_ref(v_x_226_);
lean_dec_ref(v_inst_224_);
v___x_264_ = 0;
return v___x_264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg___boxed(lean_object* v_inst_265_, lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_265_, v_x_266_, v_x_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq(lean_object* v_00_u03b1_270_, lean_object* v_inst_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_271_, v_x_272_, v_x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___boxed(lean_object* v_00_u03b1_275_, lean_object* v_inst_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq(v_00_u03b1_275_, v_inst_276_, v_x_277_, v_x_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg(lean_object* v_inst_281_, lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_281_, v_x_282_, v_x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg___boxed(lean_object* v_inst_285_, lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg(v_inst_285_, v_x_286_, v_x_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr(lean_object* v_00_u03b1_290_, lean_object* v_inst_291_, lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
uint8_t v___x_294_; 
v___x_294_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_291_, v_x_292_, v_x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___boxed(lean_object* v_00_u03b1_295_, lean_object* v_inst_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr(v_00_u03b1_295_, v_inst_296_, v_x_297_, v_x_298_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(lean_object* v_inst_301_, lean_object* v_x_302_){
_start:
{
switch(lean_obj_tag(v_x_302_))
{
case 0:
{
lean_object* v_a_303_; uint64_t v___x_304_; lean_object* v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; 
v_a_303_ = lean_ctor_get(v_x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v_x_302_, 1);
v___x_304_ = 0ULL;
v___x_305_ = lean_apply_1(v_inst_301_, v_a_303_);
v___x_306_ = lean_unbox_uint64(v___x_305_);
lean_dec_ref(v___x_305_);
v___x_307_ = lean_uint64_mix_hash(v___x_304_, v___x_306_);
return v___x_307_;
}
case 1:
{
uint8_t v_a_308_; 
lean_dec_ref(v_inst_301_);
v_a_308_ = lean_ctor_get_uint8(v_x_302_, 0);
lean_dec_ref_known(v_x_302_, 0);
if (v_a_308_ == 0)
{
uint64_t v___x_309_; 
v___x_309_ = 6634225825881527916ULL;
return v___x_309_;
}
else
{
uint64_t v___x_310_; 
v___x_310_ = 5934453574740161273ULL;
return v___x_310_;
}
}
case 2:
{
lean_object* v_a_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; 
v_a_311_ = lean_ctor_get(v_x_302_, 0);
lean_inc_ref(v_a_311_);
lean_dec_ref_known(v_x_302_, 1);
v___x_312_ = 2ULL;
v___x_313_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_301_, v_a_311_);
v___x_314_ = lean_uint64_mix_hash(v___x_312_, v___x_313_);
return v___x_314_;
}
case 3:
{
uint8_t v_a_315_; lean_object* v_a_316_; lean_object* v_a_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; 
v_a_315_ = lean_ctor_get_uint8(v_x_302_, sizeof(void*)*2);
v_a_316_ = lean_ctor_get(v_x_302_, 0);
lean_inc_ref(v_a_316_);
v_a_317_ = lean_ctor_get(v_x_302_, 1);
lean_inc_ref(v_a_317_);
lean_dec_ref_known(v_x_302_, 2);
v___x_318_ = 3ULL;
v___x_319_ = l_Std_Tactic_BVDecide_instHashableGate_hash(v_a_315_);
v___x_320_ = lean_uint64_mix_hash(v___x_318_, v___x_319_);
lean_inc_ref(v_inst_301_);
v___x_321_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_301_, v_a_316_);
v___x_322_ = lean_uint64_mix_hash(v___x_320_, v___x_321_);
v___x_323_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_301_, v_a_317_);
v___x_324_ = lean_uint64_mix_hash(v___x_322_, v___x_323_);
return v___x_324_;
}
default: 
{
lean_object* v_a_325_; lean_object* v_a_326_; lean_object* v_a_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; 
v_a_325_ = lean_ctor_get(v_x_302_, 0);
lean_inc_ref(v_a_325_);
v_a_326_ = lean_ctor_get(v_x_302_, 1);
lean_inc_ref(v_a_326_);
v_a_327_ = lean_ctor_get(v_x_302_, 2);
lean_inc_ref(v_a_327_);
lean_dec_ref_known(v_x_302_, 3);
v___x_328_ = 4ULL;
lean_inc_ref_n(v_inst_301_, 2);
v___x_329_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_301_, v_a_325_);
v___x_330_ = lean_uint64_mix_hash(v___x_328_, v___x_329_);
v___x_331_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_301_, v_a_326_);
v___x_332_ = lean_uint64_mix_hash(v___x_330_, v___x_331_);
v___x_333_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_301_, v_a_327_);
v___x_334_ = lean_uint64_mix_hash(v___x_332_, v___x_333_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg___boxed(lean_object* v_inst_335_, lean_object* v_x_336_){
_start:
{
uint64_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_335_, v_x_336_);
v_r_338_ = lean_box_uint64(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBoolExpr_hash(lean_object* v_00_u03b1_339_, lean_object* v_inst_340_, lean_object* v_x_341_){
_start:
{
uint64_t v___x_342_; 
v___x_342_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_340_, v_x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___boxed(lean_object* v_00_u03b1_343_, lean_object* v_inst_344_, lean_object* v_x_345_){
_start:
{
uint64_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash(v_00_u03b1_343_, v_inst_344_, v_x_345_);
v_r_347_ = lean_box_uint64(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr___redArg(lean_object* v_inst_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___boxed), 3, 2);
lean_closure_set(v___x_349_, 0, lean_box(0));
lean_closure_set(v___x_349_, 1, v_inst_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr(lean_object* v_00_u03b1_350_, lean_object* v_inst_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___boxed), 3, 2);
lean_closure_set(v___x_352_, 0, lean_box(0));
lean_closure_set(v___x_352_, 1, v_inst_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(lean_object* v_inst_360_, lean_object* v_x_361_){
_start:
{
switch(lean_obj_tag(v_x_361_))
{
case 0:
{
lean_object* v_a_362_; lean_object* v___x_363_; 
v_a_362_ = lean_ctor_get(v_x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v_x_361_, 1);
v___x_363_ = lean_apply_1(v_inst_360_, v_a_362_);
return v___x_363_;
}
case 1:
{
uint8_t v_a_364_; 
lean_dec_ref(v_inst_360_);
v_a_364_ = lean_ctor_get_uint8(v_x_361_, 0);
lean_dec_ref_known(v_x_361_, 0);
if (v_a_364_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0));
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1));
return v___x_366_;
}
}
case 2:
{
lean_object* v_a_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_a_367_ = lean_ctor_get(v_x_361_, 0);
lean_inc_ref(v_a_367_);
lean_dec_ref_known(v_x_361_, 1);
v___x_368_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2));
v___x_369_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_360_, v_a_367_);
v___x_370_ = lean_string_append(v___x_368_, v___x_369_);
lean_dec_ref(v___x_369_);
return v___x_370_;
}
case 3:
{
uint8_t v_a_371_; lean_object* v_a_372_; lean_object* v_a_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_a_371_ = lean_ctor_get_uint8(v_x_361_, sizeof(void*)*2);
v_a_372_ = lean_ctor_get(v_x_361_, 0);
lean_inc_ref(v_a_372_);
v_a_373_ = lean_ctor_get(v_x_361_, 1);
lean_inc_ref(v_a_373_);
lean_dec_ref_known(v_x_361_, 2);
v___x_374_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3));
lean_inc_ref(v_inst_360_);
v___x_375_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_360_, v_a_372_);
v___x_376_ = lean_string_append(v___x_374_, v___x_375_);
lean_dec_ref(v___x_375_);
v___x_377_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4));
v___x_378_ = lean_string_append(v___x_376_, v___x_377_);
v___x_379_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_371_);
v___x_380_ = lean_string_append(v___x_378_, v___x_379_);
lean_dec_ref(v___x_379_);
v___x_381_ = lean_string_append(v___x_380_, v___x_377_);
v___x_382_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_360_, v_a_373_);
v___x_383_ = lean_string_append(v___x_381_, v___x_382_);
lean_dec_ref(v___x_382_);
v___x_384_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5));
v___x_385_ = lean_string_append(v___x_383_, v___x_384_);
return v___x_385_;
}
default: 
{
lean_object* v_a_386_; lean_object* v_a_387_; lean_object* v_a_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_a_386_ = lean_ctor_get(v_x_361_, 0);
lean_inc_ref(v_a_386_);
v_a_387_ = lean_ctor_get(v_x_361_, 1);
lean_inc_ref(v_a_387_);
v_a_388_ = lean_ctor_get(v_x_361_, 2);
lean_inc_ref(v_a_388_);
lean_dec_ref_known(v_x_361_, 3);
v___x_389_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6));
lean_inc_ref_n(v_inst_360_, 2);
v___x_390_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_360_, v_a_386_);
v___x_391_ = lean_string_append(v___x_389_, v___x_390_);
lean_dec_ref(v___x_390_);
v___x_392_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4));
v___x_393_ = lean_string_append(v___x_391_, v___x_392_);
v___x_394_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_360_, v_a_387_);
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
lean_dec_ref(v___x_394_);
v___x_396_ = lean_string_append(v___x_395_, v___x_392_);
v___x_397_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_360_, v_a_388_);
v___x_398_ = lean_string_append(v___x_396_, v___x_397_);
lean_dec_ref(v___x_397_);
v___x_399_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5));
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString(lean_object* v_00_u03b1_401_, lean_object* v_inst_402_, lean_object* v_x_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_402_, v_x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString___redArg(lean_object* v_inst_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BoolExpr_toString), 3, 2);
lean_closure_set(v___x_406_, 0, lean_box(0));
lean_closure_set(v___x_406_, 1, v_inst_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString(lean_object* v_00_u03b1_407_, lean_object* v_inst_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BoolExpr_toString), 3, 2);
lean_closure_set(v___x_409_, 0, lean_box(0));
lean_closure_set(v___x_409_, 1, v_inst_408_);
return v___x_409_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(lean_object* v_a_410_, lean_object* v_x_411_){
_start:
{
switch(lean_obj_tag(v_x_411_))
{
case 0:
{
lean_object* v_a_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v_a_412_ = lean_ctor_get(v_x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v_x_411_, 1);
v___x_413_ = lean_apply_1(v_a_410_, v_a_412_);
v___x_414_ = lean_unbox(v___x_413_);
return v___x_414_;
}
case 1:
{
uint8_t v_a_415_; 
lean_dec_ref(v_a_410_);
v_a_415_ = lean_ctor_get_uint8(v_x_411_, 0);
lean_dec_ref_known(v_x_411_, 0);
return v_a_415_;
}
case 2:
{
lean_object* v_a_416_; uint8_t v___x_417_; 
v_a_416_ = lean_ctor_get(v_x_411_, 0);
lean_inc_ref(v_a_416_);
lean_dec_ref_known(v_x_411_, 1);
v___x_417_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_410_, v_a_416_);
if (v___x_417_ == 0)
{
uint8_t v___x_418_; 
v___x_418_ = 1;
return v___x_418_;
}
else
{
uint8_t v___x_419_; 
v___x_419_ = 0;
return v___x_419_;
}
}
case 3:
{
uint8_t v_a_420_; lean_object* v_a_421_; lean_object* v_a_422_; uint8_t v___x_423_; uint8_t v___x_424_; uint8_t v___x_425_; 
v_a_420_ = lean_ctor_get_uint8(v_x_411_, sizeof(void*)*2);
v_a_421_ = lean_ctor_get(v_x_411_, 0);
lean_inc_ref(v_a_421_);
v_a_422_ = lean_ctor_get(v_x_411_, 1);
lean_inc_ref(v_a_422_);
lean_dec_ref_known(v_x_411_, 2);
lean_inc_ref(v_a_410_);
v___x_423_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_410_, v_a_421_);
v___x_424_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_410_, v_a_422_);
v___x_425_ = l_Std_Tactic_BVDecide_Gate_eval(v_a_420_, v___x_423_, v___x_424_);
return v___x_425_;
}
default: 
{
lean_object* v_a_426_; lean_object* v_a_427_; lean_object* v_a_428_; uint8_t v___x_429_; 
v_a_426_ = lean_ctor_get(v_x_411_, 0);
lean_inc_ref(v_a_426_);
v_a_427_ = lean_ctor_get(v_x_411_, 1);
lean_inc_ref(v_a_427_);
v_a_428_ = lean_ctor_get(v_x_411_, 2);
lean_inc_ref(v_a_428_);
lean_dec_ref_known(v_x_411_, 3);
lean_inc_ref(v_a_410_);
v___x_429_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_410_, v_a_426_);
if (v___x_429_ == 0)
{
lean_dec_ref(v_a_427_);
v_x_411_ = v_a_428_;
goto _start;
}
else
{
lean_dec_ref(v_a_428_);
v_x_411_ = v_a_427_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___redArg___boxed(lean_object* v_a_432_, lean_object* v_x_433_){
_start:
{
uint8_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_432_, v_x_433_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval(lean_object* v_00_u03b1_436_, lean_object* v_a_437_, lean_object* v_x_438_){
_start:
{
uint8_t v___x_439_; 
v___x_439_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_437_, v_x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___boxed(lean_object* v_00_u03b1_440_, lean_object* v_a_441_, lean_object* v_x_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Std_Tactic_BVDecide_BoolExpr_eval(v_00_u03b1_440_, v_a_441_, v_x_442_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg(uint8_t v_x_445_, lean_object* v_h__1_446_, lean_object* v_h__2_447_, lean_object* v_h__3_448_, lean_object* v_h__4_449_){
_start:
{
switch(v_x_445_)
{
case 0:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec(v_h__4_449_);
lean_dec(v_h__3_448_);
lean_dec(v_h__2_447_);
v___x_450_ = lean_box(0);
v___x_451_ = lean_apply_1(v_h__1_446_, v___x_450_);
return v___x_451_;
}
case 1:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec(v_h__4_449_);
lean_dec(v_h__3_448_);
lean_dec(v_h__1_446_);
v___x_452_ = lean_box(0);
v___x_453_ = lean_apply_1(v_h__2_447_, v___x_452_);
return v___x_453_;
}
case 2:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_h__4_449_);
lean_dec(v_h__2_447_);
lean_dec(v_h__1_446_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_apply_1(v_h__3_448_, v___x_454_);
return v___x_455_;
}
default: 
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v_h__3_448_);
lean_dec(v_h__2_447_);
lean_dec(v_h__1_446_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_apply_1(v_h__4_449_, v___x_456_);
return v___x_457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg___boxed(lean_object* v_x_458_, lean_object* v_h__1_459_, lean_object* v_h__2_460_, lean_object* v_h__3_461_, lean_object* v_h__4_462_){
_start:
{
uint8_t v_x_42__boxed_463_; lean_object* v_res_464_; 
v_x_42__boxed_463_ = lean_unbox(v_x_458_);
v_res_464_ = l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg(v_x_42__boxed_463_, v_h__1_459_, v_h__2_460_, v_h__3_461_, v_h__4_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter(lean_object* v_motive_465_, uint8_t v_x_466_, lean_object* v_h__1_467_, lean_object* v_h__2_468_, lean_object* v_h__3_469_, lean_object* v_h__4_470_){
_start:
{
switch(v_x_466_)
{
case 0:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v_h__4_470_);
lean_dec(v_h__3_469_);
lean_dec(v_h__2_468_);
v___x_471_ = lean_box(0);
v___x_472_ = lean_apply_1(v_h__1_467_, v___x_471_);
return v___x_472_;
}
case 1:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v_h__4_470_);
lean_dec(v_h__3_469_);
lean_dec(v_h__1_467_);
v___x_473_ = lean_box(0);
v___x_474_ = lean_apply_1(v_h__2_468_, v___x_473_);
return v___x_474_;
}
case 2:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_h__4_470_);
lean_dec(v_h__2_468_);
lean_dec(v_h__1_467_);
v___x_475_ = lean_box(0);
v___x_476_ = lean_apply_1(v_h__3_469_, v___x_475_);
return v___x_476_;
}
default: 
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_h__3_469_);
lean_dec(v_h__2_468_);
lean_dec(v_h__1_467_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_apply_1(v_h__4_470_, v___x_477_);
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___boxed(lean_object* v_motive_479_, lean_object* v_x_480_, lean_object* v_h__1_481_, lean_object* v_h__2_482_, lean_object* v_h__3_483_, lean_object* v_h__4_484_){
_start:
{
uint8_t v_x_61__boxed_485_; lean_object* v_res_486_; 
v_x_61__boxed_485_ = lean_unbox(v_x_480_);
v_res_486_ = l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter(v_motive_479_, v_x_61__boxed_485_, v_h__1_481_, v_h__2_482_, v_h__3_483_, v_h__4_484_);
return v_res_486_;
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
