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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
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
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_boxed_7_; lean_object* v_res_8_; 
v_x_boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_Std_Tactic_BVDecide_Gate_ctorIdx(v_x_boxed_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___redArg(lean_object* v_k_9_){
_start:
{
lean_inc(v_k_9_);
return v_k_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___redArg___boxed(lean_object* v_k_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Std_Tactic_BVDecide_Gate_ctorElim___redArg(v_k_10_);
lean_dec(v_k_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, uint8_t v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_and_30_){
_start:
{
lean_inc(v_and_30_);
return v_and_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___boxed(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_and_34_){
_start:
{
uint8_t v_t_boxed_35_; lean_object* v_res_36_; 
v_t_boxed_35_ = lean_unbox(v_t_32_);
v_res_36_ = l_Std_Tactic_BVDecide_Gate_and_elim(v_motive_31_, v_t_boxed_35_, v_h_33_, v_and_34_);
lean_dec(v_and_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___redArg(lean_object* v_xor_37_){
_start:
{
lean_inc(v_xor_37_);
return v_xor_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___redArg___boxed(lean_object* v_xor_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_Tactic_BVDecide_Gate_xor_elim___redArg(v_xor_38_);
lean_dec(v_xor_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim(lean_object* v_motive_40_, uint8_t v_t_41_, lean_object* v_h_42_, lean_object* v_xor_43_){
_start:
{
lean_inc(v_xor_43_);
return v_xor_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___boxed(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_xor_47_){
_start:
{
uint8_t v_t_boxed_48_; lean_object* v_res_49_; 
v_t_boxed_48_ = lean_unbox(v_t_45_);
v_res_49_ = l_Std_Tactic_BVDecide_Gate_xor_elim(v_motive_44_, v_t_boxed_48_, v_h_46_, v_xor_47_);
lean_dec(v_xor_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___redArg(lean_object* v_beq_50_){
_start:
{
lean_inc(v_beq_50_);
return v_beq_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___redArg___boxed(lean_object* v_beq_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Tactic_BVDecide_Gate_beq_elim___redArg(v_beq_51_);
lean_dec(v_beq_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim(lean_object* v_motive_53_, uint8_t v_t_54_, lean_object* v_h_55_, lean_object* v_beq_56_){
_start:
{
lean_inc(v_beq_56_);
return v_beq_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___boxed(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_beq_60_){
_start:
{
uint8_t v_t_boxed_61_; lean_object* v_res_62_; 
v_t_boxed_61_ = lean_unbox(v_t_58_);
v_res_62_ = l_Std_Tactic_BVDecide_Gate_beq_elim(v_motive_57_, v_t_boxed_61_, v_h_59_, v_beq_60_);
lean_dec(v_beq_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___redArg(lean_object* v_or_63_){
_start:
{
lean_inc(v_or_63_);
return v_or_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___redArg___boxed(lean_object* v_or_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_Tactic_BVDecide_Gate_or_elim___redArg(v_or_64_);
lean_dec(v_or_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim(lean_object* v_motive_66_, uint8_t v_t_67_, lean_object* v_h_68_, lean_object* v_or_69_){
_start:
{
lean_inc(v_or_69_);
return v_or_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___boxed(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_or_73_){
_start:
{
uint8_t v_t_boxed_74_; lean_object* v_res_75_; 
v_t_boxed_74_ = lean_unbox(v_t_71_);
v_res_75_ = l_Std_Tactic_BVDecide_Gate_or_elim(v_motive_70_, v_t_boxed_74_, v_h_72_, v_or_73_);
lean_dec(v_or_73_);
return v_res_75_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_Gate_ofNat(lean_object* v_n_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_dec_le(v_n_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(2u);
v___x_80_ = lean_nat_dec_le(v_n_76_, v___x_79_);
if (v___x_80_ == 0)
{
uint8_t v___x_81_; 
v___x_81_ = 3;
return v___x_81_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 2;
return v___x_82_;
}
}
else
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_nat_dec_le(v_n_76_, v___x_83_);
if (v___x_84_ == 0)
{
uint8_t v___x_85_; 
v___x_85_ = 1;
return v___x_85_;
}
else
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ofNat___boxed(lean_object* v_n_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Std_Tactic_BVDecide_Gate_ofNat(v_n_87_);
lean_dec(v_n_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqGate(uint8_t v_x_90_, uint8_t v_y_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_92_ = l_Std_Tactic_BVDecide_Gate_ctorIdx(v_x_90_);
v___x_93_ = l_Std_Tactic_BVDecide_Gate_ctorIdx(v_y_91_);
v___x_94_ = lean_nat_dec_eq(v___x_92_, v___x_93_);
lean_dec(v___x_93_);
lean_dec(v___x_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqGate___boxed(lean_object* v_x_95_, lean_object* v_y_96_){
_start:
{
uint8_t v_x_20__boxed_97_; uint8_t v_y_21__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_x_20__boxed_97_ = lean_unbox(v_x_95_);
v_y_21__boxed_98_ = lean_unbox(v_y_96_);
v_res_99_ = l_Std_Tactic_BVDecide_instDecidableEqGate(v_x_20__boxed_97_, v_y_21__boxed_98_);
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
uint8_t v_x_212__boxed_132_; uint8_t v_a_213__boxed_133_; uint8_t v_a_214__boxed_134_; uint8_t v_res_135_; lean_object* v_r_136_; 
v_x_212__boxed_132_ = lean_unbox(v_x_129_);
v_a_213__boxed_133_ = lean_unbox(v_a_130_);
v_a_214__boxed_134_ = lean_unbox(v_a_131_);
v_res_135_ = l_Std_Tactic_BVDecide_Gate_eval(v_x_212__boxed_132_, v_a_213__boxed_133_, v_a_214__boxed_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(lean_object* v_x_137_){
_start:
{
switch(lean_obj_tag(v_x_137_))
{
case 0:
{
lean_object* v___x_138_; 
v___x_138_ = lean_unsigned_to_nat(0u);
return v___x_138_;
}
case 1:
{
lean_object* v___x_139_; 
v___x_139_ = lean_unsigned_to_nat(1u);
return v___x_139_;
}
case 2:
{
lean_object* v___x_140_; 
v___x_140_ = lean_unsigned_to_nat(2u);
return v___x_140_;
}
case 3:
{
lean_object* v___x_141_; 
v___x_141_ = lean_unsigned_to_nat(3u);
return v___x_141_;
}
default: 
{
lean_object* v___x_142_; 
v___x_142_ = lean_unsigned_to_nat(4u);
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg___boxed(lean_object* v_x_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(v_x_143_);
lean_dec_ref(v_x_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx(lean_object* v_00_u03b1_145_, lean_object* v_x_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(v_x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___boxed(lean_object* v_00_u03b1_148_, lean_object* v_x_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx(v_00_u03b1_148_, v_x_149_);
lean_dec_ref(v_x_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(lean_object* v_t_151_, lean_object* v_k_152_){
_start:
{
switch(lean_obj_tag(v_t_151_))
{
case 0:
{
lean_object* v_a_153_; lean_object* v___x_154_; 
v_a_153_ = lean_ctor_get(v_t_151_, 0);
lean_inc(v_a_153_);
lean_dec_ref_known(v_t_151_, 1);
v___x_154_ = lean_apply_1(v_k_152_, v_a_153_);
return v___x_154_;
}
case 1:
{
uint8_t v_a_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_a_155_ = lean_ctor_get_uint8(v_t_151_, 0);
lean_dec_ref_known(v_t_151_, 0);
v___x_156_ = lean_box(v_a_155_);
v___x_157_ = lean_apply_1(v_k_152_, v___x_156_);
return v___x_157_;
}
case 2:
{
lean_object* v_a_158_; lean_object* v___x_159_; 
v_a_158_ = lean_ctor_get(v_t_151_, 0);
lean_inc_ref(v_a_158_);
lean_dec_ref_known(v_t_151_, 1);
v___x_159_ = lean_apply_1(v_k_152_, v_a_158_);
return v___x_159_;
}
case 3:
{
uint8_t v_a_160_; lean_object* v_a_161_; lean_object* v_a_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_a_160_ = lean_ctor_get_uint8(v_t_151_, sizeof(void*)*2);
v_a_161_ = lean_ctor_get(v_t_151_, 0);
lean_inc_ref(v_a_161_);
v_a_162_ = lean_ctor_get(v_t_151_, 1);
lean_inc_ref(v_a_162_);
lean_dec_ref_known(v_t_151_, 2);
v___x_163_ = lean_box(v_a_160_);
v___x_164_ = lean_apply_3(v_k_152_, v___x_163_, v_a_161_, v_a_162_);
return v___x_164_;
}
default: 
{
lean_object* v_a_165_; lean_object* v_a_166_; lean_object* v_a_167_; lean_object* v___x_168_; 
v_a_165_ = lean_ctor_get(v_t_151_, 0);
lean_inc_ref(v_a_165_);
v_a_166_ = lean_ctor_get(v_t_151_, 1);
lean_inc_ref(v_a_166_);
v_a_167_ = lean_ctor_get(v_t_151_, 2);
lean_inc_ref(v_a_167_);
lean_dec_ref_known(v_t_151_, 3);
v___x_168_ = lean_apply_3(v_k_152_, v_a_165_, v_a_166_, v_a_167_);
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim(lean_object* v_00_u03b1_169_, lean_object* v_motive_170_, lean_object* v_ctorIdx_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_k_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_172_, v_k_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___boxed(lean_object* v_00_u03b1_176_, lean_object* v_motive_177_, lean_object* v_ctorIdx_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_k_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim(v_00_u03b1_176_, v_motive_177_, v_ctorIdx_178_, v_t_179_, v_h_180_, v_k_181_);
lean_dec(v_ctorIdx_178_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim___redArg(lean_object* v_t_183_, lean_object* v_literal_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_183_, v_literal_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim(lean_object* v_00_u03b1_186_, lean_object* v_motive_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_literal_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_188_, v_literal_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim___redArg(lean_object* v_t_192_, lean_object* v_const_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_192_, v_const_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim(lean_object* v_00_u03b1_195_, lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_const_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_197_, v_const_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim___redArg(lean_object* v_t_201_, lean_object* v_not_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_201_, v_not_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim(lean_object* v_00_u03b1_204_, lean_object* v_motive_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_not_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_206_, v_not_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim___redArg(lean_object* v_t_210_, lean_object* v_gate_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_210_, v_gate_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim(lean_object* v_00_u03b1_213_, lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_gate_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_215_, v_gate_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim___redArg(lean_object* v_t_219_, lean_object* v_ite_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_219_, v_ite_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim(lean_object* v_00_u03b1_222_, lean_object* v_motive_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_ite_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_224_, v_ite_226_);
return v___x_227_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(lean_object* v_inst_228_, lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
switch(lean_obj_tag(v_x_229_))
{
case 0:
{
if (lean_obj_tag(v_x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v_a_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_a_231_ = lean_ctor_get(v_x_229_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v_x_229_, 1);
v_a_232_ = lean_ctor_get(v_x_230_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v_x_230_, 1);
v___x_233_ = lean_apply_2(v_inst_228_, v_a_231_, v_a_232_);
v___x_234_ = lean_unbox(v___x_233_);
return v___x_234_;
}
else
{
uint8_t v___x_235_; 
lean_dec_ref_known(v_x_229_, 1);
lean_dec_ref(v_x_230_);
lean_dec_ref(v_inst_228_);
v___x_235_ = 0;
return v___x_235_;
}
}
case 1:
{
lean_dec_ref(v_inst_228_);
if (lean_obj_tag(v_x_230_) == 1)
{
uint8_t v_a_236_; 
v_a_236_ = lean_ctor_get_uint8(v_x_230_, 0);
lean_dec_ref_known(v_x_230_, 0);
if (v_a_236_ == 0)
{
uint8_t v_a_237_; 
v_a_237_ = lean_ctor_get_uint8(v_x_229_, 0);
lean_dec_ref_known(v_x_229_, 0);
if (v_a_237_ == 0)
{
uint8_t v___x_238_; 
v___x_238_ = 1;
return v___x_238_;
}
else
{
return v_a_236_;
}
}
else
{
uint8_t v_a_239_; 
v_a_239_ = lean_ctor_get_uint8(v_x_229_, 0);
lean_dec_ref_known(v_x_229_, 0);
return v_a_239_;
}
}
else
{
uint8_t v___x_240_; 
lean_dec_ref_known(v_x_229_, 0);
lean_dec_ref(v_x_230_);
v___x_240_ = 0;
return v___x_240_;
}
}
case 2:
{
if (lean_obj_tag(v_x_230_) == 2)
{
lean_object* v_a_241_; lean_object* v_a_242_; 
v_a_241_ = lean_ctor_get(v_x_229_, 0);
lean_inc_ref(v_a_241_);
lean_dec_ref_known(v_x_229_, 1);
v_a_242_ = lean_ctor_get(v_x_230_, 0);
lean_inc_ref(v_a_242_);
lean_dec_ref_known(v_x_230_, 1);
v_x_229_ = v_a_241_;
v_x_230_ = v_a_242_;
goto _start;
}
else
{
uint8_t v___x_244_; 
lean_dec_ref_known(v_x_229_, 1);
lean_dec_ref(v_x_230_);
lean_dec_ref(v_inst_228_);
v___x_244_ = 0;
return v___x_244_;
}
}
case 3:
{
if (lean_obj_tag(v_x_230_) == 3)
{
uint8_t v_a_245_; lean_object* v_a_246_; lean_object* v_a_247_; uint8_t v_a_248_; lean_object* v_a_249_; lean_object* v_a_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_a_245_ = lean_ctor_get_uint8(v_x_229_, sizeof(void*)*2);
v_a_246_ = lean_ctor_get(v_x_229_, 0);
lean_inc_ref(v_a_246_);
v_a_247_ = lean_ctor_get(v_x_229_, 1);
lean_inc_ref(v_a_247_);
lean_dec_ref_known(v_x_229_, 2);
v_a_248_ = lean_ctor_get_uint8(v_x_230_, sizeof(void*)*2);
v_a_249_ = lean_ctor_get(v_x_230_, 0);
lean_inc_ref(v_a_249_);
v_a_250_ = lean_ctor_get(v_x_230_, 1);
lean_inc_ref(v_a_250_);
lean_dec_ref_known(v_x_230_, 2);
v___x_251_ = l_Std_Tactic_BVDecide_Gate_ctorIdx(v_a_245_);
v___x_252_ = l_Std_Tactic_BVDecide_Gate_ctorIdx(v_a_248_);
v___x_253_ = lean_nat_dec_eq(v___x_251_, v___x_252_);
lean_dec(v___x_252_);
lean_dec(v___x_251_);
if (v___x_253_ == 0)
{
lean_dec_ref(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec_ref(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec_ref(v_inst_228_);
return v___x_253_;
}
else
{
uint8_t v_inst_254_; 
lean_inc_ref(v_inst_228_);
v_inst_254_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_228_, v_a_246_, v_a_249_);
if (v_inst_254_ == 0)
{
lean_dec_ref(v_a_250_);
lean_dec_ref(v_a_247_);
lean_dec_ref(v_inst_228_);
return v_inst_254_;
}
else
{
v_x_229_ = v_a_247_;
v_x_230_ = v_a_250_;
goto _start;
}
}
}
else
{
uint8_t v___x_256_; 
lean_dec_ref_known(v_x_229_, 2);
lean_dec_ref(v_x_230_);
lean_dec_ref(v_inst_228_);
v___x_256_ = 0;
return v___x_256_;
}
}
default: 
{
if (lean_obj_tag(v_x_230_) == 4)
{
lean_object* v_a_257_; lean_object* v_a_258_; lean_object* v_a_259_; lean_object* v_a_260_; lean_object* v_a_261_; lean_object* v_a_262_; uint8_t v_inst_263_; 
v_a_257_ = lean_ctor_get(v_x_229_, 0);
lean_inc_ref(v_a_257_);
v_a_258_ = lean_ctor_get(v_x_229_, 1);
lean_inc_ref(v_a_258_);
v_a_259_ = lean_ctor_get(v_x_229_, 2);
lean_inc_ref(v_a_259_);
lean_dec_ref_known(v_x_229_, 3);
v_a_260_ = lean_ctor_get(v_x_230_, 0);
lean_inc_ref(v_a_260_);
v_a_261_ = lean_ctor_get(v_x_230_, 1);
lean_inc_ref(v_a_261_);
v_a_262_ = lean_ctor_get(v_x_230_, 2);
lean_inc_ref(v_a_262_);
lean_dec_ref_known(v_x_230_, 3);
lean_inc_ref(v_inst_228_);
v_inst_263_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_228_, v_a_257_, v_a_260_);
if (v_inst_263_ == 0)
{
lean_dec_ref(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec_ref(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec_ref(v_inst_228_);
return v_inst_263_;
}
else
{
uint8_t v_inst_264_; 
lean_inc_ref(v_inst_228_);
v_inst_264_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_228_, v_a_258_, v_a_261_);
if (v_inst_264_ == 0)
{
lean_dec_ref(v_a_262_);
lean_dec_ref(v_a_259_);
lean_dec_ref(v_inst_228_);
return v_inst_264_;
}
else
{
v_x_229_ = v_a_259_;
v_x_230_ = v_a_262_;
goto _start;
}
}
}
else
{
uint8_t v___x_266_; 
lean_dec_ref_known(v_x_229_, 3);
lean_dec_ref(v_x_230_);
lean_dec_ref(v_inst_228_);
v___x_266_ = 0;
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg___boxed(lean_object* v_inst_267_, lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_267_, v_x_268_, v_x_269_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq(lean_object* v_00_u03b1_272_, lean_object* v_inst_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_273_, v_x_274_, v_x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___boxed(lean_object* v_00_u03b1_277_, lean_object* v_inst_278_, lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq(v_00_u03b1_277_, v_inst_278_, v_x_279_, v_x_280_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg(lean_object* v_inst_283_, lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_283_, v_x_284_, v_x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg___boxed(lean_object* v_inst_287_, lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___redArg(v_inst_287_, v_x_288_, v_x_289_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBoolExpr(lean_object* v_00_u03b1_292_, lean_object* v_inst_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr_decEq___redArg(v_inst_293_, v_x_294_, v_x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBoolExpr___boxed(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_, lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Std_Tactic_BVDecide_instDecidableEqBoolExpr(v_00_u03b1_297_, v_inst_298_, v_x_299_, v_x_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(lean_object* v_inst_303_, lean_object* v_x_304_){
_start:
{
switch(lean_obj_tag(v_x_304_))
{
case 0:
{
lean_object* v_a_305_; uint64_t v___x_306_; lean_object* v___x_307_; uint64_t v___x_308_; uint64_t v___x_309_; 
v_a_305_ = lean_ctor_get(v_x_304_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v_x_304_, 1);
v___x_306_ = 0ULL;
v___x_307_ = lean_apply_1(v_inst_303_, v_a_305_);
v___x_308_ = lean_unbox_uint64(v___x_307_);
lean_dec_ref(v___x_307_);
v___x_309_ = lean_uint64_mix_hash(v___x_306_, v___x_308_);
return v___x_309_;
}
case 1:
{
uint8_t v_a_310_; 
lean_dec_ref(v_inst_303_);
v_a_310_ = lean_ctor_get_uint8(v_x_304_, 0);
lean_dec_ref_known(v_x_304_, 0);
if (v_a_310_ == 0)
{
uint64_t v___x_311_; 
v___x_311_ = 6634225825881527916ULL;
return v___x_311_;
}
else
{
uint64_t v___x_312_; 
v___x_312_ = 5934453574740161273ULL;
return v___x_312_;
}
}
case 2:
{
lean_object* v_a_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; 
v_a_313_ = lean_ctor_get(v_x_304_, 0);
lean_inc_ref(v_a_313_);
lean_dec_ref_known(v_x_304_, 1);
v___x_314_ = 2ULL;
v___x_315_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_303_, v_a_313_);
v___x_316_ = lean_uint64_mix_hash(v___x_314_, v___x_315_);
return v___x_316_;
}
case 3:
{
uint8_t v_a_317_; lean_object* v_a_318_; lean_object* v_a_319_; uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v___x_325_; uint64_t v___x_326_; 
v_a_317_ = lean_ctor_get_uint8(v_x_304_, sizeof(void*)*2);
v_a_318_ = lean_ctor_get(v_x_304_, 0);
lean_inc_ref(v_a_318_);
v_a_319_ = lean_ctor_get(v_x_304_, 1);
lean_inc_ref(v_a_319_);
lean_dec_ref_known(v_x_304_, 2);
v___x_320_ = 3ULL;
v___x_321_ = l_Std_Tactic_BVDecide_instHashableGate_hash(v_a_317_);
v___x_322_ = lean_uint64_mix_hash(v___x_320_, v___x_321_);
lean_inc_ref(v_inst_303_);
v___x_323_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_303_, v_a_318_);
v___x_324_ = lean_uint64_mix_hash(v___x_322_, v___x_323_);
v___x_325_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_303_, v_a_319_);
v___x_326_ = lean_uint64_mix_hash(v___x_324_, v___x_325_);
return v___x_326_;
}
default: 
{
lean_object* v_a_327_; lean_object* v_a_328_; lean_object* v_a_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; 
v_a_327_ = lean_ctor_get(v_x_304_, 0);
lean_inc_ref(v_a_327_);
v_a_328_ = lean_ctor_get(v_x_304_, 1);
lean_inc_ref(v_a_328_);
v_a_329_ = lean_ctor_get(v_x_304_, 2);
lean_inc_ref(v_a_329_);
lean_dec_ref_known(v_x_304_, 3);
v___x_330_ = 4ULL;
lean_inc_ref_n(v_inst_303_, 2);
v___x_331_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_303_, v_a_327_);
v___x_332_ = lean_uint64_mix_hash(v___x_330_, v___x_331_);
v___x_333_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_303_, v_a_328_);
v___x_334_ = lean_uint64_mix_hash(v___x_332_, v___x_333_);
v___x_335_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_303_, v_a_329_);
v___x_336_ = lean_uint64_mix_hash(v___x_334_, v___x_335_);
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg___boxed(lean_object* v_inst_337_, lean_object* v_x_338_){
_start:
{
uint64_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_337_, v_x_338_);
v_r_340_ = lean_box_uint64(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBoolExpr_hash(lean_object* v_00_u03b1_341_, lean_object* v_inst_342_, lean_object* v_x_343_){
_start:
{
uint64_t v___x_344_; 
v___x_344_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___redArg(v_inst_342_, v_x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___boxed(lean_object* v_00_u03b1_345_, lean_object* v_inst_346_, lean_object* v_x_347_){
_start:
{
uint64_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_Std_Tactic_BVDecide_instHashableBoolExpr_hash(v_00_u03b1_345_, v_inst_346_, v_x_347_);
v_r_349_ = lean_box_uint64(v_res_348_);
return v_r_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr___redArg(lean_object* v_inst_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___boxed), 3, 2);
lean_closure_set(v___x_351_, 0, lean_box(0));
lean_closure_set(v___x_351_, 1, v_inst_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBoolExpr(lean_object* v_00_u03b1_352_, lean_object* v_inst_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instHashableBoolExpr_hash___boxed), 3, 2);
lean_closure_set(v___x_354_, 0, lean_box(0));
lean_closure_set(v___x_354_, 1, v_inst_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(lean_object* v_inst_362_, lean_object* v_x_363_){
_start:
{
switch(lean_obj_tag(v_x_363_))
{
case 0:
{
lean_object* v_a_364_; lean_object* v___x_365_; 
v_a_364_ = lean_ctor_get(v_x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v_x_363_, 1);
v___x_365_ = lean_apply_1(v_inst_362_, v_a_364_);
return v___x_365_;
}
case 1:
{
uint8_t v_a_366_; 
lean_dec_ref(v_inst_362_);
v_a_366_ = lean_ctor_get_uint8(v_x_363_, 0);
lean_dec_ref_known(v_x_363_, 0);
if (v_a_366_ == 0)
{
lean_object* v___x_367_; 
v___x_367_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0));
return v___x_367_;
}
else
{
lean_object* v___x_368_; 
v___x_368_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1));
return v___x_368_;
}
}
case 2:
{
lean_object* v_a_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_a_369_ = lean_ctor_get(v_x_363_, 0);
lean_inc_ref(v_a_369_);
lean_dec_ref_known(v_x_363_, 1);
v___x_370_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2));
v___x_371_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_362_, v_a_369_);
v___x_372_ = lean_string_append(v___x_370_, v___x_371_);
lean_dec_ref(v___x_371_);
return v___x_372_;
}
case 3:
{
uint8_t v_a_373_; lean_object* v_a_374_; lean_object* v_a_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_a_373_ = lean_ctor_get_uint8(v_x_363_, sizeof(void*)*2);
v_a_374_ = lean_ctor_get(v_x_363_, 0);
lean_inc_ref(v_a_374_);
v_a_375_ = lean_ctor_get(v_x_363_, 1);
lean_inc_ref(v_a_375_);
lean_dec_ref_known(v_x_363_, 2);
v___x_376_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3));
lean_inc_ref(v_inst_362_);
v___x_377_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_362_, v_a_374_);
v___x_378_ = lean_string_append(v___x_376_, v___x_377_);
lean_dec_ref(v___x_377_);
v___x_379_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4));
v___x_380_ = lean_string_append(v___x_378_, v___x_379_);
v___x_381_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_373_);
v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
lean_dec_ref(v___x_381_);
v___x_383_ = lean_string_append(v___x_382_, v___x_379_);
v___x_384_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_362_, v_a_375_);
v___x_385_ = lean_string_append(v___x_383_, v___x_384_);
lean_dec_ref(v___x_384_);
v___x_386_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5));
v___x_387_ = lean_string_append(v___x_385_, v___x_386_);
return v___x_387_;
}
default: 
{
lean_object* v_a_388_; lean_object* v_a_389_; lean_object* v_a_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_a_388_ = lean_ctor_get(v_x_363_, 0);
lean_inc_ref(v_a_388_);
v_a_389_ = lean_ctor_get(v_x_363_, 1);
lean_inc_ref(v_a_389_);
v_a_390_ = lean_ctor_get(v_x_363_, 2);
lean_inc_ref(v_a_390_);
lean_dec_ref_known(v_x_363_, 3);
v___x_391_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6));
lean_inc_ref_n(v_inst_362_, 2);
v___x_392_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_362_, v_a_388_);
v___x_393_ = lean_string_append(v___x_391_, v___x_392_);
lean_dec_ref(v___x_392_);
v___x_394_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4));
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
v___x_396_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_362_, v_a_389_);
v___x_397_ = lean_string_append(v___x_395_, v___x_396_);
lean_dec_ref(v___x_396_);
v___x_398_ = lean_string_append(v___x_397_, v___x_394_);
v___x_399_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_362_, v_a_390_);
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
lean_dec_ref(v___x_399_);
v___x_401_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5));
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString(lean_object* v_00_u03b1_403_, lean_object* v_inst_404_, lean_object* v_x_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_404_, v_x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString___redArg(lean_object* v_inst_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BoolExpr_toString), 3, 2);
lean_closure_set(v___x_408_, 0, lean_box(0));
lean_closure_set(v___x_408_, 1, v_inst_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BoolExpr_toString), 3, 2);
lean_closure_set(v___x_411_, 0, lean_box(0));
lean_closure_set(v___x_411_, 1, v_inst_410_);
return v___x_411_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(lean_object* v_a_412_, lean_object* v_x_413_){
_start:
{
switch(lean_obj_tag(v_x_413_))
{
case 0:
{
lean_object* v_a_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_a_414_ = lean_ctor_get(v_x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v_x_413_, 1);
v___x_415_ = lean_apply_1(v_a_412_, v_a_414_);
v___x_416_ = lean_unbox(v___x_415_);
return v___x_416_;
}
case 1:
{
uint8_t v_a_417_; 
lean_dec_ref(v_a_412_);
v_a_417_ = lean_ctor_get_uint8(v_x_413_, 0);
lean_dec_ref_known(v_x_413_, 0);
return v_a_417_;
}
case 2:
{
lean_object* v_a_418_; uint8_t v___x_419_; 
v_a_418_ = lean_ctor_get(v_x_413_, 0);
lean_inc_ref(v_a_418_);
lean_dec_ref_known(v_x_413_, 1);
v___x_419_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_412_, v_a_418_);
if (v___x_419_ == 0)
{
uint8_t v___x_420_; 
v___x_420_ = 1;
return v___x_420_;
}
else
{
uint8_t v___x_421_; 
v___x_421_ = 0;
return v___x_421_;
}
}
case 3:
{
uint8_t v_a_422_; lean_object* v_a_423_; lean_object* v_a_424_; uint8_t v___x_425_; uint8_t v___x_426_; uint8_t v___x_427_; 
v_a_422_ = lean_ctor_get_uint8(v_x_413_, sizeof(void*)*2);
v_a_423_ = lean_ctor_get(v_x_413_, 0);
lean_inc_ref(v_a_423_);
v_a_424_ = lean_ctor_get(v_x_413_, 1);
lean_inc_ref(v_a_424_);
lean_dec_ref_known(v_x_413_, 2);
lean_inc_ref(v_a_412_);
v___x_425_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_412_, v_a_423_);
v___x_426_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_412_, v_a_424_);
v___x_427_ = l_Std_Tactic_BVDecide_Gate_eval(v_a_422_, v___x_425_, v___x_426_);
return v___x_427_;
}
default: 
{
lean_object* v_a_428_; lean_object* v_a_429_; lean_object* v_a_430_; uint8_t v___x_431_; 
v_a_428_ = lean_ctor_get(v_x_413_, 0);
lean_inc_ref(v_a_428_);
v_a_429_ = lean_ctor_get(v_x_413_, 1);
lean_inc_ref(v_a_429_);
v_a_430_ = lean_ctor_get(v_x_413_, 2);
lean_inc_ref(v_a_430_);
lean_dec_ref_known(v_x_413_, 3);
lean_inc_ref(v_a_412_);
v___x_431_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_412_, v_a_428_);
if (v___x_431_ == 0)
{
lean_dec_ref(v_a_429_);
v_x_413_ = v_a_430_;
goto _start;
}
else
{
lean_dec_ref(v_a_430_);
v_x_413_ = v_a_429_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___redArg___boxed(lean_object* v_a_434_, lean_object* v_x_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_434_, v_x_435_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval(lean_object* v_00_u03b1_438_, lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_439_, v_x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___boxed(lean_object* v_00_u03b1_442_, lean_object* v_a_443_, lean_object* v_x_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Std_Tactic_BVDecide_BoolExpr_eval(v_00_u03b1_442_, v_a_443_, v_x_444_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg(uint8_t v_x_447_, lean_object* v_h__1_448_, lean_object* v_h__2_449_, lean_object* v_h__3_450_, lean_object* v_h__4_451_){
_start:
{
switch(v_x_447_)
{
case 0:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec(v_h__4_451_);
lean_dec(v_h__3_450_);
lean_dec(v_h__2_449_);
v___x_452_ = lean_box(0);
v___x_453_ = lean_apply_1(v_h__1_448_, v___x_452_);
return v___x_453_;
}
case 1:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_h__4_451_);
lean_dec(v_h__3_450_);
lean_dec(v_h__1_448_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_apply_1(v_h__2_449_, v___x_454_);
return v___x_455_;
}
case 2:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v_h__4_451_);
lean_dec(v_h__2_449_);
lean_dec(v_h__1_448_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_apply_1(v_h__3_450_, v___x_456_);
return v___x_457_;
}
default: 
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v_h__3_450_);
lean_dec(v_h__2_449_);
lean_dec(v_h__1_448_);
v___x_458_ = lean_box(0);
v___x_459_ = lean_apply_1(v_h__4_451_, v___x_458_);
return v___x_459_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg___boxed(lean_object* v_x_460_, lean_object* v_h__1_461_, lean_object* v_h__2_462_, lean_object* v_h__3_463_, lean_object* v_h__4_464_){
_start:
{
uint8_t v_x_42__boxed_465_; lean_object* v_res_466_; 
v_x_42__boxed_465_ = lean_unbox(v_x_460_);
v_res_466_ = l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg(v_x_42__boxed_465_, v_h__1_461_, v_h__2_462_, v_h__3_463_, v_h__4_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter(lean_object* v_motive_467_, uint8_t v_x_468_, lean_object* v_h__1_469_, lean_object* v_h__2_470_, lean_object* v_h__3_471_, lean_object* v_h__4_472_){
_start:
{
switch(v_x_468_)
{
case 0:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v_h__4_472_);
lean_dec(v_h__3_471_);
lean_dec(v_h__2_470_);
v___x_473_ = lean_box(0);
v___x_474_ = lean_apply_1(v_h__1_469_, v___x_473_);
return v___x_474_;
}
case 1:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_h__4_472_);
lean_dec(v_h__3_471_);
lean_dec(v_h__1_469_);
v___x_475_ = lean_box(0);
v___x_476_ = lean_apply_1(v_h__2_470_, v___x_475_);
return v___x_476_;
}
case 2:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_h__4_472_);
lean_dec(v_h__2_470_);
lean_dec(v_h__1_469_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_apply_1(v_h__3_471_, v___x_477_);
return v___x_478_;
}
default: 
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v_h__3_471_);
lean_dec(v_h__2_470_);
lean_dec(v_h__1_469_);
v___x_479_ = lean_box(0);
v___x_480_ = lean_apply_1(v_h__4_472_, v___x_479_);
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___boxed(lean_object* v_motive_481_, lean_object* v_x_482_, lean_object* v_h__1_483_, lean_object* v_h__2_484_, lean_object* v_h__3_485_, lean_object* v_h__4_486_){
_start:
{
uint8_t v_x_61__boxed_487_; lean_object* v_res_488_; 
v_x_61__boxed_487_ = lean_unbox(v_x_482_);
v_res_488_ = l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter(v_motive_481_, v_x_61__boxed_487_, v_h__1_483_, v_h__2_484_, v_h__3_485_, v_h__4_486_);
return v_res_488_;
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
