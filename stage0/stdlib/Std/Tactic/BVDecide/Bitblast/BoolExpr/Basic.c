// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic
// Imports: public import Init.Data.String.Basic
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
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toCtorIdx(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Std_Tactic_BVDecide_Gate_ctorIdx(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toCtorIdx___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_x_4__boxed_12_; lean_object* v_res_13_; 
v_x_4__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = l_Std_Tactic_BVDecide_Gate_toCtorIdx(v_x_4__boxed_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___redArg(lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___redArg___boxed(lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_Tactic_BVDecide_Gate_ctorElim___redArg(v_k_15_);
lean_dec(v_k_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, uint8_t v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_inc(v_k_21_);
return v_k_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
uint8_t v_t_boxed_27_; lean_object* v_res_28_; 
v_t_boxed_27_ = lean_unbox(v_t_24_);
v_res_28_ = l_Std_Tactic_BVDecide_Gate_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_boxed_27_, v_h_25_, v_k_26_);
lean_dec(v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___redArg(lean_object* v_and_29_){
_start:
{
lean_inc(v_and_29_);
return v_and_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___redArg___boxed(lean_object* v_and_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Tactic_BVDecide_Gate_and_elim___redArg(v_and_30_);
lean_dec(v_and_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim(lean_object* v_motive_32_, uint8_t v_t_33_, lean_object* v_h_34_, lean_object* v_and_35_){
_start:
{
lean_inc(v_and_35_);
return v_and_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_and_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_and_39_){
_start:
{
uint8_t v_t_boxed_40_; lean_object* v_res_41_; 
v_t_boxed_40_ = lean_unbox(v_t_37_);
v_res_41_ = l_Std_Tactic_BVDecide_Gate_and_elim(v_motive_36_, v_t_boxed_40_, v_h_38_, v_and_39_);
lean_dec(v_and_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___redArg(lean_object* v_xor_42_){
_start:
{
lean_inc(v_xor_42_);
return v_xor_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___redArg___boxed(lean_object* v_xor_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Tactic_BVDecide_Gate_xor_elim___redArg(v_xor_43_);
lean_dec(v_xor_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim(lean_object* v_motive_45_, uint8_t v_t_46_, lean_object* v_h_47_, lean_object* v_xor_48_){
_start:
{
lean_inc(v_xor_48_);
return v_xor_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_xor_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_xor_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Std_Tactic_BVDecide_Gate_xor_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_xor_52_);
lean_dec(v_xor_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___redArg(lean_object* v_beq_55_){
_start:
{
lean_inc(v_beq_55_);
return v_beq_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___redArg___boxed(lean_object* v_beq_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_Tactic_BVDecide_Gate_beq_elim___redArg(v_beq_56_);
lean_dec(v_beq_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_beq_61_){
_start:
{
lean_inc(v_beq_61_);
return v_beq_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_beq_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_beq_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = l_Std_Tactic_BVDecide_Gate_beq_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_beq_65_);
lean_dec(v_beq_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___redArg(lean_object* v_or_68_){
_start:
{
lean_inc(v_or_68_);
return v_or_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___redArg___boxed(lean_object* v_or_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_Tactic_BVDecide_Gate_or_elim___redArg(v_or_69_);
lean_dec(v_or_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_or_74_){
_start:
{
lean_inc(v_or_74_);
return v_or_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_or_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_or_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = l_Std_Tactic_BVDecide_Gate_or_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_or_78_);
lean_dec(v_or_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toString(uint8_t v_x_85_){
_start:
{
switch(v_x_85_)
{
case 0:
{
lean_object* v___x_86_; 
v___x_86_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__0));
return v___x_86_;
}
case 1:
{
lean_object* v___x_87_; 
v___x_87_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__1));
return v___x_87_;
}
case 2:
{
lean_object* v___x_88_; 
v___x_88_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__2));
return v___x_88_;
}
default: 
{
lean_object* v___x_89_; 
v___x_89_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__3));
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toString___boxed(lean_object* v_x_90_){
_start:
{
uint8_t v_x_40__boxed_91_; lean_object* v_res_92_; 
v_x_40__boxed_91_ = lean_unbox(v_x_90_);
v_res_92_ = l_Std_Tactic_BVDecide_Gate_toString(v_x_40__boxed_91_);
return v_res_92_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_Gate_eval(uint8_t v_x_93_, uint8_t v_a_94_, uint8_t v_a_95_){
_start:
{
switch(v_x_93_)
{
case 0:
{
if (v_a_94_ == 0)
{
return v_a_94_;
}
else
{
return v_a_95_;
}
}
case 1:
{
if (v_a_94_ == 0)
{
return v_a_95_;
}
else
{
if (v_a_95_ == 0)
{
return v_a_94_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
}
case 2:
{
if (v_a_94_ == 0)
{
if (v_a_95_ == 0)
{
uint8_t v___x_97_; 
v___x_97_ = 1;
return v___x_97_;
}
else
{
return v_a_94_;
}
}
else
{
return v_a_95_;
}
}
default: 
{
if (v_a_94_ == 0)
{
return v_a_95_;
}
else
{
return v_a_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_eval___boxed(lean_object* v_x_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
uint8_t v_x_237__boxed_101_; uint8_t v_a_238__boxed_102_; uint8_t v_a_239__boxed_103_; uint8_t v_res_104_; lean_object* v_r_105_; 
v_x_237__boxed_101_ = lean_unbox(v_x_98_);
v_a_238__boxed_102_ = lean_unbox(v_a_99_);
v_a_239__boxed_103_ = lean_unbox(v_a_100_);
v_res_104_ = l_Std_Tactic_BVDecide_Gate_eval(v_x_237__boxed_101_, v_a_238__boxed_102_, v_a_239__boxed_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(lean_object* v_x_106_){
_start:
{
switch(lean_obj_tag(v_x_106_))
{
case 0:
{
lean_object* v___x_107_; 
v___x_107_ = lean_unsigned_to_nat(0u);
return v___x_107_;
}
case 1:
{
lean_object* v___x_108_; 
v___x_108_ = lean_unsigned_to_nat(1u);
return v___x_108_;
}
case 2:
{
lean_object* v___x_109_; 
v___x_109_ = lean_unsigned_to_nat(2u);
return v___x_109_;
}
case 3:
{
lean_object* v___x_110_; 
v___x_110_ = lean_unsigned_to_nat(3u);
return v___x_110_;
}
default: 
{
lean_object* v___x_111_; 
v___x_111_ = lean_unsigned_to_nat(4u);
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg___boxed(lean_object* v_x_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(v_x_112_);
lean_dec_ref(v_x_112_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx(lean_object* v_00_u03b1_114_, lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(v_x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___boxed(lean_object* v_00_u03b1_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx(v_00_u03b1_117_, v_x_118_);
lean_dec_ref(v_x_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(lean_object* v_t_120_, lean_object* v_k_121_){
_start:
{
switch(lean_obj_tag(v_t_120_))
{
case 0:
{
lean_object* v_a_122_; lean_object* v___x_123_; 
v_a_122_ = lean_ctor_get(v_t_120_, 0);
lean_inc(v_a_122_);
lean_dec_ref(v_t_120_);
v___x_123_ = lean_apply_1(v_k_121_, v_a_122_);
return v___x_123_;
}
case 1:
{
uint8_t v_a_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_a_124_ = lean_ctor_get_uint8(v_t_120_, 0);
lean_dec_ref(v_t_120_);
v___x_125_ = lean_box(v_a_124_);
v___x_126_ = lean_apply_1(v_k_121_, v___x_125_);
return v___x_126_;
}
case 2:
{
lean_object* v_a_127_; lean_object* v___x_128_; 
v_a_127_ = lean_ctor_get(v_t_120_, 0);
lean_inc_ref(v_a_127_);
lean_dec_ref(v_t_120_);
v___x_128_ = lean_apply_1(v_k_121_, v_a_127_);
return v___x_128_;
}
case 3:
{
uint8_t v_a_129_; lean_object* v_a_130_; lean_object* v_a_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_a_129_ = lean_ctor_get_uint8(v_t_120_, sizeof(void*)*2);
v_a_130_ = lean_ctor_get(v_t_120_, 0);
lean_inc_ref(v_a_130_);
v_a_131_ = lean_ctor_get(v_t_120_, 1);
lean_inc_ref(v_a_131_);
lean_dec_ref(v_t_120_);
v___x_132_ = lean_box(v_a_129_);
v___x_133_ = lean_apply_3(v_k_121_, v___x_132_, v_a_130_, v_a_131_);
return v___x_133_;
}
default: 
{
lean_object* v_a_134_; lean_object* v_a_135_; lean_object* v_a_136_; lean_object* v___x_137_; 
v_a_134_ = lean_ctor_get(v_t_120_, 0);
lean_inc_ref(v_a_134_);
v_a_135_ = lean_ctor_get(v_t_120_, 1);
lean_inc_ref(v_a_135_);
v_a_136_ = lean_ctor_get(v_t_120_, 2);
lean_inc_ref(v_a_136_);
lean_dec_ref(v_t_120_);
v___x_137_ = lean_apply_3(v_k_121_, v_a_134_, v_a_135_, v_a_136_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim(lean_object* v_00_u03b1_138_, lean_object* v_motive_139_, lean_object* v_ctorIdx_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_k_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_141_, v_k_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___boxed(lean_object* v_00_u03b1_145_, lean_object* v_motive_146_, lean_object* v_ctorIdx_147_, lean_object* v_t_148_, lean_object* v_h_149_, lean_object* v_k_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim(v_00_u03b1_145_, v_motive_146_, v_ctorIdx_147_, v_t_148_, v_h_149_, v_k_150_);
lean_dec(v_ctorIdx_147_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim___redArg(lean_object* v_t_152_, lean_object* v_literal_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_152_, v_literal_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim(lean_object* v_00_u03b1_155_, lean_object* v_motive_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_literal_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_157_, v_literal_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim___redArg(lean_object* v_t_161_, lean_object* v_const_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_161_, v_const_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim(lean_object* v_00_u03b1_164_, lean_object* v_motive_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_const_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_166_, v_const_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim___redArg(lean_object* v_t_170_, lean_object* v_not_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_170_, v_not_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim(lean_object* v_00_u03b1_173_, lean_object* v_motive_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_not_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_175_, v_not_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim___redArg(lean_object* v_t_179_, lean_object* v_gate_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_179_, v_gate_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim(lean_object* v_00_u03b1_182_, lean_object* v_motive_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_gate_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_184_, v_gate_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim___redArg(lean_object* v_t_188_, lean_object* v_ite_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_188_, v_ite_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim(lean_object* v_00_u03b1_191_, lean_object* v_motive_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_ite_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_193_, v_ite_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(lean_object* v_inst_204_, lean_object* v_x_205_){
_start:
{
switch(lean_obj_tag(v_x_205_))
{
case 0:
{
lean_object* v_a_206_; lean_object* v___x_207_; 
v_a_206_ = lean_ctor_get(v_x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref(v_x_205_);
v___x_207_ = lean_apply_1(v_inst_204_, v_a_206_);
return v___x_207_;
}
case 1:
{
uint8_t v_a_208_; 
lean_dec_ref(v_inst_204_);
v_a_208_ = lean_ctor_get_uint8(v_x_205_, 0);
lean_dec_ref(v_x_205_);
if (v_a_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0));
return v___x_209_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1));
return v___x_210_;
}
}
case 2:
{
lean_object* v_a_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_a_211_ = lean_ctor_get(v_x_205_, 0);
lean_inc_ref(v_a_211_);
lean_dec_ref(v_x_205_);
v___x_212_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2));
v___x_213_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_204_, v_a_211_);
v___x_214_ = lean_string_append(v___x_212_, v___x_213_);
lean_dec_ref(v___x_213_);
return v___x_214_;
}
case 3:
{
uint8_t v_a_215_; lean_object* v_a_216_; lean_object* v_a_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_a_215_ = lean_ctor_get_uint8(v_x_205_, sizeof(void*)*2);
v_a_216_ = lean_ctor_get(v_x_205_, 0);
lean_inc_ref(v_a_216_);
v_a_217_ = lean_ctor_get(v_x_205_, 1);
lean_inc_ref(v_a_217_);
lean_dec_ref(v_x_205_);
v___x_218_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3));
lean_inc_ref(v_inst_204_);
v___x_219_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_204_, v_a_216_);
v___x_220_ = lean_string_append(v___x_218_, v___x_219_);
lean_dec_ref(v___x_219_);
v___x_221_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4));
v___x_222_ = lean_string_append(v___x_220_, v___x_221_);
v___x_223_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_215_);
v___x_224_ = lean_string_append(v___x_222_, v___x_223_);
lean_dec_ref(v___x_223_);
v___x_225_ = lean_string_append(v___x_224_, v___x_221_);
v___x_226_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_204_, v_a_217_);
v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
lean_dec_ref(v___x_226_);
v___x_228_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5));
v___x_229_ = lean_string_append(v___x_227_, v___x_228_);
return v___x_229_;
}
default: 
{
lean_object* v_a_230_; lean_object* v_a_231_; lean_object* v_a_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_a_230_ = lean_ctor_get(v_x_205_, 0);
lean_inc_ref(v_a_230_);
v_a_231_ = lean_ctor_get(v_x_205_, 1);
lean_inc_ref(v_a_231_);
v_a_232_ = lean_ctor_get(v_x_205_, 2);
lean_inc_ref(v_a_232_);
lean_dec_ref(v_x_205_);
v___x_233_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6));
lean_inc_ref(v_inst_204_);
v___x_234_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_204_, v_a_230_);
v___x_235_ = lean_string_append(v___x_233_, v___x_234_);
lean_dec_ref(v___x_234_);
v___x_236_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4));
v___x_237_ = lean_string_append(v___x_235_, v___x_236_);
lean_inc_ref(v_inst_204_);
v___x_238_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_204_, v_a_231_);
v___x_239_ = lean_string_append(v___x_237_, v___x_238_);
lean_dec_ref(v___x_238_);
v___x_240_ = lean_string_append(v___x_239_, v___x_236_);
v___x_241_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_204_, v_a_232_);
v___x_242_ = lean_string_append(v___x_240_, v___x_241_);
lean_dec_ref(v___x_241_);
v___x_243_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5));
v___x_244_ = lean_string_append(v___x_242_, v___x_243_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString(lean_object* v_00_u03b1_245_, lean_object* v_inst_246_, lean_object* v_x_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_246_, v_x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString___redArg(lean_object* v_inst_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BoolExpr_toString), 3, 2);
lean_closure_set(v___x_250_, 0, lean_box(0));
lean_closure_set(v___x_250_, 1, v_inst_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString(lean_object* v_00_u03b1_251_, lean_object* v_inst_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BoolExpr_toString), 3, 2);
lean_closure_set(v___x_253_, 0, lean_box(0));
lean_closure_set(v___x_253_, 1, v_inst_252_);
return v___x_253_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(lean_object* v_a_254_, lean_object* v_x_255_){
_start:
{
switch(lean_obj_tag(v_x_255_))
{
case 0:
{
lean_object* v_a_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_a_256_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref(v_x_255_);
v___x_257_ = lean_apply_1(v_a_254_, v_a_256_);
v___x_258_ = lean_unbox(v___x_257_);
return v___x_258_;
}
case 1:
{
uint8_t v_a_259_; 
lean_dec_ref(v_a_254_);
v_a_259_ = lean_ctor_get_uint8(v_x_255_, 0);
lean_dec_ref(v_x_255_);
return v_a_259_;
}
case 2:
{
lean_object* v_a_260_; uint8_t v___x_261_; 
v_a_260_ = lean_ctor_get(v_x_255_, 0);
lean_inc_ref(v_a_260_);
lean_dec_ref(v_x_255_);
v___x_261_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_254_, v_a_260_);
if (v___x_261_ == 0)
{
uint8_t v___x_262_; 
v___x_262_ = 1;
return v___x_262_;
}
else
{
uint8_t v___x_263_; 
v___x_263_ = 0;
return v___x_263_;
}
}
case 3:
{
uint8_t v_a_264_; lean_object* v_a_265_; lean_object* v_a_266_; uint8_t v___x_267_; uint8_t v___x_268_; uint8_t v___x_269_; 
v_a_264_ = lean_ctor_get_uint8(v_x_255_, sizeof(void*)*2);
v_a_265_ = lean_ctor_get(v_x_255_, 0);
lean_inc_ref(v_a_265_);
v_a_266_ = lean_ctor_get(v_x_255_, 1);
lean_inc_ref(v_a_266_);
lean_dec_ref(v_x_255_);
lean_inc_ref(v_a_254_);
v___x_267_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_254_, v_a_265_);
v___x_268_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_254_, v_a_266_);
v___x_269_ = l_Std_Tactic_BVDecide_Gate_eval(v_a_264_, v___x_267_, v___x_268_);
return v___x_269_;
}
default: 
{
lean_object* v_a_270_; lean_object* v_a_271_; lean_object* v_a_272_; uint8_t v___x_273_; 
v_a_270_ = lean_ctor_get(v_x_255_, 0);
lean_inc_ref(v_a_270_);
v_a_271_ = lean_ctor_get(v_x_255_, 1);
lean_inc_ref(v_a_271_);
v_a_272_ = lean_ctor_get(v_x_255_, 2);
lean_inc_ref(v_a_272_);
lean_dec_ref(v_x_255_);
lean_inc_ref(v_a_254_);
v___x_273_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_254_, v_a_270_);
if (v___x_273_ == 0)
{
lean_dec_ref(v_a_271_);
v_x_255_ = v_a_272_;
goto _start;
}
else
{
lean_dec_ref(v_a_272_);
v_x_255_ = v_a_271_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___redArg___boxed(lean_object* v_a_276_, lean_object* v_x_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_276_, v_x_277_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval(lean_object* v_00_u03b1_280_, lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_281_, v_x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___boxed(lean_object* v_00_u03b1_284_, lean_object* v_a_285_, lean_object* v_x_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Std_Tactic_BVDecide_BoolExpr_eval(v_00_u03b1_284_, v_a_285_, v_x_286_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg(uint8_t v_x_289_, lean_object* v_h__1_290_, lean_object* v_h__2_291_, lean_object* v_h__3_292_, lean_object* v_h__4_293_){
_start:
{
switch(v_x_289_)
{
case 0:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec(v_h__4_293_);
lean_dec(v_h__3_292_);
lean_dec(v_h__2_291_);
v___x_294_ = lean_box(0);
v___x_295_ = lean_apply_1(v_h__1_290_, v___x_294_);
return v___x_295_;
}
case 1:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v_h__4_293_);
lean_dec(v_h__3_292_);
lean_dec(v_h__1_290_);
v___x_296_ = lean_box(0);
v___x_297_ = lean_apply_1(v_h__2_291_, v___x_296_);
return v___x_297_;
}
case 2:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_h__4_293_);
lean_dec(v_h__2_291_);
lean_dec(v_h__1_290_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_apply_1(v_h__3_292_, v___x_298_);
return v___x_299_;
}
default: 
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_h__3_292_);
lean_dec(v_h__2_291_);
lean_dec(v_h__1_290_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_apply_1(v_h__4_293_, v___x_300_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg___boxed(lean_object* v_x_302_, lean_object* v_h__1_303_, lean_object* v_h__2_304_, lean_object* v_h__3_305_, lean_object* v_h__4_306_){
_start:
{
uint8_t v_x_46__boxed_307_; lean_object* v_res_308_; 
v_x_46__boxed_307_ = lean_unbox(v_x_302_);
v_res_308_ = l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg(v_x_46__boxed_307_, v_h__1_303_, v_h__2_304_, v_h__3_305_, v_h__4_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter(lean_object* v_motive_309_, uint8_t v_x_310_, lean_object* v_h__1_311_, lean_object* v_h__2_312_, lean_object* v_h__3_313_, lean_object* v_h__4_314_){
_start:
{
switch(v_x_310_)
{
case 0:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_h__4_314_);
lean_dec(v_h__3_313_);
lean_dec(v_h__2_312_);
v___x_315_ = lean_box(0);
v___x_316_ = lean_apply_1(v_h__1_311_, v___x_315_);
return v___x_316_;
}
case 1:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_h__4_314_);
lean_dec(v_h__3_313_);
lean_dec(v_h__1_311_);
v___x_317_ = lean_box(0);
v___x_318_ = lean_apply_1(v_h__2_312_, v___x_317_);
return v___x_318_;
}
case 2:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_h__4_314_);
lean_dec(v_h__2_312_);
lean_dec(v_h__1_311_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_apply_1(v_h__3_313_, v___x_319_);
return v___x_320_;
}
default: 
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v_h__3_313_);
lean_dec(v_h__2_312_);
lean_dec(v_h__1_311_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_apply_1(v_h__4_314_, v___x_321_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___boxed(lean_object* v_motive_323_, lean_object* v_x_324_, lean_object* v_h__1_325_, lean_object* v_h__2_326_, lean_object* v_h__3_327_, lean_object* v_h__4_328_){
_start:
{
uint8_t v_x_65__boxed_329_; lean_object* v_res_330_; 
v_x_65__boxed_329_ = lean_unbox(v_x_324_);
v_res_330_ = l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter(v_motive_323_, v_x_65__boxed_329_, v_h__1_325_, v_h__2_326_, v_h__3_327_, v_h__4_328_);
return v_res_330_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Basic(builtin);
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
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
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
