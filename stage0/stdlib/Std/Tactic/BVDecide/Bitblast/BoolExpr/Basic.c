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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toString(uint8_t v_x_80_){
_start:
{
switch(v_x_80_)
{
case 0:
{
lean_object* v___x_81_; 
v___x_81_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__0));
return v___x_81_;
}
case 1:
{
lean_object* v___x_82_; 
v___x_82_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__1));
return v___x_82_;
}
case 2:
{
lean_object* v___x_83_; 
v___x_83_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__2));
return v___x_83_;
}
default: 
{
lean_object* v___x_84_; 
v___x_84_ = ((lean_object*)(l_Std_Tactic_BVDecide_Gate_toString___closed__3));
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_toString___boxed(lean_object* v_x_85_){
_start:
{
uint8_t v_x_40__boxed_86_; lean_object* v_res_87_; 
v_x_40__boxed_86_ = lean_unbox(v_x_85_);
v_res_87_ = l_Std_Tactic_BVDecide_Gate_toString(v_x_40__boxed_86_);
return v_res_87_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_Gate_eval(uint8_t v_x_88_, uint8_t v_a_89_, uint8_t v_a_90_){
_start:
{
switch(v_x_88_)
{
case 0:
{
if (v_a_89_ == 0)
{
return v_a_89_;
}
else
{
return v_a_90_;
}
}
case 1:
{
if (v_a_89_ == 0)
{
return v_a_90_;
}
else
{
if (v_a_90_ == 0)
{
return v_a_89_;
}
else
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
}
}
case 2:
{
if (v_a_89_ == 0)
{
if (v_a_90_ == 0)
{
uint8_t v___x_92_; 
v___x_92_ = 1;
return v___x_92_;
}
else
{
return v_a_89_;
}
}
else
{
return v_a_90_;
}
}
default: 
{
if (v_a_89_ == 0)
{
return v_a_90_;
}
else
{
return v_a_89_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_Gate_eval___boxed(lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
uint8_t v_x_229__boxed_96_; uint8_t v_a_230__boxed_97_; uint8_t v_a_231__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_x_229__boxed_96_ = lean_unbox(v_x_93_);
v_a_230__boxed_97_ = lean_unbox(v_a_94_);
v_a_231__boxed_98_ = lean_unbox(v_a_95_);
v_res_99_ = l_Std_Tactic_BVDecide_Gate_eval(v_x_229__boxed_96_, v_a_230__boxed_97_, v_a_231__boxed_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(lean_object* v_x_101_){
_start:
{
switch(lean_obj_tag(v_x_101_))
{
case 0:
{
lean_object* v___x_102_; 
v___x_102_ = lean_unsigned_to_nat(0u);
return v___x_102_;
}
case 1:
{
lean_object* v___x_103_; 
v___x_103_ = lean_unsigned_to_nat(1u);
return v___x_103_;
}
case 2:
{
lean_object* v___x_104_; 
v___x_104_ = lean_unsigned_to_nat(2u);
return v___x_104_;
}
case 3:
{
lean_object* v___x_105_; 
v___x_105_ = lean_unsigned_to_nat(3u);
return v___x_105_;
}
default: 
{
lean_object* v___x_106_; 
v___x_106_ = lean_unsigned_to_nat(4u);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg___boxed(lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(v_x_107_);
lean_dec_ref(v_x_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx(lean_object* v_00_u03b1_109_, lean_object* v_x_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(v_x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___boxed(lean_object* v_00_u03b1_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx(v_00_u03b1_112_, v_x_113_);
lean_dec_ref(v_x_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(lean_object* v_t_115_, lean_object* v_k_116_){
_start:
{
switch(lean_obj_tag(v_t_115_))
{
case 0:
{
lean_object* v_a_117_; lean_object* v___x_118_; 
v_a_117_ = lean_ctor_get(v_t_115_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v_t_115_, 1);
v___x_118_ = lean_apply_1(v_k_116_, v_a_117_);
return v___x_118_;
}
case 1:
{
uint8_t v_a_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_a_119_ = lean_ctor_get_uint8(v_t_115_, 0);
lean_dec_ref_known(v_t_115_, 0);
v___x_120_ = lean_box(v_a_119_);
v___x_121_ = lean_apply_1(v_k_116_, v___x_120_);
return v___x_121_;
}
case 2:
{
lean_object* v_a_122_; lean_object* v___x_123_; 
v_a_122_ = lean_ctor_get(v_t_115_, 0);
lean_inc_ref(v_a_122_);
lean_dec_ref_known(v_t_115_, 1);
v___x_123_ = lean_apply_1(v_k_116_, v_a_122_);
return v___x_123_;
}
case 3:
{
uint8_t v_a_124_; lean_object* v_a_125_; lean_object* v_a_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_a_124_ = lean_ctor_get_uint8(v_t_115_, sizeof(void*)*2);
v_a_125_ = lean_ctor_get(v_t_115_, 0);
lean_inc_ref(v_a_125_);
v_a_126_ = lean_ctor_get(v_t_115_, 1);
lean_inc_ref(v_a_126_);
lean_dec_ref_known(v_t_115_, 2);
v___x_127_ = lean_box(v_a_124_);
v___x_128_ = lean_apply_3(v_k_116_, v___x_127_, v_a_125_, v_a_126_);
return v___x_128_;
}
default: 
{
lean_object* v_a_129_; lean_object* v_a_130_; lean_object* v_a_131_; lean_object* v___x_132_; 
v_a_129_ = lean_ctor_get(v_t_115_, 0);
lean_inc_ref(v_a_129_);
v_a_130_ = lean_ctor_get(v_t_115_, 1);
lean_inc_ref(v_a_130_);
v_a_131_ = lean_ctor_get(v_t_115_, 2);
lean_inc_ref(v_a_131_);
lean_dec_ref_known(v_t_115_, 3);
v___x_132_ = lean_apply_3(v_k_116_, v_a_129_, v_a_130_, v_a_131_);
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim(lean_object* v_00_u03b1_133_, lean_object* v_motive_134_, lean_object* v_ctorIdx_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_k_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_136_, v_k_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ctorElim___boxed(lean_object* v_00_u03b1_140_, lean_object* v_motive_141_, lean_object* v_ctorIdx_142_, lean_object* v_t_143_, lean_object* v_h_144_, lean_object* v_k_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim(v_00_u03b1_140_, v_motive_141_, v_ctorIdx_142_, v_t_143_, v_h_144_, v_k_145_);
lean_dec(v_ctorIdx_142_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim___redArg(lean_object* v_t_147_, lean_object* v_literal_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_147_, v_literal_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_literal_elim(lean_object* v_00_u03b1_150_, lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_literal_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_152_, v_literal_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim___redArg(lean_object* v_t_156_, lean_object* v_const_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_156_, v_const_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_const_elim(lean_object* v_00_u03b1_159_, lean_object* v_motive_160_, lean_object* v_t_161_, lean_object* v_h_162_, lean_object* v_const_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_161_, v_const_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim___redArg(lean_object* v_t_165_, lean_object* v_not_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_165_, v_not_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_not_elim(lean_object* v_00_u03b1_168_, lean_object* v_motive_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_not_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_170_, v_not_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim___redArg(lean_object* v_t_174_, lean_object* v_gate_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_174_, v_gate_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_gate_elim(lean_object* v_00_u03b1_177_, lean_object* v_motive_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_gate_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_179_, v_gate_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim___redArg(lean_object* v_t_183_, lean_object* v_ite_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_183_, v_ite_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_ite_elim(lean_object* v_00_u03b1_186_, lean_object* v_motive_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_ite_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_188_, v_ite_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(lean_object* v_inst_199_, lean_object* v_x_200_){
_start:
{
switch(lean_obj_tag(v_x_200_))
{
case 0:
{
lean_object* v_a_201_; lean_object* v___x_202_; 
v_a_201_ = lean_ctor_get(v_x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v_x_200_, 1);
v___x_202_ = lean_apply_1(v_inst_199_, v_a_201_);
return v___x_202_;
}
case 1:
{
uint8_t v_a_203_; 
lean_dec_ref(v_inst_199_);
v_a_203_ = lean_ctor_get_uint8(v_x_200_, 0);
lean_dec_ref_known(v_x_200_, 0);
if (v_a_203_ == 0)
{
lean_object* v___x_204_; 
v___x_204_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0));
return v___x_204_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1));
return v___x_205_;
}
}
case 2:
{
lean_object* v_a_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_a_206_ = lean_ctor_get(v_x_200_, 0);
lean_inc_ref(v_a_206_);
lean_dec_ref_known(v_x_200_, 1);
v___x_207_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2));
v___x_208_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_199_, v_a_206_);
v___x_209_ = lean_string_append(v___x_207_, v___x_208_);
lean_dec_ref(v___x_208_);
return v___x_209_;
}
case 3:
{
uint8_t v_a_210_; lean_object* v_a_211_; lean_object* v_a_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_a_210_ = lean_ctor_get_uint8(v_x_200_, sizeof(void*)*2);
v_a_211_ = lean_ctor_get(v_x_200_, 0);
lean_inc_ref(v_a_211_);
v_a_212_ = lean_ctor_get(v_x_200_, 1);
lean_inc_ref(v_a_212_);
lean_dec_ref_known(v_x_200_, 2);
v___x_213_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3));
lean_inc_ref(v_inst_199_);
v___x_214_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_199_, v_a_211_);
v___x_215_ = lean_string_append(v___x_213_, v___x_214_);
lean_dec_ref(v___x_214_);
v___x_216_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4));
v___x_217_ = lean_string_append(v___x_215_, v___x_216_);
v___x_218_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_210_);
v___x_219_ = lean_string_append(v___x_217_, v___x_218_);
lean_dec_ref(v___x_218_);
v___x_220_ = lean_string_append(v___x_219_, v___x_216_);
v___x_221_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_199_, v_a_212_);
v___x_222_ = lean_string_append(v___x_220_, v___x_221_);
lean_dec_ref(v___x_221_);
v___x_223_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5));
v___x_224_ = lean_string_append(v___x_222_, v___x_223_);
return v___x_224_;
}
default: 
{
lean_object* v_a_225_; lean_object* v_a_226_; lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_a_225_ = lean_ctor_get(v_x_200_, 0);
lean_inc_ref(v_a_225_);
v_a_226_ = lean_ctor_get(v_x_200_, 1);
lean_inc_ref(v_a_226_);
v_a_227_ = lean_ctor_get(v_x_200_, 2);
lean_inc_ref(v_a_227_);
lean_dec_ref_known(v_x_200_, 3);
v___x_228_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6));
lean_inc_ref_n(v_inst_199_, 2);
v___x_229_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_199_, v_a_225_);
v___x_230_ = lean_string_append(v___x_228_, v___x_229_);
lean_dec_ref(v___x_229_);
v___x_231_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4));
v___x_232_ = lean_string_append(v___x_230_, v___x_231_);
v___x_233_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_199_, v_a_226_);
v___x_234_ = lean_string_append(v___x_232_, v___x_233_);
lean_dec_ref(v___x_233_);
v___x_235_ = lean_string_append(v___x_234_, v___x_231_);
v___x_236_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_199_, v_a_227_);
v___x_237_ = lean_string_append(v___x_235_, v___x_236_);
lean_dec_ref(v___x_236_);
v___x_238_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5));
v___x_239_ = lean_string_append(v___x_237_, v___x_238_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString(lean_object* v_00_u03b1_240_, lean_object* v_inst_241_, lean_object* v_x_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_241_, v_x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString___redArg(lean_object* v_inst_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BoolExpr_toString), 3, 2);
lean_closure_set(v___x_245_, 0, lean_box(0));
lean_closure_set(v___x_245_, 1, v_inst_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_instToString(lean_object* v_00_u03b1_246_, lean_object* v_inst_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BoolExpr_toString), 3, 2);
lean_closure_set(v___x_248_, 0, lean_box(0));
lean_closure_set(v___x_248_, 1, v_inst_247_);
return v___x_248_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(lean_object* v_a_249_, lean_object* v_x_250_){
_start:
{
switch(lean_obj_tag(v_x_250_))
{
case 0:
{
lean_object* v_a_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_a_251_ = lean_ctor_get(v_x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v_x_250_, 1);
v___x_252_ = lean_apply_1(v_a_249_, v_a_251_);
v___x_253_ = lean_unbox(v___x_252_);
return v___x_253_;
}
case 1:
{
uint8_t v_a_254_; 
lean_dec_ref(v_a_249_);
v_a_254_ = lean_ctor_get_uint8(v_x_250_, 0);
lean_dec_ref_known(v_x_250_, 0);
return v_a_254_;
}
case 2:
{
lean_object* v_a_255_; uint8_t v___x_256_; 
v_a_255_ = lean_ctor_get(v_x_250_, 0);
lean_inc_ref(v_a_255_);
lean_dec_ref_known(v_x_250_, 1);
v___x_256_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_249_, v_a_255_);
if (v___x_256_ == 0)
{
uint8_t v___x_257_; 
v___x_257_ = 1;
return v___x_257_;
}
else
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
}
case 3:
{
uint8_t v_a_259_; lean_object* v_a_260_; lean_object* v_a_261_; uint8_t v___x_262_; uint8_t v___x_263_; uint8_t v___x_264_; 
v_a_259_ = lean_ctor_get_uint8(v_x_250_, sizeof(void*)*2);
v_a_260_ = lean_ctor_get(v_x_250_, 0);
lean_inc_ref(v_a_260_);
v_a_261_ = lean_ctor_get(v_x_250_, 1);
lean_inc_ref(v_a_261_);
lean_dec_ref_known(v_x_250_, 2);
lean_inc_ref(v_a_249_);
v___x_262_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_249_, v_a_260_);
v___x_263_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_249_, v_a_261_);
v___x_264_ = l_Std_Tactic_BVDecide_Gate_eval(v_a_259_, v___x_262_, v___x_263_);
return v___x_264_;
}
default: 
{
lean_object* v_a_265_; lean_object* v_a_266_; lean_object* v_a_267_; uint8_t v___x_268_; 
v_a_265_ = lean_ctor_get(v_x_250_, 0);
lean_inc_ref(v_a_265_);
v_a_266_ = lean_ctor_get(v_x_250_, 1);
lean_inc_ref(v_a_266_);
v_a_267_ = lean_ctor_get(v_x_250_, 2);
lean_inc_ref(v_a_267_);
lean_dec_ref_known(v_x_250_, 3);
lean_inc_ref(v_a_249_);
v___x_268_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_249_, v_a_265_);
if (v___x_268_ == 0)
{
lean_dec_ref(v_a_266_);
v_x_250_ = v_a_267_;
goto _start;
}
else
{
lean_dec_ref(v_a_267_);
v_x_250_ = v_a_266_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___redArg___boxed(lean_object* v_a_271_, lean_object* v_x_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_271_, v_x_272_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval(lean_object* v_00_u03b1_275_, lean_object* v_a_276_, lean_object* v_x_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_276_, v_x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_eval___boxed(lean_object* v_00_u03b1_279_, lean_object* v_a_280_, lean_object* v_x_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l_Std_Tactic_BVDecide_BoolExpr_eval(v_00_u03b1_279_, v_a_280_, v_x_281_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg(uint8_t v_x_284_, lean_object* v_h__1_285_, lean_object* v_h__2_286_, lean_object* v_h__3_287_, lean_object* v_h__4_288_){
_start:
{
switch(v_x_284_)
{
case 0:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_h__4_288_);
lean_dec(v_h__3_287_);
lean_dec(v_h__2_286_);
v___x_289_ = lean_box(0);
v___x_290_ = lean_apply_1(v_h__1_285_, v___x_289_);
return v___x_290_;
}
case 1:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v_h__4_288_);
lean_dec(v_h__3_287_);
lean_dec(v_h__1_285_);
v___x_291_ = lean_box(0);
v___x_292_ = lean_apply_1(v_h__2_286_, v___x_291_);
return v___x_292_;
}
case 2:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec(v_h__4_288_);
lean_dec(v_h__2_286_);
lean_dec(v_h__1_285_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_apply_1(v_h__3_287_, v___x_293_);
return v___x_294_;
}
default: 
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v_h__3_287_);
lean_dec(v_h__2_286_);
lean_dec(v_h__1_285_);
v___x_295_ = lean_box(0);
v___x_296_ = lean_apply_1(v_h__4_288_, v___x_295_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg___boxed(lean_object* v_x_297_, lean_object* v_h__1_298_, lean_object* v_h__2_299_, lean_object* v_h__3_300_, lean_object* v_h__4_301_){
_start:
{
uint8_t v_x_42__boxed_302_; lean_object* v_res_303_; 
v_x_42__boxed_302_ = lean_unbox(v_x_297_);
v_res_303_ = l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg(v_x_42__boxed_302_, v_h__1_298_, v_h__2_299_, v_h__3_300_, v_h__4_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter(lean_object* v_motive_304_, uint8_t v_x_305_, lean_object* v_h__1_306_, lean_object* v_h__2_307_, lean_object* v_h__3_308_, lean_object* v_h__4_309_){
_start:
{
switch(v_x_305_)
{
case 0:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_h__4_309_);
lean_dec(v_h__3_308_);
lean_dec(v_h__2_307_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_apply_1(v_h__1_306_, v___x_310_);
return v___x_311_;
}
case 1:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v_h__4_309_);
lean_dec(v_h__3_308_);
lean_dec(v_h__1_306_);
v___x_312_ = lean_box(0);
v___x_313_ = lean_apply_1(v_h__2_307_, v___x_312_);
return v___x_313_;
}
case 2:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_h__4_309_);
lean_dec(v_h__2_307_);
lean_dec(v_h__1_306_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_apply_1(v_h__3_308_, v___x_314_);
return v___x_315_;
}
default: 
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_h__3_308_);
lean_dec(v_h__2_307_);
lean_dec(v_h__1_306_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_apply_1(v_h__4_309_, v___x_316_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___boxed(lean_object* v_motive_318_, lean_object* v_x_319_, lean_object* v_h__1_320_, lean_object* v_h__2_321_, lean_object* v_h__3_322_, lean_object* v_h__4_323_){
_start:
{
uint8_t v_x_61__boxed_324_; lean_object* v_res_325_; 
v_x_61__boxed_324_ = lean_unbox(v_x_319_);
v_res_325_ = l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter(v_motive_318_, v_x_61__boxed_324_, v_h__1_320_, v_h__2_321_, v_h__3_322_, v_h__4_323_);
return v_res_325_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
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
