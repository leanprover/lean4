// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Assignment
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Entails public import Std.Tactic.BVDecide.LRAT.Internal.PosFin public import Init.Grind
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment_default;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqAssignment(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqAssignment___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pos"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "both"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "unassigned"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasPosAssignment(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasPosAssignment___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasNegAssignment(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasNegAssignment___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addPosAssignment(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addPosAssignment___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removePosAssignment(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removePosAssignment___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addNegAssignment(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addNegAssignment___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeNegAssignment(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeNegAssignment___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instEntailsPosFinArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instEntailsPosFinArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_boxed_7_; lean_object* v_res_8_; 
v_x_boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_x_boxed_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCtorIdx(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCtorIdx___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_x_4__boxed_12_; lean_object* v_res_13_; 
v_x_4__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCtorIdx(v_x_4__boxed_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___redArg(lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___redArg___boxed(lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___redArg(v_k_15_);
lean_dec(v_k_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, uint8_t v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_inc(v_k_21_);
return v_k_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
uint8_t v_t_boxed_27_; lean_object* v_res_28_; 
v_t_boxed_27_ = lean_unbox(v_t_24_);
v_res_28_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_boxed_27_, v_h_25_, v_k_26_);
lean_dec(v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___redArg(lean_object* v_pos_29_){
_start:
{
lean_inc(v_pos_29_);
return v_pos_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___redArg___boxed(lean_object* v_pos_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___redArg(v_pos_30_);
lean_dec(v_pos_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim(lean_object* v_motive_32_, uint8_t v_t_33_, lean_object* v_h_34_, lean_object* v_pos_35_){
_start:
{
lean_inc(v_pos_35_);
return v_pos_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_pos_39_){
_start:
{
uint8_t v_t_boxed_40_; lean_object* v_res_41_; 
v_t_boxed_40_ = lean_unbox(v_t_37_);
v_res_41_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim(v_motive_36_, v_t_boxed_40_, v_h_38_, v_pos_39_);
lean_dec(v_pos_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___redArg(lean_object* v_neg_42_){
_start:
{
lean_inc(v_neg_42_);
return v_neg_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___redArg___boxed(lean_object* v_neg_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___redArg(v_neg_43_);
lean_dec(v_neg_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim(lean_object* v_motive_45_, uint8_t v_t_46_, lean_object* v_h_47_, lean_object* v_neg_48_){
_start:
{
lean_inc(v_neg_48_);
return v_neg_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_neg_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_neg_52_);
lean_dec(v_neg_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___redArg(lean_object* v_both_55_){
_start:
{
lean_inc(v_both_55_);
return v_both_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___redArg___boxed(lean_object* v_both_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___redArg(v_both_56_);
lean_dec(v_both_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_both_61_){
_start:
{
lean_inc(v_both_61_);
return v_both_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_both_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_both_65_);
lean_dec(v_both_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___redArg(lean_object* v_unassigned_68_){
_start:
{
lean_inc(v_unassigned_68_);
return v_unassigned_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___redArg___boxed(lean_object* v_unassigned_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___redArg(v_unassigned_69_);
lean_dec(v_unassigned_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_unassigned_74_){
_start:
{
lean_inc(v_unassigned_74_);
return v_unassigned_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_unassigned_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_unassigned_78_);
lean_dec(v_unassigned_78_);
return v_res_80_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment_default(void){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment(void){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofNat(lean_object* v_n_83_){
_start:
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = lean_nat_dec_le(v_n_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(2u);
v___x_87_ = lean_nat_dec_le(v_n_83_, v___x_86_);
if (v___x_87_ == 0)
{
uint8_t v___x_88_; 
v___x_88_ = 3;
return v___x_88_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = 2;
return v___x_89_;
}
}
else
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_nat_dec_le(v_n_83_, v___x_90_);
if (v___x_91_ == 0)
{
uint8_t v___x_92_; 
v___x_92_ = 1;
return v___x_92_;
}
else
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofNat___boxed(lean_object* v_n_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofNat(v_n_94_);
lean_dec(v_n_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqAssignment(uint8_t v_x_97_, uint8_t v_y_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_99_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_x_97_);
v___x_100_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_y_98_);
v___x_101_ = lean_nat_dec_eq(v___x_99_, v___x_100_);
lean_dec(v___x_100_);
lean_dec(v___x_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqAssignment___boxed(lean_object* v_x_102_, lean_object* v_y_103_){
_start:
{
uint8_t v_x_13__boxed_104_; uint8_t v_y_14__boxed_105_; uint8_t v_res_106_; lean_object* v_r_107_; 
v_x_13__boxed_104_ = lean_unbox(v_x_102_);
v_y_14__boxed_105_ = lean_unbox(v_y_103_);
v_res_106_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqAssignment(v_x_13__boxed_104_, v_y_14__boxed_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq(uint8_t v_x_108_, uint8_t v_y_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_110_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_x_108_);
v___x_111_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_y_109_);
v___x_112_ = lean_nat_dec_eq(v___x_110_, v___x_111_);
lean_dec(v___x_111_);
lean_dec(v___x_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq___boxed(lean_object* v_x_113_, lean_object* v_y_114_){
_start:
{
uint8_t v_x_17__boxed_115_; uint8_t v_y_18__boxed_116_; uint8_t v_res_117_; lean_object* v_r_118_; 
v_x_17__boxed_115_ = lean_unbox(v_x_113_);
v_y_18__boxed_116_ = lean_unbox(v_y_114_);
v_res_117_ = l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq(v_x_17__boxed_115_, v_y_18__boxed_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0(uint8_t v_a_125_){
_start:
{
switch(v_a_125_)
{
case 0:
{
lean_object* v___x_126_; 
v___x_126_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__0));
return v___x_126_;
}
case 1:
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__1));
return v___x_127_;
}
case 2:
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__2));
return v___x_128_;
}
default: 
{
lean_object* v___x_129_; 
v___x_129_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__3));
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___boxed(lean_object* v_a_130_){
_start:
{
uint8_t v_a_boxed_131_; lean_object* v_res_132_; 
v_a_boxed_131_ = lean_unbox(v_a_130_);
v_res_132_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0(v_a_boxed_131_);
return v_res_132_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasPosAssignment(uint8_t v_assignment_135_){
_start:
{
switch(v_assignment_135_)
{
case 1:
{
uint8_t v___x_136_; 
v___x_136_ = 0;
return v___x_136_;
}
case 3:
{
uint8_t v___x_137_; 
v___x_137_ = 0;
return v___x_137_;
}
default: 
{
uint8_t v___x_138_; 
v___x_138_ = 1;
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasPosAssignment___boxed(lean_object* v_assignment_139_){
_start:
{
uint8_t v_assignment_boxed_140_; uint8_t v_res_141_; lean_object* v_r_142_; 
v_assignment_boxed_140_ = lean_unbox(v_assignment_139_);
v_res_141_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasPosAssignment(v_assignment_boxed_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasNegAssignment(uint8_t v_assignment_143_){
_start:
{
switch(v_assignment_143_)
{
case 1:
{
uint8_t v___x_144_; 
v___x_144_ = 1;
return v___x_144_;
}
case 2:
{
uint8_t v___x_145_; 
v___x_145_ = 1;
return v___x_145_;
}
default: 
{
uint8_t v___x_146_; 
v___x_146_ = 0;
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasNegAssignment___boxed(lean_object* v_assignment_147_){
_start:
{
uint8_t v_assignment_boxed_148_; uint8_t v_res_149_; lean_object* v_r_150_; 
v_assignment_boxed_148_ = lean_unbox(v_assignment_147_);
v_res_149_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasNegAssignment(v_assignment_boxed_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addPosAssignment(uint8_t v_oldAssignment_151_){
_start:
{
switch(v_oldAssignment_151_)
{
case 1:
{
uint8_t v___x_152_; 
v___x_152_ = 2;
return v___x_152_;
}
case 3:
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
default: 
{
return v_oldAssignment_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addPosAssignment___boxed(lean_object* v_oldAssignment_154_){
_start:
{
uint8_t v_oldAssignment_boxed_155_; uint8_t v_res_156_; lean_object* v_r_157_; 
v_oldAssignment_boxed_155_ = lean_unbox(v_oldAssignment_154_);
v_res_156_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addPosAssignment(v_oldAssignment_boxed_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removePosAssignment(uint8_t v_oldAssignment_158_){
_start:
{
switch(v_oldAssignment_158_)
{
case 0:
{
uint8_t v___x_159_; 
v___x_159_ = 3;
return v___x_159_;
}
case 2:
{
uint8_t v___x_160_; 
v___x_160_ = 1;
return v___x_160_;
}
default: 
{
return v_oldAssignment_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removePosAssignment___boxed(lean_object* v_oldAssignment_161_){
_start:
{
uint8_t v_oldAssignment_boxed_162_; uint8_t v_res_163_; lean_object* v_r_164_; 
v_oldAssignment_boxed_162_ = lean_unbox(v_oldAssignment_161_);
v_res_163_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removePosAssignment(v_oldAssignment_boxed_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addNegAssignment(uint8_t v_oldAssignment_165_){
_start:
{
switch(v_oldAssignment_165_)
{
case 0:
{
uint8_t v___x_166_; 
v___x_166_ = 2;
return v___x_166_;
}
case 3:
{
uint8_t v___x_167_; 
v___x_167_ = 1;
return v___x_167_;
}
default: 
{
return v_oldAssignment_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addNegAssignment___boxed(lean_object* v_oldAssignment_168_){
_start:
{
uint8_t v_oldAssignment_boxed_169_; uint8_t v_res_170_; lean_object* v_r_171_; 
v_oldAssignment_boxed_169_ = lean_unbox(v_oldAssignment_168_);
v_res_170_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addNegAssignment(v_oldAssignment_boxed_169_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeNegAssignment(uint8_t v_oldAssignment_172_){
_start:
{
switch(v_oldAssignment_172_)
{
case 1:
{
uint8_t v___x_173_; 
v___x_173_ = 3;
return v___x_173_;
}
case 2:
{
uint8_t v___x_174_; 
v___x_174_ = 0;
return v___x_174_;
}
default: 
{
return v_oldAssignment_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeNegAssignment___boxed(lean_object* v_oldAssignment_175_){
_start:
{
uint8_t v_oldAssignment_boxed_176_; uint8_t v_res_177_; lean_object* v_r_178_; 
v_oldAssignment_boxed_176_ = lean_unbox(v_oldAssignment_175_);
v_res_177_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeNegAssignment(v_oldAssignment_boxed_176_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(uint8_t v_a_179_, lean_object* v_h__1_180_, lean_object* v_h__2_181_, lean_object* v_h__3_182_, lean_object* v_h__4_183_){
_start:
{
switch(v_a_179_)
{
case 0:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_h__4_183_);
lean_dec(v_h__3_182_);
lean_dec(v_h__2_181_);
v___x_184_ = lean_box(0);
v___x_185_ = lean_apply_1(v_h__1_180_, v___x_184_);
return v___x_185_;
}
case 1:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v_h__4_183_);
lean_dec(v_h__3_182_);
lean_dec(v_h__1_180_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_apply_1(v_h__2_181_, v___x_186_);
return v___x_187_;
}
case 2:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_h__4_183_);
lean_dec(v_h__2_181_);
lean_dec(v_h__1_180_);
v___x_188_ = lean_box(0);
v___x_189_ = lean_apply_1(v_h__3_182_, v___x_188_);
return v___x_189_;
}
default: 
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v_h__3_182_);
lean_dec(v_h__2_181_);
lean_dec(v_h__1_180_);
v___x_190_ = lean_box(0);
v___x_191_ = lean_apply_1(v_h__4_183_, v___x_190_);
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(lean_object* v_a_192_, lean_object* v_h__1_193_, lean_object* v_h__2_194_, lean_object* v_h__3_195_, lean_object* v_h__4_196_){
_start:
{
uint8_t v_a_46__boxed_197_; lean_object* v_res_198_; 
v_a_46__boxed_197_ = lean_unbox(v_a_192_);
v_res_198_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_46__boxed_197_, v_h__1_193_, v_h__2_194_, v_h__3_195_, v_h__4_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(lean_object* v_motive_199_, uint8_t v_a_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_, lean_object* v_h__3_203_, lean_object* v_h__4_204_){
_start:
{
switch(v_a_200_)
{
case 0:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v_h__4_204_);
lean_dec(v_h__3_203_);
lean_dec(v_h__2_202_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_apply_1(v_h__1_201_, v___x_205_);
return v___x_206_;
}
case 1:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v_h__4_204_);
lean_dec(v_h__3_203_);
lean_dec(v_h__1_201_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_apply_1(v_h__2_202_, v___x_207_);
return v___x_208_;
}
case 2:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_h__4_204_);
lean_dec(v_h__2_202_);
lean_dec(v_h__1_201_);
v___x_209_ = lean_box(0);
v___x_210_ = lean_apply_1(v_h__3_203_, v___x_209_);
return v___x_210_;
}
default: 
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_h__3_203_);
lean_dec(v_h__2_202_);
lean_dec(v_h__1_201_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_apply_1(v_h__4_204_, v___x_211_);
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(lean_object* v_motive_213_, lean_object* v_a_214_, lean_object* v_h__1_215_, lean_object* v_h__2_216_, lean_object* v_h__3_217_, lean_object* v_h__4_218_){
_start:
{
uint8_t v_a_65__boxed_219_; lean_object* v_res_220_; 
v_a_65__boxed_219_ = lean_unbox(v_a_214_);
v_res_220_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(v_motive_213_, v_a_65__boxed_219_, v_h__1_215_, v_h__2_216_, v_h__3_217_, v_h__4_218_);
return v_res_220_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(uint8_t v_b_221_, uint8_t v_a_222_){
_start:
{
if (v_b_221_ == 0)
{
switch(v_a_222_)
{
case 0:
{
uint8_t v___x_223_; 
v___x_223_ = 2;
return v___x_223_;
}
case 3:
{
uint8_t v___x_224_; 
v___x_224_ = 1;
return v___x_224_;
}
default: 
{
return v_a_222_;
}
}
}
else
{
switch(v_a_222_)
{
case 1:
{
uint8_t v___x_225_; 
v___x_225_ = 2;
return v___x_225_;
}
case 3:
{
uint8_t v___x_226_; 
v___x_226_ = 0;
return v___x_226_;
}
default: 
{
return v_a_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment___boxed(lean_object* v_b_227_, lean_object* v_a_228_){
_start:
{
uint8_t v_b_boxed_229_; uint8_t v_a_boxed_230_; uint8_t v_res_231_; lean_object* v_r_232_; 
v_b_boxed_229_ = lean_unbox(v_b_227_);
v_a_boxed_230_ = lean_unbox(v_a_228_);
v_res_231_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(v_b_boxed_229_, v_a_boxed_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(uint8_t v_b_233_, uint8_t v_a_234_){
_start:
{
if (v_b_233_ == 0)
{
switch(v_a_234_)
{
case 1:
{
uint8_t v___x_235_; 
v___x_235_ = 3;
return v___x_235_;
}
case 2:
{
uint8_t v___x_236_; 
v___x_236_ = 0;
return v___x_236_;
}
default: 
{
return v_a_234_;
}
}
}
else
{
switch(v_a_234_)
{
case 0:
{
uint8_t v___x_237_; 
v___x_237_ = 3;
return v___x_237_;
}
case 2:
{
uint8_t v___x_238_; 
v___x_238_ = 1;
return v___x_238_;
}
default: 
{
return v_a_234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment___boxed(lean_object* v_b_239_, lean_object* v_a_240_){
_start:
{
uint8_t v_b_boxed_241_; uint8_t v_a_boxed_242_; uint8_t v_res_243_; lean_object* v_r_244_; 
v_b_boxed_241_ = lean_unbox(v_b_239_);
v_a_boxed_242_ = lean_unbox(v_a_240_);
v_res_243_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(v_b_boxed_241_, v_a_boxed_242_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(uint8_t v_b_245_, uint8_t v_a_246_){
_start:
{
if (v_b_245_ == 0)
{
switch(v_a_246_)
{
case 1:
{
uint8_t v___x_247_; 
v___x_247_ = 1;
return v___x_247_;
}
case 2:
{
uint8_t v___x_248_; 
v___x_248_ = 1;
return v___x_248_;
}
default: 
{
return v_b_245_;
}
}
}
else
{
switch(v_a_246_)
{
case 1:
{
uint8_t v___x_249_; 
v___x_249_ = 0;
return v___x_249_;
}
case 3:
{
uint8_t v___x_250_; 
v___x_250_ = 0;
return v___x_250_;
}
default: 
{
return v_b_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment___boxed(lean_object* v_b_251_, lean_object* v_a_252_){
_start:
{
uint8_t v_b_boxed_253_; uint8_t v_a_boxed_254_; uint8_t v_res_255_; lean_object* v_r_256_; 
v_b_boxed_253_ = lean_unbox(v_b_251_);
v_a_boxed_254_ = lean_unbox(v_a_252_);
v_res_255_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(v_b_boxed_253_, v_a_boxed_254_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instEntailsPosFinArray(lean_object* v_n_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_box(0);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instEntailsPosFinArray___boxed(lean_object* v_n_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instEntailsPosFinArray(v_n_259_);
lean_dec(v_n_259_);
return v_res_260_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment_default = _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment_default();
l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment = _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
}
#ifdef __cplusplus
}
#endif
