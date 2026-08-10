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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___redArg(lean_object* v_k_9_){
_start:
{
lean_inc(v_k_9_);
return v_k_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___redArg___boxed(lean_object* v_k_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___redArg(v_k_10_);
lean_dec(v_k_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, uint8_t v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___redArg(lean_object* v_pos_24_){
_start:
{
lean_inc(v_pos_24_);
return v_pos_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___redArg___boxed(lean_object* v_pos_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___redArg(v_pos_25_);
lean_dec(v_pos_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_pos_30_){
_start:
{
lean_inc(v_pos_30_);
return v_pos_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___boxed(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_pos_34_){
_start:
{
uint8_t v_t_boxed_35_; lean_object* v_res_36_; 
v_t_boxed_35_ = lean_unbox(v_t_32_);
v_res_36_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim(v_motive_31_, v_t_boxed_35_, v_h_33_, v_pos_34_);
lean_dec(v_pos_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___redArg(lean_object* v_neg_37_){
_start:
{
lean_inc(v_neg_37_);
return v_neg_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___redArg___boxed(lean_object* v_neg_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___redArg(v_neg_38_);
lean_dec(v_neg_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim(lean_object* v_motive_40_, uint8_t v_t_41_, lean_object* v_h_42_, lean_object* v_neg_43_){
_start:
{
lean_inc(v_neg_43_);
return v_neg_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___boxed(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_neg_47_){
_start:
{
uint8_t v_t_boxed_48_; lean_object* v_res_49_; 
v_t_boxed_48_ = lean_unbox(v_t_45_);
v_res_49_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim(v_motive_44_, v_t_boxed_48_, v_h_46_, v_neg_47_);
lean_dec(v_neg_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___redArg(lean_object* v_both_50_){
_start:
{
lean_inc(v_both_50_);
return v_both_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___redArg___boxed(lean_object* v_both_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___redArg(v_both_51_);
lean_dec(v_both_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim(lean_object* v_motive_53_, uint8_t v_t_54_, lean_object* v_h_55_, lean_object* v_both_56_){
_start:
{
lean_inc(v_both_56_);
return v_both_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___boxed(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_both_60_){
_start:
{
uint8_t v_t_boxed_61_; lean_object* v_res_62_; 
v_t_boxed_61_ = lean_unbox(v_t_58_);
v_res_62_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim(v_motive_57_, v_t_boxed_61_, v_h_59_, v_both_60_);
lean_dec(v_both_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___redArg(lean_object* v_unassigned_63_){
_start:
{
lean_inc(v_unassigned_63_);
return v_unassigned_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___redArg___boxed(lean_object* v_unassigned_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___redArg(v_unassigned_64_);
lean_dec(v_unassigned_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim(lean_object* v_motive_66_, uint8_t v_t_67_, lean_object* v_h_68_, lean_object* v_unassigned_69_){
_start:
{
lean_inc(v_unassigned_69_);
return v_unassigned_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___boxed(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_unassigned_73_){
_start:
{
uint8_t v_t_boxed_74_; lean_object* v_res_75_; 
v_t_boxed_74_ = lean_unbox(v_t_71_);
v_res_75_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim(v_motive_70_, v_t_boxed_74_, v_h_72_, v_unassigned_73_);
lean_dec(v_unassigned_73_);
return v_res_75_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment_default(void){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment(void){
_start:
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofNat(lean_object* v_n_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_nat_dec_le(v_n_78_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(2u);
v___x_82_ = lean_nat_dec_le(v_n_78_, v___x_81_);
if (v___x_82_ == 0)
{
uint8_t v___x_83_; 
v___x_83_ = 3;
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 2;
return v___x_84_;
}
}
else
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = lean_nat_dec_le(v_n_78_, v___x_85_);
if (v___x_86_ == 0)
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofNat___boxed(lean_object* v_n_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofNat(v_n_89_);
lean_dec(v_n_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqAssignment(uint8_t v_x_92_, uint8_t v_y_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_94_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_x_92_);
v___x_95_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_y_93_);
v___x_96_ = lean_nat_dec_eq(v___x_94_, v___x_95_);
lean_dec(v___x_95_);
lean_dec(v___x_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqAssignment___boxed(lean_object* v_x_97_, lean_object* v_y_98_){
_start:
{
uint8_t v_x_13__boxed_99_; uint8_t v_y_14__boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_x_13__boxed_99_ = lean_unbox(v_x_97_);
v_y_14__boxed_100_ = lean_unbox(v_y_98_);
v_res_101_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqAssignment(v_x_13__boxed_99_, v_y_14__boxed_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq(uint8_t v_x_103_, uint8_t v_y_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_105_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_x_103_);
v___x_106_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_y_104_);
v___x_107_ = lean_nat_dec_eq(v___x_105_, v___x_106_);
lean_dec(v___x_106_);
lean_dec(v___x_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq___boxed(lean_object* v_x_108_, lean_object* v_y_109_){
_start:
{
uint8_t v_x_17__boxed_110_; uint8_t v_y_18__boxed_111_; uint8_t v_res_112_; lean_object* v_r_113_; 
v_x_17__boxed_110_ = lean_unbox(v_x_108_);
v_y_18__boxed_111_ = lean_unbox(v_y_109_);
v_res_112_ = l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq(v_x_17__boxed_110_, v_y_18__boxed_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0(uint8_t v_a_120_){
_start:
{
switch(v_a_120_)
{
case 0:
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__0));
return v___x_121_;
}
case 1:
{
lean_object* v___x_122_; 
v___x_122_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__1));
return v___x_122_;
}
case 2:
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__2));
return v___x_123_;
}
default: 
{
lean_object* v___x_124_; 
v___x_124_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__3));
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___boxed(lean_object* v_a_125_){
_start:
{
uint8_t v_a_boxed_126_; lean_object* v_res_127_; 
v_a_boxed_126_ = lean_unbox(v_a_125_);
v_res_127_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0(v_a_boxed_126_);
return v_res_127_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasPosAssignment(uint8_t v_assignment_130_){
_start:
{
switch(v_assignment_130_)
{
case 1:
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
case 3:
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
default: 
{
uint8_t v___x_133_; 
v___x_133_ = 1;
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasPosAssignment___boxed(lean_object* v_assignment_134_){
_start:
{
uint8_t v_assignment_boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_assignment_boxed_135_ = lean_unbox(v_assignment_134_);
v_res_136_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasPosAssignment(v_assignment_boxed_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasNegAssignment(uint8_t v_assignment_138_){
_start:
{
switch(v_assignment_138_)
{
case 1:
{
uint8_t v___x_139_; 
v___x_139_ = 1;
return v___x_139_;
}
case 2:
{
uint8_t v___x_140_; 
v___x_140_ = 1;
return v___x_140_;
}
default: 
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasNegAssignment___boxed(lean_object* v_assignment_142_){
_start:
{
uint8_t v_assignment_boxed_143_; uint8_t v_res_144_; lean_object* v_r_145_; 
v_assignment_boxed_143_ = lean_unbox(v_assignment_142_);
v_res_144_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasNegAssignment(v_assignment_boxed_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addPosAssignment(uint8_t v_oldAssignment_146_){
_start:
{
switch(v_oldAssignment_146_)
{
case 1:
{
uint8_t v___x_147_; 
v___x_147_ = 2;
return v___x_147_;
}
case 3:
{
uint8_t v___x_148_; 
v___x_148_ = 0;
return v___x_148_;
}
default: 
{
return v_oldAssignment_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addPosAssignment___boxed(lean_object* v_oldAssignment_149_){
_start:
{
uint8_t v_oldAssignment_boxed_150_; uint8_t v_res_151_; lean_object* v_r_152_; 
v_oldAssignment_boxed_150_ = lean_unbox(v_oldAssignment_149_);
v_res_151_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addPosAssignment(v_oldAssignment_boxed_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removePosAssignment(uint8_t v_oldAssignment_153_){
_start:
{
switch(v_oldAssignment_153_)
{
case 0:
{
uint8_t v___x_154_; 
v___x_154_ = 3;
return v___x_154_;
}
case 2:
{
uint8_t v___x_155_; 
v___x_155_ = 1;
return v___x_155_;
}
default: 
{
return v_oldAssignment_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removePosAssignment___boxed(lean_object* v_oldAssignment_156_){
_start:
{
uint8_t v_oldAssignment_boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v_oldAssignment_boxed_157_ = lean_unbox(v_oldAssignment_156_);
v_res_158_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removePosAssignment(v_oldAssignment_boxed_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addNegAssignment(uint8_t v_oldAssignment_160_){
_start:
{
switch(v_oldAssignment_160_)
{
case 0:
{
uint8_t v___x_161_; 
v___x_161_ = 2;
return v___x_161_;
}
case 3:
{
uint8_t v___x_162_; 
v___x_162_ = 1;
return v___x_162_;
}
default: 
{
return v_oldAssignment_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addNegAssignment___boxed(lean_object* v_oldAssignment_163_){
_start:
{
uint8_t v_oldAssignment_boxed_164_; uint8_t v_res_165_; lean_object* v_r_166_; 
v_oldAssignment_boxed_164_ = lean_unbox(v_oldAssignment_163_);
v_res_165_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addNegAssignment(v_oldAssignment_boxed_164_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeNegAssignment(uint8_t v_oldAssignment_167_){
_start:
{
switch(v_oldAssignment_167_)
{
case 1:
{
uint8_t v___x_168_; 
v___x_168_ = 3;
return v___x_168_;
}
case 2:
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
default: 
{
return v_oldAssignment_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeNegAssignment___boxed(lean_object* v_oldAssignment_170_){
_start:
{
uint8_t v_oldAssignment_boxed_171_; uint8_t v_res_172_; lean_object* v_r_173_; 
v_oldAssignment_boxed_171_ = lean_unbox(v_oldAssignment_170_);
v_res_172_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeNegAssignment(v_oldAssignment_boxed_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(uint8_t v_a_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_, lean_object* v_h__3_177_, lean_object* v_h__4_178_){
_start:
{
switch(v_a_174_)
{
case 0:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_h__4_178_);
lean_dec(v_h__3_177_);
lean_dec(v_h__2_176_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_apply_1(v_h__1_175_, v___x_179_);
return v___x_180_;
}
case 1:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_h__4_178_);
lean_dec(v_h__3_177_);
lean_dec(v_h__1_175_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_apply_1(v_h__2_176_, v___x_181_);
return v___x_182_;
}
case 2:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_h__4_178_);
lean_dec(v_h__2_176_);
lean_dec(v_h__1_175_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_apply_1(v_h__3_177_, v___x_183_);
return v___x_184_;
}
default: 
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_h__3_177_);
lean_dec(v_h__2_176_);
lean_dec(v_h__1_175_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_apply_1(v_h__4_178_, v___x_185_);
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(lean_object* v_a_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_, lean_object* v_h__3_190_, lean_object* v_h__4_191_){
_start:
{
uint8_t v_a_42__boxed_192_; lean_object* v_res_193_; 
v_a_42__boxed_192_ = lean_unbox(v_a_187_);
v_res_193_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_42__boxed_192_, v_h__1_188_, v_h__2_189_, v_h__3_190_, v_h__4_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(lean_object* v_motive_194_, uint8_t v_a_195_, lean_object* v_h__1_196_, lean_object* v_h__2_197_, lean_object* v_h__3_198_, lean_object* v_h__4_199_){
_start:
{
switch(v_a_195_)
{
case 0:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v_h__4_199_);
lean_dec(v_h__3_198_);
lean_dec(v_h__2_197_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_apply_1(v_h__1_196_, v___x_200_);
return v___x_201_;
}
case 1:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_h__4_199_);
lean_dec(v_h__3_198_);
lean_dec(v_h__1_196_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_apply_1(v_h__2_197_, v___x_202_);
return v___x_203_;
}
case 2:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v_h__4_199_);
lean_dec(v_h__2_197_);
lean_dec(v_h__1_196_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_apply_1(v_h__3_198_, v___x_204_);
return v___x_205_;
}
default: 
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v_h__3_198_);
lean_dec(v_h__2_197_);
lean_dec(v_h__1_196_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_apply_1(v_h__4_199_, v___x_206_);
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(lean_object* v_motive_208_, lean_object* v_a_209_, lean_object* v_h__1_210_, lean_object* v_h__2_211_, lean_object* v_h__3_212_, lean_object* v_h__4_213_){
_start:
{
uint8_t v_a_61__boxed_214_; lean_object* v_res_215_; 
v_a_61__boxed_214_ = lean_unbox(v_a_209_);
v_res_215_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(v_motive_208_, v_a_61__boxed_214_, v_h__1_210_, v_h__2_211_, v_h__3_212_, v_h__4_213_);
return v_res_215_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(uint8_t v_b_216_, uint8_t v_a_217_){
_start:
{
if (v_b_216_ == 0)
{
switch(v_a_217_)
{
case 0:
{
uint8_t v___x_218_; 
v___x_218_ = 2;
return v___x_218_;
}
case 3:
{
uint8_t v___x_219_; 
v___x_219_ = 1;
return v___x_219_;
}
default: 
{
return v_a_217_;
}
}
}
else
{
switch(v_a_217_)
{
case 1:
{
uint8_t v___x_220_; 
v___x_220_ = 2;
return v___x_220_;
}
case 3:
{
uint8_t v___x_221_; 
v___x_221_ = 0;
return v___x_221_;
}
default: 
{
return v_a_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment___boxed(lean_object* v_b_222_, lean_object* v_a_223_){
_start:
{
uint8_t v_b_boxed_224_; uint8_t v_a_boxed_225_; uint8_t v_res_226_; lean_object* v_r_227_; 
v_b_boxed_224_ = lean_unbox(v_b_222_);
v_a_boxed_225_ = lean_unbox(v_a_223_);
v_res_226_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(v_b_boxed_224_, v_a_boxed_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(uint8_t v_b_228_, uint8_t v_a_229_){
_start:
{
if (v_b_228_ == 0)
{
switch(v_a_229_)
{
case 1:
{
uint8_t v___x_230_; 
v___x_230_ = 3;
return v___x_230_;
}
case 2:
{
uint8_t v___x_231_; 
v___x_231_ = 0;
return v___x_231_;
}
default: 
{
return v_a_229_;
}
}
}
else
{
switch(v_a_229_)
{
case 0:
{
uint8_t v___x_232_; 
v___x_232_ = 3;
return v___x_232_;
}
case 2:
{
uint8_t v___x_233_; 
v___x_233_ = 1;
return v___x_233_;
}
default: 
{
return v_a_229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment___boxed(lean_object* v_b_234_, lean_object* v_a_235_){
_start:
{
uint8_t v_b_boxed_236_; uint8_t v_a_boxed_237_; uint8_t v_res_238_; lean_object* v_r_239_; 
v_b_boxed_236_ = lean_unbox(v_b_234_);
v_a_boxed_237_ = lean_unbox(v_a_235_);
v_res_238_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(v_b_boxed_236_, v_a_boxed_237_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(uint8_t v_b_240_, uint8_t v_a_241_){
_start:
{
if (v_b_240_ == 0)
{
switch(v_a_241_)
{
case 1:
{
uint8_t v___x_242_; 
v___x_242_ = 1;
return v___x_242_;
}
case 2:
{
uint8_t v___x_243_; 
v___x_243_ = 1;
return v___x_243_;
}
default: 
{
return v_b_240_;
}
}
}
else
{
switch(v_a_241_)
{
case 1:
{
uint8_t v___x_244_; 
v___x_244_ = 0;
return v___x_244_;
}
case 3:
{
uint8_t v___x_245_; 
v___x_245_ = 0;
return v___x_245_;
}
default: 
{
return v_b_240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment___boxed(lean_object* v_b_246_, lean_object* v_a_247_){
_start:
{
uint8_t v_b_boxed_248_; uint8_t v_a_boxed_249_; uint8_t v_res_250_; lean_object* v_r_251_; 
v_b_boxed_248_ = lean_unbox(v_b_246_);
v_a_boxed_249_ = lean_unbox(v_a_247_);
v_res_250_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(v_b_boxed_248_, v_a_boxed_249_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instEntailsPosFinArray(lean_object* v_n_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_box(0);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instEntailsPosFinArray___boxed(lean_object* v_n_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instEntailsPosFinArray(v_n_254_);
lean_dec(v_n_254_);
return v_res_255_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
