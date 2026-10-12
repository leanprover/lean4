// Lean compiler output
// Module: Init.Grind.Ring.Envelope
// Imports: public import Init.Grind.Ordered.Ring import all Init.Data.AC import Init.Omega import Init.RCases
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___redArg();
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___redArg();
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value;
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value;
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value;
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value;
static const lean_ctor_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_0),((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_1),((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_2),((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value;
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "coeNotation"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value;
static const lean_ctor_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 100, 71, 170, 251, 12, 50, 58)}};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6_value;
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "↑"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(lean_object* v_p_1_){
_start:
{
lean_inc_ref(v_p_1_);
return v_p_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg___boxed(lean_object* v_p_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(v_p_2_);
lean_dec_ref(v_p_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk(lean_object* v_00_u03b1_4_, lean_object* v_inst_5_, lean_object* v_p_6_){
_start:
{
lean_inc_ref(v_p_6_);
return v_p_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___boxed(lean_object* v_00_u03b1_7_, lean_object* v_inst_8_, lean_object* v_p_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Grind_Ring_OfSemiring_Q_mk(v_00_u03b1_7_, v_inst_8_, v_p_9_);
lean_dec_ref(v_p_9_);
lean_dec_ref(v_inst_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___redArg(lean_object* v_q_u2081_11_, lean_object* v_q_u2082_12_, lean_object* v_f_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_2(v_f_13_, v_q_u2081_11_, v_q_u2082_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_00_u03b2_17_, lean_object* v_q_u2081_18_, lean_object* v_q_u2082_19_, lean_object* v_f_20_, lean_object* v_h_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_apply_2(v_f_20_, v_q_u2081_18_, v_q_u2082_19_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___boxed(lean_object* v_00_u03b1_23_, lean_object* v_inst_24_, lean_object* v_00_u03b2_25_, lean_object* v_q_u2081_26_, lean_object* v_q_u2082_27_, lean_object* v_f_28_, lean_object* v_h_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(v_00_u03b1_23_, v_inst_24_, v_00_u03b2_25_, v_q_u2081_26_, v_q_u2082_27_, v_f_28_, v_h_29_);
lean_dec_ref(v_inst_24_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast___redArg(lean_object* v_inst_31_, lean_object* v_n_32_){
_start:
{
lean_object* v_natCast_33_; lean_object* v_ofNat_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_natCast_33_ = lean_ctor_get(v_inst_31_, 2);
lean_inc(v_natCast_33_);
v_ofNat_34_ = lean_ctor_get(v_inst_31_, 3);
lean_inc(v_ofNat_34_);
lean_dec_ref(v_inst_31_);
v___x_35_ = lean_apply_1(v_natCast_33_, v_n_32_);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_apply_1(v_ofNat_34_, v___x_36_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_35_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast(lean_object* v_00_u03b1_39_, lean_object* v_inst_40_, lean_object* v_n_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_40_, v_n_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_nat_to_int(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg(lean_object* v_inst_45_, lean_object* v_n_46_){
_start:
{
lean_object* v_natCast_47_; lean_object* v_ofNat_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_natCast_47_ = lean_ctor_get(v_inst_45_, 2);
lean_inc(v_natCast_47_);
v_ofNat_48_ = lean_ctor_get(v_inst_45_, 3);
lean_inc(v_ofNat_48_);
lean_dec_ref(v_inst_45_);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_obj_once(&l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0, &l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0_once, _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0);
v___x_51_ = lean_int_dec_lt(v_n_46_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_nat_abs(v_n_46_);
v___x_53_ = lean_apply_1(v_natCast_47_, v___x_52_);
v___x_54_ = lean_apply_1(v_ofNat_48_, v___x_49_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_apply_1(v_ofNat_48_, v___x_49_);
v___x_57_ = lean_nat_abs(v_n_46_);
v___x_58_ = lean_apply_1(v_natCast_47_, v___x_57_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_56_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg___boxed(lean_object* v_inst_60_, lean_object* v_n_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_60_, v_n_61_);
lean_dec(v_n_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast(lean_object* v_00_u03b1_63_, lean_object* v_inst_64_, lean_object* v_n_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_64_, v_n_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___boxed(lean_object* v_00_u03b1_67_, lean_object* v_inst_68_, lean_object* v_n_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Grind_Ring_OfSemiring_intCast(v_00_u03b1_67_, v_inst_68_, v_n_69_);
lean_dec(v_n_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub___redArg(lean_object* v_inst_71_, lean_object* v_q_u2081_72_, lean_object* v_q_u2082_73_){
_start:
{
lean_object* v_toAdd_74_; lean_object* v_fst_75_; lean_object* v_snd_76_; lean_object* v_fst_77_; lean_object* v_snd_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_87_; 
v_toAdd_74_ = lean_ctor_get(v_inst_71_, 0);
lean_inc(v_toAdd_74_);
lean_dec_ref(v_inst_71_);
v_fst_75_ = lean_ctor_get(v_q_u2081_72_, 0);
lean_inc(v_fst_75_);
v_snd_76_ = lean_ctor_get(v_q_u2081_72_, 1);
lean_inc(v_snd_76_);
lean_dec(v_q_u2081_72_);
v_fst_77_ = lean_ctor_get(v_q_u2082_73_, 0);
v_snd_78_ = lean_ctor_get(v_q_u2082_73_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_q_u2082_73_);
if (v_isSharedCheck_87_ == 0)
{
v___x_80_ = v_q_u2082_73_;
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_snd_78_);
lean_inc(v_fst_77_);
lean_dec(v_q_u2082_73_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
lean_inc(v_toAdd_74_);
v___x_82_ = lean_apply_2(v_toAdd_74_, v_fst_75_, v_snd_78_);
v___x_83_ = lean_apply_2(v_toAdd_74_, v_fst_77_, v_snd_76_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v___x_83_);
lean_ctor_set(v___x_80_, 0, v___x_82_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub(lean_object* v_00_u03b1_88_, lean_object* v_inst_89_, lean_object* v_q_u2081_90_, lean_object* v_q_u2082_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Grind_Ring_OfSemiring_sub___redArg(v_inst_89_, v_q_u2081_90_, v_q_u2082_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add___redArg(lean_object* v_inst_93_, lean_object* v_q_u2081_94_, lean_object* v_q_u2082_95_){
_start:
{
lean_object* v_toAdd_96_; lean_object* v_fst_97_; lean_object* v_snd_98_; lean_object* v_fst_99_; lean_object* v_snd_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_109_; 
v_toAdd_96_ = lean_ctor_get(v_inst_93_, 0);
lean_inc(v_toAdd_96_);
lean_dec_ref(v_inst_93_);
v_fst_97_ = lean_ctor_get(v_q_u2081_94_, 0);
lean_inc(v_fst_97_);
v_snd_98_ = lean_ctor_get(v_q_u2081_94_, 1);
lean_inc(v_snd_98_);
lean_dec(v_q_u2081_94_);
v_fst_99_ = lean_ctor_get(v_q_u2082_95_, 0);
v_snd_100_ = lean_ctor_get(v_q_u2082_95_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v_q_u2082_95_);
if (v_isSharedCheck_109_ == 0)
{
v___x_102_ = v_q_u2082_95_;
v_isShared_103_ = v_isSharedCheck_109_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_snd_100_);
lean_inc(v_fst_99_);
lean_dec(v_q_u2082_95_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_109_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
lean_inc(v_toAdd_96_);
v___x_104_ = lean_apply_2(v_toAdd_96_, v_fst_97_, v_fst_99_);
v___x_105_ = lean_apply_2(v_toAdd_96_, v_snd_98_, v_snd_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_105_);
lean_ctor_set(v___x_102_, 0, v___x_104_);
v___x_107_ = v___x_102_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add(lean_object* v_00_u03b1_110_, lean_object* v_inst_111_, lean_object* v_q_u2081_112_, lean_object* v_q_u2082_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Grind_Ring_OfSemiring_add___redArg(v_inst_111_, v_q_u2081_112_, v_q_u2082_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul___redArg(lean_object* v_inst_115_, lean_object* v_q_u2081_116_, lean_object* v_q_u2082_117_){
_start:
{
lean_object* v_toAdd_118_; lean_object* v_toMul_119_; lean_object* v_fst_120_; lean_object* v_snd_121_; lean_object* v_fst_122_; lean_object* v_snd_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_136_; 
v_toAdd_118_ = lean_ctor_get(v_inst_115_, 0);
lean_inc(v_toAdd_118_);
v_toMul_119_ = lean_ctor_get(v_inst_115_, 1);
lean_inc(v_toMul_119_);
lean_dec_ref(v_inst_115_);
v_fst_120_ = lean_ctor_get(v_q_u2081_116_, 0);
lean_inc(v_fst_120_);
v_snd_121_ = lean_ctor_get(v_q_u2081_116_, 1);
lean_inc(v_snd_121_);
lean_dec(v_q_u2081_116_);
v_fst_122_ = lean_ctor_get(v_q_u2082_117_, 0);
v_snd_123_ = lean_ctor_get(v_q_u2082_117_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_q_u2082_117_);
if (v_isSharedCheck_136_ == 0)
{
v___x_125_ = v_q_u2082_117_;
v_isShared_126_ = v_isSharedCheck_136_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_snd_123_);
lean_inc(v_fst_122_);
lean_dec(v_q_u2082_117_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_136_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
lean_inc_n(v_toMul_119_, 3);
lean_inc(v_fst_122_);
lean_inc(v_fst_120_);
v___x_127_ = lean_apply_2(v_toMul_119_, v_fst_120_, v_fst_122_);
lean_inc(v_snd_123_);
lean_inc(v_snd_121_);
v___x_128_ = lean_apply_2(v_toMul_119_, v_snd_121_, v_snd_123_);
lean_inc(v_toAdd_118_);
v___x_129_ = lean_apply_2(v_toAdd_118_, v___x_127_, v___x_128_);
v___x_130_ = lean_apply_2(v_toMul_119_, v_fst_120_, v_snd_123_);
v___x_131_ = lean_apply_2(v_toMul_119_, v_snd_121_, v_fst_122_);
v___x_132_ = lean_apply_2(v_toAdd_118_, v___x_130_, v___x_131_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_132_);
lean_ctor_set(v___x_125_, 0, v___x_129_);
v___x_134_ = v___x_125_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul(lean_object* v_00_u03b1_137_, lean_object* v_inst_138_, lean_object* v_q_u2081_139_, lean_object* v_q_u2082_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_138_, v_q_u2081_139_, v_q_u2082_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___redArg(lean_object* v_q_142_){
_start:
{
lean_object* v_fst_143_; lean_object* v_snd_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_fst_143_ = lean_ctor_get(v_q_142_, 0);
v_snd_144_ = lean_ctor_get(v_q_142_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_q_142_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v_q_142_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_snd_144_);
lean_inc(v_fst_143_);
lean_dec(v_q_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v_fst_143_);
lean_ctor_set(v___x_146_, 0, v_snd_144_);
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_snd_144_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_fst_143_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg(lean_object* v_00_u03b1_152_, lean_object* v_inst_153_, lean_object* v_q_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Grind_Ring_OfSemiring_neg___redArg(v_q_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___boxed(lean_object* v_00_u03b1_156_, lean_object* v_inst_157_, lean_object* v_q_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Grind_Ring_OfSemiring_neg(v_00_u03b1_156_, v_inst_157_, v_q_158_);
lean_dec_ref(v_inst_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg(lean_object* v_inst_160_, lean_object* v_a_161_, lean_object* v_n_162_){
_start:
{
lean_object* v_zero_163_; uint8_t v_isZero_164_; 
v_zero_163_ = lean_unsigned_to_nat(0u);
v_isZero_164_ = lean_nat_dec_eq(v_n_162_, v_zero_163_);
if (v_isZero_164_ == 1)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v_a_161_);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_160_, v___x_165_);
return v___x_166_;
}
else
{
lean_object* v_one_167_; lean_object* v_n_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_one_167_ = lean_unsigned_to_nat(1u);
v_n_168_ = lean_nat_sub(v_n_162_, v_one_167_);
lean_inc(v_a_161_);
lean_inc_ref(v_inst_160_);
v___x_169_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_160_, v_a_161_, v_n_168_);
lean_dec(v_n_168_);
v___x_170_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_160_, v___x_169_, v_a_161_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg___boxed(lean_object* v_inst_171_, lean_object* v_a_172_, lean_object* v_n_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_171_, v_a_172_, v_n_173_);
lean_dec(v_n_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow(lean_object* v_00_u03b1_175_, lean_object* v_inst_176_, lean_object* v_a_177_, lean_object* v_n_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_176_, v_a_177_, v_n_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___boxed(lean_object* v_00_u03b1_180_, lean_object* v_inst_181_, lean_object* v_a_182_, lean_object* v_n_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Grind_Ring_OfSemiring_npow(v_00_u03b1_180_, v_inst_181_, v_a_182_, v_n_183_);
lean_dec(v_n_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(lean_object* v_inst_185_, lean_object* v_n_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_inc_ref(v_inst_185_);
v___x_188_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_185_, v_n_186_);
v___x_189_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_185_, v___x_188_, v_a_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul(lean_object* v_00_u03b1_190_, lean_object* v_inst_191_, lean_object* v_n_192_, lean_object* v_a_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(v_inst_191_, v_n_192_, v_a_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(lean_object* v_inst_195_, lean_object* v_i_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_inc_ref(v_inst_195_);
v___x_198_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_195_, v_i_196_);
v___x_199_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_195_, v___x_198_, v_a_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg___boxed(lean_object* v_inst_200_, lean_object* v_i_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_200_, v_i_201_, v_a_202_);
lean_dec(v_i_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul(lean_object* v_00_u03b1_204_, lean_object* v_inst_205_, lean_object* v_i_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_205_, v_i_206_, v_a_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___boxed(lean_object* v_00_u03b1_209_, lean_object* v_inst_210_, lean_object* v_i_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Grind_Ring_OfSemiring_zsmul(v_00_u03b1_209_, v_inst_210_, v_i_211_, v_a_212_);
lean_dec(v_i_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0(lean_object* v_inst_214_, lean_object* v_n_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_214_, v_n_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(lean_object* v_inst_217_){
_start:
{
lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
lean_inc_ref_n(v_inst_217_, 9);
v___f_218_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0), 2, 1);
lean_closure_set(v___f_218_, 0, v_inst_217_);
v___x_219_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_add), 4, 2);
lean_closure_set(v___x_219_, 0, lean_box(0));
lean_closure_set(v___x_219_, 1, v_inst_217_);
v___x_220_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_mul), 4, 2);
lean_closure_set(v___x_220_, 0, lean_box(0));
lean_closure_set(v___x_220_, 1, v_inst_217_);
v___x_221_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_natCast), 3, 2);
lean_closure_set(v___x_221_, 0, lean_box(0));
lean_closure_set(v___x_221_, 1, v_inst_217_);
v___x_222_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_nsmul), 4, 2);
lean_closure_set(v___x_222_, 0, lean_box(0));
lean_closure_set(v___x_222_, 1, v_inst_217_);
v___x_223_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_npow___boxed), 4, 2);
lean_closure_set(v___x_223_, 0, lean_box(0));
lean_closure_set(v___x_223_, 1, v_inst_217_);
v___x_224_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_224_, 0, v___x_219_);
lean_ctor_set(v___x_224_, 1, v___x_220_);
lean_ctor_set(v___x_224_, 2, v___x_221_);
lean_ctor_set(v___x_224_, 3, v___f_218_);
lean_ctor_set(v___x_224_, 4, v___x_222_);
lean_ctor_set(v___x_224_, 5, v___x_223_);
v___x_225_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_225_, 0, lean_box(0));
lean_closure_set(v___x_225_, 1, v_inst_217_);
v___x_226_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_226_, 0, lean_box(0));
lean_closure_set(v___x_226_, 1, v_inst_217_);
v___x_227_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_227_, 0, lean_box(0));
lean_closure_set(v___x_227_, 1, v_inst_217_);
v___x_228_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_zsmul___boxed), 4, 2);
lean_closure_set(v___x_228_, 0, lean_box(0));
lean_closure_set(v___x_228_, 1, v_inst_217_);
v___x_229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_229_, 0, v___x_224_);
lean_ctor_set(v___x_229_, 1, v___x_225_);
lean_ctor_set(v___x_229_, 2, v___x_226_);
lean_ctor_set(v___x_229_, 3, v___x_227_);
lean_ctor_set(v___x_229_, 4, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring(lean_object* v_00_u03b1_230_, lean_object* v_inst_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ___redArg(lean_object* v_inst_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_ofNat_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_ofNat_235_ = lean_ctor_get(v_inst_233_, 3);
lean_inc(v_ofNat_235_);
lean_dec_ref(v_inst_233_);
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_apply_1(v_ofNat_235_, v___x_236_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v_a_234_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ(lean_object* v_00_u03b1_239_, lean_object* v_inst_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Grind_Ring_OfSemiring_toQ___redArg(v_inst_240_, v_a_241_);
return v___x_242_;
}
}
lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___redArg(){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_box(0);
return v___x_244_;
}
}
LEAN_EXPORT void l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_245_;
v_res_245_ = l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___redArg();
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___redArg___boxed(lean_object* v___dummy_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___redArg();
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(lean_object* v_00_u03b1_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_inst_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_box(0);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___boxed(lean_object* v_00_u03b1_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(v_00_u03b1_254_, v_inst_255_, v_inst_256_, v_inst_257_, v_inst_258_);
lean_dec_ref(v_inst_255_);
return v_res_259_;
}
}
lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___redArg(){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lean_box(0);
return v___x_261_;
}
}
LEAN_EXPORT void l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_262_;
v_res_262_ = l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___redArg();
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___redArg___boxed(lean_object* v___dummy_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___redArg();
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(lean_object* v_00_u03b1_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_inst_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_box(0);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___boxed(lean_object* v_00_u03b1_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_inst_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(v_00_u03b1_271_, v_inst_272_, v_inst_273_, v_inst_274_, v_inst_275_);
lean_dec_ref(v_inst_272_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring___redArg(lean_object* v_inst_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring(lean_object* v_00_u03b1_279_, lean_object* v_inst_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(lean_object* v_inst_282_){
_start:
{
lean_object* v_toSemiring_283_; lean_object* v_toAdd_284_; 
v_toSemiring_283_ = lean_ctor_get(v_inst_282_, 0);
v_toAdd_284_ = lean_ctor_get(v_toSemiring_283_, 0);
lean_inc(v_toAdd_284_);
return v_toAdd_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg___boxed(lean_object* v_inst_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_285_);
lean_dec_ref(v_inst_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(lean_object* v_00_u03b1_287_, lean_object* v_inst_288_, lean_object* v_inst_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___boxed(lean_object* v_00_u03b1_291_, lean_object* v_inst_292_, lean_object* v_inst_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(v_00_u03b1_291_, v_inst_292_, v_inst_293_);
lean_dec_ref(v_inst_293_);
lean_dec_ref(v_inst_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___redArg(lean_object* v_inst_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_296_, 0, lean_box(0));
lean_closure_set(v___x_296_, 1, v_inst_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_, lean_object* v_inst_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_300_, 0, lean_box(0));
lean_closure_set(v___x_300_, 1, v_inst_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___boxed(lean_object* v_00_u03b1_301_, lean_object* v_inst_302_, lean_object* v_inst_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(v_00_u03b1_301_, v_inst_302_, v_inst_303_);
lean_dec_ref(v_inst_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(lean_object* v_inst_305_){
_start:
{
lean_object* v_toSemiring_306_; lean_object* v_toMul_307_; 
v_toSemiring_306_ = lean_ctor_get(v_inst_305_, 0);
v_toMul_307_ = lean_ctor_get(v_toSemiring_306_, 1);
lean_inc(v_toMul_307_);
return v_toMul_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg___boxed(lean_object* v_inst_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_308_);
lean_dec_ref(v_inst_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(lean_object* v_00_u03b1_310_, lean_object* v_inst_311_, lean_object* v_inst_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___boxed(lean_object* v_00_u03b1_314_, lean_object* v_inst_315_, lean_object* v_inst_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(v_00_u03b1_314_, v_inst_315_, v_inst_316_);
lean_dec_ref(v_inst_316_);
lean_dec_ref(v_inst_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___redArg(lean_object* v_inst_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_319_, 0, lean_box(0));
lean_closure_set(v___x_319_, 1, v_inst_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(lean_object* v_00_u03b1_320_, lean_object* v_inst_321_, lean_object* v_inst_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_323_, 0, lean_box(0));
lean_closure_set(v___x_323_, 1, v_inst_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___boxed(lean_object* v_00_u03b1_324_, lean_object* v_inst_325_, lean_object* v_inst_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(v_00_u03b1_324_, v_inst_325_, v_inst_326_);
lean_dec_ref(v_inst_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(lean_object* v_n_328_, lean_object* v_inst_329_){
_start:
{
lean_object* v_toSemiring_330_; lean_object* v_ofNat_331_; lean_object* v___x_332_; 
v_toSemiring_330_ = lean_ctor_get(v_inst_329_, 0);
lean_inc_ref(v_toSemiring_330_);
lean_dec_ref(v_inst_329_);
v_ofNat_331_ = lean_ctor_get(v_toSemiring_330_, 3);
lean_inc(v_ofNat_331_);
lean_dec_ref(v_toSemiring_330_);
v___x_332_ = lean_apply_1(v_ofNat_331_, v_n_328_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(lean_object* v_00_u03b1_333_, lean_object* v_inst_334_, lean_object* v_n_335_, lean_object* v_inst_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(v_n_335_, v_inst_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___boxed(lean_object* v_00_u03b1_338_, lean_object* v_inst_339_, lean_object* v_n_340_, lean_object* v_inst_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(v_00_u03b1_338_, v_inst_339_, v_n_340_, v_inst_341_);
lean_dec_ref(v_inst_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(lean_object* v_inst_343_){
_start:
{
lean_object* v_toSemiring_344_; lean_object* v_natCast_345_; 
v_toSemiring_344_ = lean_ctor_get(v_inst_343_, 0);
v_natCast_345_ = lean_ctor_get(v_toSemiring_344_, 2);
lean_inc(v_natCast_345_);
return v_natCast_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg___boxed(lean_object* v_inst_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_346_);
lean_dec_ref(v_inst_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(lean_object* v_00_u03b1_348_, lean_object* v_inst_349_, lean_object* v_inst_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___boxed(lean_object* v_00_u03b1_352_, lean_object* v_inst_353_, lean_object* v_inst_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(v_00_u03b1_352_, v_inst_353_, v_inst_354_);
lean_dec_ref(v_inst_354_);
lean_dec_ref(v_inst_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___redArg(lean_object* v_inst_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_357_, 0, lean_box(0));
lean_closure_set(v___x_357_, 1, v_inst_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(lean_object* v_00_u03b1_358_, lean_object* v_inst_359_, lean_object* v_inst_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_361_, 0, lean_box(0));
lean_closure_set(v___x_361_, 1, v_inst_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___boxed(lean_object* v_00_u03b1_362_, lean_object* v_inst_363_, lean_object* v_inst_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(v_00_u03b1_362_, v_inst_363_, v_inst_364_);
lean_dec_ref(v_inst_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(lean_object* v_inst_366_){
_start:
{
lean_object* v_toSemiring_367_; lean_object* v_npow_368_; 
v_toSemiring_367_ = lean_ctor_get(v_inst_366_, 0);
v_npow_368_ = lean_ctor_get(v_toSemiring_367_, 5);
lean_inc(v_npow_368_);
return v_npow_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg___boxed(lean_object* v_inst_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_369_);
lean_dec_ref(v_inst_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(lean_object* v_00_u03b1_371_, lean_object* v_inst_372_, lean_object* v_inst_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___boxed(lean_object* v_00_u03b1_375_, lean_object* v_inst_376_, lean_object* v_inst_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(v_00_u03b1_375_, v_inst_376_, v_inst_377_);
lean_dec_ref(v_inst_377_);
lean_dec_ref(v_inst_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(lean_object* v_stx_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4));
lean_inc(v_stx_392_);
v___x_396_ = l_Lean_Syntax_isOfKind(v_stx_392_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v_stx_392_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_a_394_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = l_Lean_Syntax_getArg(v_stx_392_, v___x_399_);
lean_dec(v_stx_392_);
lean_inc(v___x_400_);
v___x_401_ = l_Lean_Syntax_matchesNull(v___x_400_, v___x_399_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec(v___x_400_);
v___x_402_ = lean_box(0);
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v_a_394_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = l_Lean_Syntax_getArg(v___x_400_, v___x_404_);
lean_dec(v___x_400_);
v___x_406_ = 0;
v___x_407_ = l_Lean_SourceInfo_fromRef(v_a_393_, v___x_406_);
v___x_408_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6));
v___x_409_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7));
lean_inc(v___x_407_);
v___x_410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_407_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = l_Lean_Syntax_node2(v___x_407_, v___x_408_, v___x_410_, v___x_405_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_a_394_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___boxed(lean_object* v_stx_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(v_stx_413_, v_a_414_, v_a_415_);
lean_dec(v_a_414_);
return v_res_416_;
}
}
lean_object* runtime_initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ring_Envelope(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Ring_Envelope(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* initialize_Init_Data_AC(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ring_Envelope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ordered_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Ring_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Ring_Envelope(builtin);
}
#ifdef __cplusplus
}
#endif
