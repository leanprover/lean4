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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_){
_start:
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_8_; 
v_fst_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_fst_4_);
v_snd_5_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_x_1_);
v_fst_6_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_fst_6_);
v_snd_7_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_snd_7_);
lean_dec_ref(v_x_2_);
v___x_8_ = lean_apply_4(v_h__1_3_, v_fst_4_, v_snd_5_, v_fst_6_, v_snd_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter(lean_object* v_00_u03b1_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_x_12_, lean_object* v_h__1_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter___redArg(v_x_11_, v_x_12_, v_h__1_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(lean_object* v_p_15_){
_start:
{
lean_inc_ref(v_p_15_);
return v_p_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg___boxed(lean_object* v_p_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(v_p_16_);
lean_dec_ref(v_p_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk(lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_p_20_){
_start:
{
lean_inc_ref(v_p_20_);
return v_p_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___boxed(lean_object* v_00_u03b1_21_, lean_object* v_inst_22_, lean_object* v_p_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Grind_Ring_OfSemiring_Q_mk(v_00_u03b1_21_, v_inst_22_, v_p_23_);
lean_dec_ref(v_p_23_);
lean_dec_ref(v_inst_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___redArg(lean_object* v_q_u2081_25_, lean_object* v_q_u2082_26_, lean_object* v_f_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_apply_2(v_f_27_, v_q_u2081_25_, v_q_u2082_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(lean_object* v_00_u03b1_29_, lean_object* v_inst_30_, lean_object* v_00_u03b2_31_, lean_object* v_q_u2081_32_, lean_object* v_q_u2082_33_, lean_object* v_f_34_, lean_object* v_h_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_apply_2(v_f_34_, v_q_u2081_32_, v_q_u2082_33_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___boxed(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_00_u03b2_39_, lean_object* v_q_u2081_40_, lean_object* v_q_u2082_41_, lean_object* v_f_42_, lean_object* v_h_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(v_00_u03b1_37_, v_inst_38_, v_00_u03b2_39_, v_q_u2081_40_, v_q_u2082_41_, v_f_42_, v_h_43_);
lean_dec_ref(v_inst_38_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast___redArg(lean_object* v_inst_45_, lean_object* v_n_46_){
_start:
{
lean_object* v_natCast_47_; lean_object* v_ofNat_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_natCast_47_ = lean_ctor_get(v_inst_45_, 2);
lean_inc(v_natCast_47_);
v_ofNat_48_ = lean_ctor_get(v_inst_45_, 3);
lean_inc(v_ofNat_48_);
lean_dec_ref(v_inst_45_);
v___x_49_ = lean_apply_1(v_natCast_47_, v_n_46_);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_apply_1(v_ofNat_48_, v___x_50_);
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_49_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_, lean_object* v_n_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_54_, v_n_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_nat_to_int(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg(lean_object* v_inst_59_, lean_object* v_n_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_obj_once(&l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0, &l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0_once, _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0);
v___x_63_ = lean_int_dec_lt(v_n_60_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v_natCast_64_; lean_object* v_ofNat_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_natCast_64_ = lean_ctor_get(v_inst_59_, 2);
lean_inc(v_natCast_64_);
v_ofNat_65_ = lean_ctor_get(v_inst_59_, 3);
lean_inc(v_ofNat_65_);
lean_dec_ref(v_inst_59_);
v___x_66_ = lean_nat_abs(v_n_60_);
v___x_67_ = lean_apply_1(v_natCast_64_, v___x_66_);
v___x_68_ = lean_apply_1(v_ofNat_65_, v___x_61_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
return v___x_69_;
}
else
{
lean_object* v_natCast_70_; lean_object* v_ofNat_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_natCast_70_ = lean_ctor_get(v_inst_59_, 2);
lean_inc(v_natCast_70_);
v_ofNat_71_ = lean_ctor_get(v_inst_59_, 3);
lean_inc(v_ofNat_71_);
lean_dec_ref(v_inst_59_);
v___x_72_ = lean_apply_1(v_ofNat_71_, v___x_61_);
v___x_73_ = lean_nat_abs(v_n_60_);
v___x_74_ = lean_apply_1(v_natCast_70_, v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_72_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg___boxed(lean_object* v_inst_76_, lean_object* v_n_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_76_, v_n_77_);
lean_dec(v_n_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast(lean_object* v_00_u03b1_79_, lean_object* v_inst_80_, lean_object* v_n_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_80_, v_n_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___boxed(lean_object* v_00_u03b1_83_, lean_object* v_inst_84_, lean_object* v_n_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Grind_Ring_OfSemiring_intCast(v_00_u03b1_83_, v_inst_84_, v_n_85_);
lean_dec(v_n_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub___redArg(lean_object* v_inst_87_, lean_object* v_q_u2081_88_, lean_object* v_q_u2082_89_){
_start:
{
lean_object* v_toAdd_90_; lean_object* v_fst_91_; lean_object* v_snd_92_; lean_object* v_fst_93_; lean_object* v_snd_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_103_; 
v_toAdd_90_ = lean_ctor_get(v_inst_87_, 0);
lean_inc(v_toAdd_90_);
lean_dec_ref(v_inst_87_);
v_fst_91_ = lean_ctor_get(v_q_u2081_88_, 0);
lean_inc(v_fst_91_);
v_snd_92_ = lean_ctor_get(v_q_u2081_88_, 1);
lean_inc(v_snd_92_);
lean_dec(v_q_u2081_88_);
v_fst_93_ = lean_ctor_get(v_q_u2082_89_, 0);
v_snd_94_ = lean_ctor_get(v_q_u2082_89_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_q_u2082_89_);
if (v_isSharedCheck_103_ == 0)
{
v___x_96_ = v_q_u2082_89_;
v_isShared_97_ = v_isSharedCheck_103_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_snd_94_);
lean_inc(v_fst_93_);
lean_dec(v_q_u2082_89_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_103_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_101_; 
lean_inc(v_toAdd_90_);
v___x_98_ = lean_apply_2(v_toAdd_90_, v_fst_91_, v_snd_94_);
v___x_99_ = lean_apply_2(v_toAdd_90_, v_fst_93_, v_snd_92_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v___x_99_);
lean_ctor_set(v___x_96_, 0, v___x_98_);
v___x_101_ = v___x_96_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub(lean_object* v_00_u03b1_104_, lean_object* v_inst_105_, lean_object* v_q_u2081_106_, lean_object* v_q_u2082_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_Grind_Ring_OfSemiring_sub___redArg(v_inst_105_, v_q_u2081_106_, v_q_u2082_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add___redArg(lean_object* v_inst_109_, lean_object* v_q_u2081_110_, lean_object* v_q_u2082_111_){
_start:
{
lean_object* v_toAdd_112_; lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_125_; 
v_toAdd_112_ = lean_ctor_get(v_inst_109_, 0);
lean_inc(v_toAdd_112_);
lean_dec_ref(v_inst_109_);
v_fst_113_ = lean_ctor_get(v_q_u2081_110_, 0);
lean_inc(v_fst_113_);
v_snd_114_ = lean_ctor_get(v_q_u2081_110_, 1);
lean_inc(v_snd_114_);
lean_dec(v_q_u2081_110_);
v_fst_115_ = lean_ctor_get(v_q_u2082_111_, 0);
v_snd_116_ = lean_ctor_get(v_q_u2082_111_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_q_u2082_111_);
if (v_isSharedCheck_125_ == 0)
{
v___x_118_ = v_q_u2082_111_;
v_isShared_119_ = v_isSharedCheck_125_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_q_u2082_111_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_125_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
lean_inc(v_toAdd_112_);
v___x_120_ = lean_apply_2(v_toAdd_112_, v_fst_113_, v_fst_115_);
v___x_121_ = lean_apply_2(v_toAdd_112_, v_snd_114_, v_snd_116_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v___x_121_);
lean_ctor_set(v___x_118_, 0, v___x_120_);
v___x_123_ = v___x_118_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add(lean_object* v_00_u03b1_126_, lean_object* v_inst_127_, lean_object* v_q_u2081_128_, lean_object* v_q_u2082_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Grind_Ring_OfSemiring_add___redArg(v_inst_127_, v_q_u2081_128_, v_q_u2082_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul___redArg(lean_object* v_inst_131_, lean_object* v_q_u2081_132_, lean_object* v_q_u2082_133_){
_start:
{
lean_object* v_toAdd_134_; lean_object* v_toMul_135_; lean_object* v_fst_136_; lean_object* v_snd_137_; lean_object* v_fst_138_; lean_object* v_snd_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_152_; 
v_toAdd_134_ = lean_ctor_get(v_inst_131_, 0);
lean_inc(v_toAdd_134_);
v_toMul_135_ = lean_ctor_get(v_inst_131_, 1);
lean_inc(v_toMul_135_);
lean_dec_ref(v_inst_131_);
v_fst_136_ = lean_ctor_get(v_q_u2081_132_, 0);
lean_inc(v_fst_136_);
v_snd_137_ = lean_ctor_get(v_q_u2081_132_, 1);
lean_inc(v_snd_137_);
lean_dec(v_q_u2081_132_);
v_fst_138_ = lean_ctor_get(v_q_u2082_133_, 0);
v_snd_139_ = lean_ctor_get(v_q_u2082_133_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_q_u2082_133_);
if (v_isSharedCheck_152_ == 0)
{
v___x_141_ = v_q_u2082_133_;
v_isShared_142_ = v_isSharedCheck_152_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_snd_139_);
lean_inc(v_fst_138_);
lean_dec(v_q_u2082_133_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_152_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
lean_inc(v_toMul_135_);
lean_inc(v_fst_138_);
lean_inc(v_fst_136_);
v___x_143_ = lean_apply_2(v_toMul_135_, v_fst_136_, v_fst_138_);
lean_inc(v_toMul_135_);
lean_inc(v_snd_139_);
lean_inc(v_snd_137_);
v___x_144_ = lean_apply_2(v_toMul_135_, v_snd_137_, v_snd_139_);
lean_inc(v_toAdd_134_);
v___x_145_ = lean_apply_2(v_toAdd_134_, v___x_143_, v___x_144_);
lean_inc(v_toMul_135_);
v___x_146_ = lean_apply_2(v_toMul_135_, v_fst_136_, v_snd_139_);
v___x_147_ = lean_apply_2(v_toMul_135_, v_snd_137_, v_fst_138_);
v___x_148_ = lean_apply_2(v_toAdd_134_, v___x_146_, v___x_147_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v___x_148_);
lean_ctor_set(v___x_141_, 0, v___x_145_);
v___x_150_ = v___x_141_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul(lean_object* v_00_u03b1_153_, lean_object* v_inst_154_, lean_object* v_q_u2081_155_, lean_object* v_q_u2082_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_154_, v_q_u2081_155_, v_q_u2082_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___redArg(lean_object* v_q_158_){
_start:
{
lean_object* v_fst_159_; lean_object* v_snd_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_fst_159_ = lean_ctor_get(v_q_158_, 0);
v_snd_160_ = lean_ctor_get(v_q_158_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_q_158_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v_q_158_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_snd_160_);
lean_inc(v_fst_159_);
lean_dec(v_q_158_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 1, v_fst_159_);
lean_ctor_set(v___x_162_, 0, v_snd_160_);
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_snd_160_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_fst_159_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg(lean_object* v_00_u03b1_168_, lean_object* v_inst_169_, lean_object* v_q_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Grind_Ring_OfSemiring_neg___redArg(v_q_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___boxed(lean_object* v_00_u03b1_172_, lean_object* v_inst_173_, lean_object* v_q_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Grind_Ring_OfSemiring_neg(v_00_u03b1_172_, v_inst_173_, v_q_174_);
lean_dec_ref(v_inst_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg(lean_object* v_inst_176_, lean_object* v_a_177_, lean_object* v_n_178_){
_start:
{
lean_object* v_zero_179_; uint8_t v_isZero_180_; 
v_zero_179_ = lean_unsigned_to_nat(0u);
v_isZero_180_ = lean_nat_dec_eq(v_n_178_, v_zero_179_);
if (v_isZero_180_ == 1)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_a_177_);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_176_, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v_one_183_; lean_object* v_n_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_one_183_ = lean_unsigned_to_nat(1u);
v_n_184_ = lean_nat_sub(v_n_178_, v_one_183_);
lean_inc(v_a_177_);
lean_inc_ref(v_inst_176_);
v___x_185_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_176_, v_a_177_, v_n_184_);
lean_dec(v_n_184_);
v___x_186_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_176_, v___x_185_, v_a_177_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg___boxed(lean_object* v_inst_187_, lean_object* v_a_188_, lean_object* v_n_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_187_, v_a_188_, v_n_189_);
lean_dec(v_n_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow(lean_object* v_00_u03b1_191_, lean_object* v_inst_192_, lean_object* v_a_193_, lean_object* v_n_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_192_, v_a_193_, v_n_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___boxed(lean_object* v_00_u03b1_196_, lean_object* v_inst_197_, lean_object* v_a_198_, lean_object* v_n_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Grind_Ring_OfSemiring_npow(v_00_u03b1_196_, v_inst_197_, v_a_198_, v_n_199_);
lean_dec(v_n_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(lean_object* v_inst_201_, lean_object* v_n_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_inc_ref(v_inst_201_);
v___x_204_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_201_, v_n_202_);
v___x_205_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_201_, v___x_204_, v_a_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul(lean_object* v_00_u03b1_206_, lean_object* v_inst_207_, lean_object* v_n_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(v_inst_207_, v_n_208_, v_a_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(lean_object* v_inst_211_, lean_object* v_i_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_inc_ref(v_inst_211_);
v___x_214_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_211_, v_i_212_);
v___x_215_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_211_, v___x_214_, v_a_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg___boxed(lean_object* v_inst_216_, lean_object* v_i_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_216_, v_i_217_, v_a_218_);
lean_dec(v_i_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul(lean_object* v_00_u03b1_220_, lean_object* v_inst_221_, lean_object* v_i_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_221_, v_i_222_, v_a_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___boxed(lean_object* v_00_u03b1_225_, lean_object* v_inst_226_, lean_object* v_i_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Grind_Ring_OfSemiring_zsmul(v_00_u03b1_225_, v_inst_226_, v_i_227_, v_a_228_);
lean_dec(v_i_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0(lean_object* v_inst_230_, lean_object* v_n_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_230_, v_n_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(lean_object* v_inst_233_){
_start:
{
lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
lean_inc_ref(v_inst_233_);
v___f_234_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0), 2, 1);
lean_closure_set(v___f_234_, 0, v_inst_233_);
lean_inc_ref(v_inst_233_);
v___x_235_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_add), 4, 2);
lean_closure_set(v___x_235_, 0, lean_box(0));
lean_closure_set(v___x_235_, 1, v_inst_233_);
lean_inc_ref(v_inst_233_);
v___x_236_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_mul), 4, 2);
lean_closure_set(v___x_236_, 0, lean_box(0));
lean_closure_set(v___x_236_, 1, v_inst_233_);
lean_inc_ref(v_inst_233_);
v___x_237_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_natCast), 3, 2);
lean_closure_set(v___x_237_, 0, lean_box(0));
lean_closure_set(v___x_237_, 1, v_inst_233_);
lean_inc_ref(v_inst_233_);
v___x_238_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_nsmul), 4, 2);
lean_closure_set(v___x_238_, 0, lean_box(0));
lean_closure_set(v___x_238_, 1, v_inst_233_);
lean_inc_ref(v_inst_233_);
v___x_239_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_npow___boxed), 4, 2);
lean_closure_set(v___x_239_, 0, lean_box(0));
lean_closure_set(v___x_239_, 1, v_inst_233_);
v___x_240_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_240_, 0, v___x_235_);
lean_ctor_set(v___x_240_, 1, v___x_236_);
lean_ctor_set(v___x_240_, 2, v___x_237_);
lean_ctor_set(v___x_240_, 3, v___f_234_);
lean_ctor_set(v___x_240_, 4, v___x_238_);
lean_ctor_set(v___x_240_, 5, v___x_239_);
lean_inc_ref(v_inst_233_);
v___x_241_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_241_, 0, lean_box(0));
lean_closure_set(v___x_241_, 1, v_inst_233_);
lean_inc_ref(v_inst_233_);
v___x_242_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_242_, 0, lean_box(0));
lean_closure_set(v___x_242_, 1, v_inst_233_);
lean_inc_ref(v_inst_233_);
v___x_243_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_243_, 0, lean_box(0));
lean_closure_set(v___x_243_, 1, v_inst_233_);
v___x_244_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_zsmul___boxed), 4, 2);
lean_closure_set(v___x_244_, 0, lean_box(0));
lean_closure_set(v___x_244_, 1, v_inst_233_);
v___x_245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_245_, 0, v___x_240_);
lean_ctor_set(v___x_245_, 1, v___x_241_);
lean_ctor_set(v___x_245_, 2, v___x_242_);
lean_ctor_set(v___x_245_, 3, v___x_243_);
lean_ctor_set(v___x_245_, 4, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring(lean_object* v_00_u03b1_246_, lean_object* v_inst_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ___redArg(lean_object* v_inst_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_ofNat_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_ofNat_251_ = lean_ctor_get(v_inst_249_, 3);
lean_inc(v_ofNat_251_);
lean_dec_ref(v_inst_249_);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_apply_1(v_ofNat_251_, v___x_252_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v_a_250_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ(lean_object* v_00_u03b1_255_, lean_object* v_inst_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Grind_Ring_OfSemiring_toQ___redArg(v_inst_256_, v_a_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(lean_object* v_00_u03b1_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_inst_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_box(0);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___boxed(lean_object* v_00_u03b1_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_inst_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(v_00_u03b1_265_, v_inst_266_, v_inst_267_, v_inst_268_, v_inst_269_);
lean_dec_ref(v_inst_266_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(lean_object* v_00_u03b1_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_inst_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_box(0);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___boxed(lean_object* v_00_u03b1_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_inst_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(v_00_u03b1_277_, v_inst_278_, v_inst_279_, v_inst_280_, v_inst_281_);
lean_dec_ref(v_inst_278_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring___redArg(lean_object* v_inst_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring(lean_object* v_00_u03b1_285_, lean_object* v_inst_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(lean_object* v_inst_288_){
_start:
{
lean_object* v_toSemiring_289_; lean_object* v_toAdd_290_; 
v_toSemiring_289_ = lean_ctor_get(v_inst_288_, 0);
v_toAdd_290_ = lean_ctor_get(v_toSemiring_289_, 0);
lean_inc(v_toAdd_290_);
return v_toAdd_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg___boxed(lean_object* v_inst_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_291_);
lean_dec_ref(v_inst_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(lean_object* v_00_u03b1_293_, lean_object* v_inst_294_, lean_object* v_inst_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___boxed(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_, lean_object* v_inst_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(v_00_u03b1_297_, v_inst_298_, v_inst_299_);
lean_dec_ref(v_inst_299_);
lean_dec_ref(v_inst_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___redArg(lean_object* v_inst_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_302_, 0, lean_box(0));
lean_closure_set(v___x_302_, 1, v_inst_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(lean_object* v_00_u03b1_303_, lean_object* v_inst_304_, lean_object* v_inst_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_306_, 0, lean_box(0));
lean_closure_set(v___x_306_, 1, v_inst_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___boxed(lean_object* v_00_u03b1_307_, lean_object* v_inst_308_, lean_object* v_inst_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(v_00_u03b1_307_, v_inst_308_, v_inst_309_);
lean_dec_ref(v_inst_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(lean_object* v_inst_311_){
_start:
{
lean_object* v_toSemiring_312_; lean_object* v_toMul_313_; 
v_toSemiring_312_ = lean_ctor_get(v_inst_311_, 0);
v_toMul_313_ = lean_ctor_get(v_toSemiring_312_, 1);
lean_inc(v_toMul_313_);
return v_toMul_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg___boxed(lean_object* v_inst_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_314_);
lean_dec_ref(v_inst_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(lean_object* v_00_u03b1_316_, lean_object* v_inst_317_, lean_object* v_inst_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___boxed(lean_object* v_00_u03b1_320_, lean_object* v_inst_321_, lean_object* v_inst_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(v_00_u03b1_320_, v_inst_321_, v_inst_322_);
lean_dec_ref(v_inst_322_);
lean_dec_ref(v_inst_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___redArg(lean_object* v_inst_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_325_, 0, lean_box(0));
lean_closure_set(v___x_325_, 1, v_inst_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(lean_object* v_00_u03b1_326_, lean_object* v_inst_327_, lean_object* v_inst_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_329_, 0, lean_box(0));
lean_closure_set(v___x_329_, 1, v_inst_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___boxed(lean_object* v_00_u03b1_330_, lean_object* v_inst_331_, lean_object* v_inst_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(v_00_u03b1_330_, v_inst_331_, v_inst_332_);
lean_dec_ref(v_inst_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(lean_object* v_n_334_, lean_object* v_inst_335_){
_start:
{
lean_object* v_toSemiring_336_; lean_object* v_ofNat_337_; lean_object* v___x_338_; 
v_toSemiring_336_ = lean_ctor_get(v_inst_335_, 0);
lean_inc_ref(v_toSemiring_336_);
lean_dec_ref(v_inst_335_);
v_ofNat_337_ = lean_ctor_get(v_toSemiring_336_, 3);
lean_inc(v_ofNat_337_);
lean_dec_ref(v_toSemiring_336_);
v___x_338_ = lean_apply_1(v_ofNat_337_, v_n_334_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(lean_object* v_00_u03b1_339_, lean_object* v_inst_340_, lean_object* v_n_341_, lean_object* v_inst_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(v_n_341_, v_inst_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___boxed(lean_object* v_00_u03b1_344_, lean_object* v_inst_345_, lean_object* v_n_346_, lean_object* v_inst_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(v_00_u03b1_344_, v_inst_345_, v_n_346_, v_inst_347_);
lean_dec_ref(v_inst_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(lean_object* v_inst_349_){
_start:
{
lean_object* v_toSemiring_350_; lean_object* v_natCast_351_; 
v_toSemiring_350_ = lean_ctor_get(v_inst_349_, 0);
v_natCast_351_ = lean_ctor_get(v_toSemiring_350_, 2);
lean_inc(v_natCast_351_);
return v_natCast_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg___boxed(lean_object* v_inst_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_352_);
lean_dec_ref(v_inst_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(lean_object* v_00_u03b1_354_, lean_object* v_inst_355_, lean_object* v_inst_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___boxed(lean_object* v_00_u03b1_358_, lean_object* v_inst_359_, lean_object* v_inst_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(v_00_u03b1_358_, v_inst_359_, v_inst_360_);
lean_dec_ref(v_inst_360_);
lean_dec_ref(v_inst_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___redArg(lean_object* v_inst_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_363_, 0, lean_box(0));
lean_closure_set(v___x_363_, 1, v_inst_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(lean_object* v_00_u03b1_364_, lean_object* v_inst_365_, lean_object* v_inst_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_367_, 0, lean_box(0));
lean_closure_set(v___x_367_, 1, v_inst_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___boxed(lean_object* v_00_u03b1_368_, lean_object* v_inst_369_, lean_object* v_inst_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(v_00_u03b1_368_, v_inst_369_, v_inst_370_);
lean_dec_ref(v_inst_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(lean_object* v_inst_372_){
_start:
{
lean_object* v_toSemiring_373_; lean_object* v_npow_374_; 
v_toSemiring_373_ = lean_ctor_get(v_inst_372_, 0);
v_npow_374_ = lean_ctor_get(v_toSemiring_373_, 5);
lean_inc(v_npow_374_);
return v_npow_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg___boxed(lean_object* v_inst_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_375_);
lean_dec_ref(v_inst_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(lean_object* v_00_u03b1_377_, lean_object* v_inst_378_, lean_object* v_inst_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___boxed(lean_object* v_00_u03b1_381_, lean_object* v_inst_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(v_00_u03b1_381_, v_inst_382_, v_inst_383_);
lean_dec_ref(v_inst_383_);
lean_dec_ref(v_inst_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(lean_object* v_stx_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4));
lean_inc(v_stx_398_);
v___x_402_ = l_Lean_Syntax_isOfKind(v_stx_398_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_stx_398_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_a_400_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = l_Lean_Syntax_getArg(v_stx_398_, v___x_405_);
lean_dec(v_stx_398_);
lean_inc(v___x_406_);
v___x_407_ = l_Lean_Syntax_matchesNull(v___x_406_, v___x_405_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v___x_406_);
v___x_408_ = lean_box(0);
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_a_400_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = l_Lean_Syntax_getArg(v___x_406_, v___x_410_);
lean_dec(v___x_406_);
v___x_412_ = 0;
v___x_413_ = l_Lean_SourceInfo_fromRef(v_a_399_, v___x_412_);
v___x_414_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6));
v___x_415_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7));
lean_inc(v___x_413_);
v___x_416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_413_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = l_Lean_Syntax_node2(v___x_413_, v___x_414_, v___x_416_, v___x_411_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v_a_400_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___boxed(lean_object* v_stx_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(v_stx_419_, v_a_420_, v_a_421_);
lean_dec(v_a_420_);
return v_res_422_;
}
}
lean_object* runtime_initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ring_Envelope(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
