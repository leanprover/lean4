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
lean_object* v_fst_14_; lean_object* v_snd_15_; lean_object* v_fst_16_; lean_object* v_snd_17_; lean_object* v___x_18_; 
v_fst_14_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_fst_14_);
v_snd_15_ = lean_ctor_get(v_x_11_, 1);
lean_inc(v_snd_15_);
lean_dec_ref(v_x_11_);
v_fst_16_ = lean_ctor_get(v_x_12_, 0);
lean_inc(v_fst_16_);
v_snd_17_ = lean_ctor_get(v_x_12_, 1);
lean_inc(v_snd_17_);
lean_dec_ref(v_x_12_);
v___x_18_ = lean_apply_4(v_h__1_13_, v_fst_14_, v_snd_15_, v_fst_16_, v_snd_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(lean_object* v_p_19_){
_start:
{
lean_inc_ref(v_p_19_);
return v_p_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg___boxed(lean_object* v_p_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(v_p_20_);
lean_dec_ref(v_p_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_, lean_object* v_p_24_){
_start:
{
lean_inc_ref(v_p_24_);
return v_p_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___boxed(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_p_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Grind_Ring_OfSemiring_Q_mk(v_00_u03b1_25_, v_inst_26_, v_p_27_);
lean_dec_ref(v_p_27_);
lean_dec_ref(v_inst_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___redArg(lean_object* v_q_u2081_29_, lean_object* v_q_u2082_30_, lean_object* v_f_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_apply_2(v_f_31_, v_q_u2081_29_, v_q_u2082_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(lean_object* v_00_u03b1_33_, lean_object* v_inst_34_, lean_object* v_00_u03b2_35_, lean_object* v_q_u2081_36_, lean_object* v_q_u2082_37_, lean_object* v_f_38_, lean_object* v_h_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_apply_2(v_f_38_, v_q_u2081_36_, v_q_u2082_37_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___boxed(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_00_u03b2_43_, lean_object* v_q_u2081_44_, lean_object* v_q_u2082_45_, lean_object* v_f_46_, lean_object* v_h_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(v_00_u03b1_41_, v_inst_42_, v_00_u03b2_43_, v_q_u2081_44_, v_q_u2082_45_, v_f_46_, v_h_47_);
lean_dec_ref(v_inst_42_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast___redArg(lean_object* v_inst_49_, lean_object* v_n_50_){
_start:
{
lean_object* v_natCast_51_; lean_object* v_ofNat_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_natCast_51_ = lean_ctor_get(v_inst_49_, 2);
lean_inc(v_natCast_51_);
v_ofNat_52_ = lean_ctor_get(v_inst_49_, 3);
lean_inc(v_ofNat_52_);
lean_dec_ref(v_inst_49_);
v___x_53_ = lean_apply_1(v_natCast_51_, v_n_50_);
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_apply_1(v_ofNat_52_, v___x_54_);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_53_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_n_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_58_, v_n_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg(lean_object* v_inst_63_, lean_object* v_n_64_){
_start:
{
lean_object* v_natCast_65_; lean_object* v_ofNat_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v_natCast_65_ = lean_ctor_get(v_inst_63_, 2);
lean_inc(v_natCast_65_);
v_ofNat_66_ = lean_ctor_get(v_inst_63_, 3);
lean_inc(v_ofNat_66_);
lean_dec_ref(v_inst_63_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_obj_once(&l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0, &l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0_once, _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0);
v___x_69_ = lean_int_dec_lt(v_n_64_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_nat_abs(v_n_64_);
v___x_71_ = lean_apply_1(v_natCast_65_, v___x_70_);
v___x_72_ = lean_apply_1(v_ofNat_66_, v___x_67_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_74_ = lean_apply_1(v_ofNat_66_, v___x_67_);
v___x_75_ = lean_nat_abs(v_n_64_);
v___x_76_ = lean_apply_1(v_natCast_65_, v___x_75_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_74_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg___boxed(lean_object* v_inst_78_, lean_object* v_n_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_78_, v_n_79_);
lean_dec(v_n_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast(lean_object* v_00_u03b1_81_, lean_object* v_inst_82_, lean_object* v_n_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_82_, v_n_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___boxed(lean_object* v_00_u03b1_85_, lean_object* v_inst_86_, lean_object* v_n_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Grind_Ring_OfSemiring_intCast(v_00_u03b1_85_, v_inst_86_, v_n_87_);
lean_dec(v_n_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub___redArg(lean_object* v_inst_89_, lean_object* v_q_u2081_90_, lean_object* v_q_u2082_91_){
_start:
{
lean_object* v_toAdd_92_; lean_object* v_fst_93_; lean_object* v_snd_94_; lean_object* v_fst_95_; lean_object* v_snd_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_105_; 
v_toAdd_92_ = lean_ctor_get(v_inst_89_, 0);
lean_inc(v_toAdd_92_);
lean_dec_ref(v_inst_89_);
v_fst_93_ = lean_ctor_get(v_q_u2081_90_, 0);
lean_inc(v_fst_93_);
v_snd_94_ = lean_ctor_get(v_q_u2081_90_, 1);
lean_inc(v_snd_94_);
lean_dec(v_q_u2081_90_);
v_fst_95_ = lean_ctor_get(v_q_u2082_91_, 0);
v_snd_96_ = lean_ctor_get(v_q_u2082_91_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_q_u2082_91_);
if (v_isSharedCheck_105_ == 0)
{
v___x_98_ = v_q_u2082_91_;
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_snd_96_);
lean_inc(v_fst_95_);
lean_dec(v_q_u2082_91_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
lean_inc(v_toAdd_92_);
v___x_100_ = lean_apply_2(v_toAdd_92_, v_fst_93_, v_snd_96_);
v___x_101_ = lean_apply_2(v_toAdd_92_, v_fst_95_, v_snd_94_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_101_);
lean_ctor_set(v___x_98_, 0, v___x_100_);
v___x_103_ = v___x_98_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub(lean_object* v_00_u03b1_106_, lean_object* v_inst_107_, lean_object* v_q_u2081_108_, lean_object* v_q_u2082_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Grind_Ring_OfSemiring_sub___redArg(v_inst_107_, v_q_u2081_108_, v_q_u2082_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add___redArg(lean_object* v_inst_111_, lean_object* v_q_u2081_112_, lean_object* v_q_u2082_113_){
_start:
{
lean_object* v_toAdd_114_; lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v_fst_117_; lean_object* v_snd_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_127_; 
v_toAdd_114_ = lean_ctor_get(v_inst_111_, 0);
lean_inc(v_toAdd_114_);
lean_dec_ref(v_inst_111_);
v_fst_115_ = lean_ctor_get(v_q_u2081_112_, 0);
lean_inc(v_fst_115_);
v_snd_116_ = lean_ctor_get(v_q_u2081_112_, 1);
lean_inc(v_snd_116_);
lean_dec(v_q_u2081_112_);
v_fst_117_ = lean_ctor_get(v_q_u2082_113_, 0);
v_snd_118_ = lean_ctor_get(v_q_u2082_113_, 1);
v_isSharedCheck_127_ = !lean_is_exclusive(v_q_u2082_113_);
if (v_isSharedCheck_127_ == 0)
{
v___x_120_ = v_q_u2082_113_;
v_isShared_121_ = v_isSharedCheck_127_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_snd_118_);
lean_inc(v_fst_117_);
lean_dec(v_q_u2082_113_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_127_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
lean_inc(v_toAdd_114_);
v___x_122_ = lean_apply_2(v_toAdd_114_, v_fst_115_, v_fst_117_);
v___x_123_ = lean_apply_2(v_toAdd_114_, v_snd_116_, v_snd_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_123_);
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_125_ = v___x_120_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add(lean_object* v_00_u03b1_128_, lean_object* v_inst_129_, lean_object* v_q_u2081_130_, lean_object* v_q_u2082_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Grind_Ring_OfSemiring_add___redArg(v_inst_129_, v_q_u2081_130_, v_q_u2082_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul___redArg(lean_object* v_inst_133_, lean_object* v_q_u2081_134_, lean_object* v_q_u2082_135_){
_start:
{
lean_object* v_toAdd_136_; lean_object* v_toMul_137_; lean_object* v_fst_138_; lean_object* v_snd_139_; lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_154_; 
v_toAdd_136_ = lean_ctor_get(v_inst_133_, 0);
lean_inc(v_toAdd_136_);
v_toMul_137_ = lean_ctor_get(v_inst_133_, 1);
lean_inc(v_toMul_137_);
lean_dec_ref(v_inst_133_);
v_fst_138_ = lean_ctor_get(v_q_u2081_134_, 0);
lean_inc(v_fst_138_);
v_snd_139_ = lean_ctor_get(v_q_u2081_134_, 1);
lean_inc(v_snd_139_);
lean_dec(v_q_u2081_134_);
v_fst_140_ = lean_ctor_get(v_q_u2082_135_, 0);
v_snd_141_ = lean_ctor_get(v_q_u2082_135_, 1);
v_isSharedCheck_154_ = !lean_is_exclusive(v_q_u2082_135_);
if (v_isSharedCheck_154_ == 0)
{
v___x_143_ = v_q_u2082_135_;
v_isShared_144_ = v_isSharedCheck_154_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_snd_141_);
lean_inc(v_fst_140_);
lean_dec(v_q_u2082_135_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_154_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
lean_inc_n(v_toMul_137_, 3);
lean_inc(v_fst_140_);
lean_inc(v_fst_138_);
v___x_145_ = lean_apply_2(v_toMul_137_, v_fst_138_, v_fst_140_);
lean_inc(v_snd_141_);
lean_inc(v_snd_139_);
v___x_146_ = lean_apply_2(v_toMul_137_, v_snd_139_, v_snd_141_);
lean_inc(v_toAdd_136_);
v___x_147_ = lean_apply_2(v_toAdd_136_, v___x_145_, v___x_146_);
v___x_148_ = lean_apply_2(v_toMul_137_, v_fst_138_, v_snd_141_);
v___x_149_ = lean_apply_2(v_toMul_137_, v_snd_139_, v_fst_140_);
v___x_150_ = lean_apply_2(v_toAdd_136_, v___x_148_, v___x_149_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v___x_150_);
lean_ctor_set(v___x_143_, 0, v___x_147_);
v___x_152_ = v___x_143_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul(lean_object* v_00_u03b1_155_, lean_object* v_inst_156_, lean_object* v_q_u2081_157_, lean_object* v_q_u2082_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_156_, v_q_u2081_157_, v_q_u2082_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___redArg(lean_object* v_q_160_){
_start:
{
lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_fst_161_ = lean_ctor_get(v_q_160_, 0);
v_snd_162_ = lean_ctor_get(v_q_160_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_q_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v_q_160_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_snd_162_);
lean_inc(v_fst_161_);
lean_dec(v_q_160_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v_fst_161_);
lean_ctor_set(v___x_164_, 0, v_snd_162_);
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_snd_162_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_fst_161_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg(lean_object* v_00_u03b1_170_, lean_object* v_inst_171_, lean_object* v_q_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Grind_Ring_OfSemiring_neg___redArg(v_q_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___boxed(lean_object* v_00_u03b1_174_, lean_object* v_inst_175_, lean_object* v_q_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Grind_Ring_OfSemiring_neg(v_00_u03b1_174_, v_inst_175_, v_q_176_);
lean_dec_ref(v_inst_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg(lean_object* v_inst_178_, lean_object* v_a_179_, lean_object* v_n_180_){
_start:
{
lean_object* v_zero_181_; uint8_t v_isZero_182_; 
v_zero_181_ = lean_unsigned_to_nat(0u);
v_isZero_182_ = lean_nat_dec_eq(v_n_180_, v_zero_181_);
if (v_isZero_182_ == 1)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_a_179_);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_178_, v___x_183_);
return v___x_184_;
}
else
{
lean_object* v_one_185_; lean_object* v_n_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_one_185_ = lean_unsigned_to_nat(1u);
v_n_186_ = lean_nat_sub(v_n_180_, v_one_185_);
lean_inc(v_a_179_);
lean_inc_ref(v_inst_178_);
v___x_187_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_178_, v_a_179_, v_n_186_);
lean_dec(v_n_186_);
v___x_188_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_178_, v___x_187_, v_a_179_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg___boxed(lean_object* v_inst_189_, lean_object* v_a_190_, lean_object* v_n_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_189_, v_a_190_, v_n_191_);
lean_dec(v_n_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow(lean_object* v_00_u03b1_193_, lean_object* v_inst_194_, lean_object* v_a_195_, lean_object* v_n_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_194_, v_a_195_, v_n_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___boxed(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_, lean_object* v_a_200_, lean_object* v_n_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Grind_Ring_OfSemiring_npow(v_00_u03b1_198_, v_inst_199_, v_a_200_, v_n_201_);
lean_dec(v_n_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(lean_object* v_inst_203_, lean_object* v_n_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_inc_ref(v_inst_203_);
v___x_206_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_203_, v_n_204_);
v___x_207_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_203_, v___x_206_, v_a_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul(lean_object* v_00_u03b1_208_, lean_object* v_inst_209_, lean_object* v_n_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(v_inst_209_, v_n_210_, v_a_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(lean_object* v_inst_213_, lean_object* v_i_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_inc_ref(v_inst_213_);
v___x_216_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_213_, v_i_214_);
v___x_217_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_213_, v___x_216_, v_a_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg___boxed(lean_object* v_inst_218_, lean_object* v_i_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_218_, v_i_219_, v_a_220_);
lean_dec(v_i_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul(lean_object* v_00_u03b1_222_, lean_object* v_inst_223_, lean_object* v_i_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_223_, v_i_224_, v_a_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___boxed(lean_object* v_00_u03b1_227_, lean_object* v_inst_228_, lean_object* v_i_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Grind_Ring_OfSemiring_zsmul(v_00_u03b1_227_, v_inst_228_, v_i_229_, v_a_230_);
lean_dec(v_i_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0(lean_object* v_inst_232_, lean_object* v_n_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_232_, v_n_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(lean_object* v_inst_235_){
_start:
{
lean_object* v___f_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_inc_ref_n(v_inst_235_, 9);
v___f_236_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0), 2, 1);
lean_closure_set(v___f_236_, 0, v_inst_235_);
v___x_237_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_add), 4, 2);
lean_closure_set(v___x_237_, 0, lean_box(0));
lean_closure_set(v___x_237_, 1, v_inst_235_);
v___x_238_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_mul), 4, 2);
lean_closure_set(v___x_238_, 0, lean_box(0));
lean_closure_set(v___x_238_, 1, v_inst_235_);
v___x_239_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_natCast), 3, 2);
lean_closure_set(v___x_239_, 0, lean_box(0));
lean_closure_set(v___x_239_, 1, v_inst_235_);
v___x_240_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_nsmul), 4, 2);
lean_closure_set(v___x_240_, 0, lean_box(0));
lean_closure_set(v___x_240_, 1, v_inst_235_);
v___x_241_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_npow___boxed), 4, 2);
lean_closure_set(v___x_241_, 0, lean_box(0));
lean_closure_set(v___x_241_, 1, v_inst_235_);
v___x_242_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_242_, 0, v___x_237_);
lean_ctor_set(v___x_242_, 1, v___x_238_);
lean_ctor_set(v___x_242_, 2, v___x_239_);
lean_ctor_set(v___x_242_, 3, v___f_236_);
lean_ctor_set(v___x_242_, 4, v___x_240_);
lean_ctor_set(v___x_242_, 5, v___x_241_);
v___x_243_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_243_, 0, lean_box(0));
lean_closure_set(v___x_243_, 1, v_inst_235_);
v___x_244_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_244_, 0, lean_box(0));
lean_closure_set(v___x_244_, 1, v_inst_235_);
v___x_245_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_245_, 0, lean_box(0));
lean_closure_set(v___x_245_, 1, v_inst_235_);
v___x_246_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_zsmul___boxed), 4, 2);
lean_closure_set(v___x_246_, 0, lean_box(0));
lean_closure_set(v___x_246_, 1, v_inst_235_);
v___x_247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_247_, 0, v___x_242_);
lean_ctor_set(v___x_247_, 1, v___x_243_);
lean_ctor_set(v___x_247_, 2, v___x_244_);
lean_ctor_set(v___x_247_, 3, v___x_245_);
lean_ctor_set(v___x_247_, 4, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring(lean_object* v_00_u03b1_248_, lean_object* v_inst_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ___redArg(lean_object* v_inst_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_ofNat_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_ofNat_253_ = lean_ctor_get(v_inst_251_, 3);
lean_inc(v_ofNat_253_);
lean_dec_ref(v_inst_251_);
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_apply_1(v_ofNat_253_, v___x_254_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_a_252_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ(lean_object* v_00_u03b1_257_, lean_object* v_inst_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Grind_Ring_OfSemiring_toQ___redArg(v_inst_258_, v_a_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(lean_object* v_00_u03b1_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_inst_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___boxed(lean_object* v_00_u03b1_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_inst_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(v_00_u03b1_267_, v_inst_268_, v_inst_269_, v_inst_270_, v_inst_271_);
lean_dec_ref(v_inst_268_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(lean_object* v_00_u03b1_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_inst_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_box(0);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___boxed(lean_object* v_00_u03b1_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_inst_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(v_00_u03b1_279_, v_inst_280_, v_inst_281_, v_inst_282_, v_inst_283_);
lean_dec_ref(v_inst_280_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring___redArg(lean_object* v_inst_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring(lean_object* v_00_u03b1_287_, lean_object* v_inst_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(lean_object* v_inst_290_){
_start:
{
lean_object* v_toSemiring_291_; lean_object* v_toAdd_292_; 
v_toSemiring_291_ = lean_ctor_get(v_inst_290_, 0);
v_toAdd_292_ = lean_ctor_get(v_toSemiring_291_, 0);
lean_inc(v_toAdd_292_);
return v_toAdd_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg___boxed(lean_object* v_inst_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_293_);
lean_dec_ref(v_inst_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(lean_object* v_00_u03b1_295_, lean_object* v_inst_296_, lean_object* v_inst_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___boxed(lean_object* v_00_u03b1_299_, lean_object* v_inst_300_, lean_object* v_inst_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(v_00_u03b1_299_, v_inst_300_, v_inst_301_);
lean_dec_ref(v_inst_301_);
lean_dec_ref(v_inst_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___redArg(lean_object* v_inst_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_304_, 0, lean_box(0));
lean_closure_set(v___x_304_, 1, v_inst_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(lean_object* v_00_u03b1_305_, lean_object* v_inst_306_, lean_object* v_inst_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_308_, 0, lean_box(0));
lean_closure_set(v___x_308_, 1, v_inst_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___boxed(lean_object* v_00_u03b1_309_, lean_object* v_inst_310_, lean_object* v_inst_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(v_00_u03b1_309_, v_inst_310_, v_inst_311_);
lean_dec_ref(v_inst_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(lean_object* v_inst_313_){
_start:
{
lean_object* v_toSemiring_314_; lean_object* v_toMul_315_; 
v_toSemiring_314_ = lean_ctor_get(v_inst_313_, 0);
v_toMul_315_ = lean_ctor_get(v_toSemiring_314_, 1);
lean_inc(v_toMul_315_);
return v_toMul_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg___boxed(lean_object* v_inst_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_316_);
lean_dec_ref(v_inst_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(lean_object* v_00_u03b1_318_, lean_object* v_inst_319_, lean_object* v_inst_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___boxed(lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_inst_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(v_00_u03b1_322_, v_inst_323_, v_inst_324_);
lean_dec_ref(v_inst_324_);
lean_dec_ref(v_inst_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___redArg(lean_object* v_inst_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_327_, 0, lean_box(0));
lean_closure_set(v___x_327_, 1, v_inst_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(lean_object* v_00_u03b1_328_, lean_object* v_inst_329_, lean_object* v_inst_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_331_, 0, lean_box(0));
lean_closure_set(v___x_331_, 1, v_inst_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___boxed(lean_object* v_00_u03b1_332_, lean_object* v_inst_333_, lean_object* v_inst_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(v_00_u03b1_332_, v_inst_333_, v_inst_334_);
lean_dec_ref(v_inst_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(lean_object* v_n_336_, lean_object* v_inst_337_){
_start:
{
lean_object* v_toSemiring_338_; lean_object* v_ofNat_339_; lean_object* v___x_340_; 
v_toSemiring_338_ = lean_ctor_get(v_inst_337_, 0);
lean_inc_ref(v_toSemiring_338_);
lean_dec_ref(v_inst_337_);
v_ofNat_339_ = lean_ctor_get(v_toSemiring_338_, 3);
lean_inc(v_ofNat_339_);
lean_dec_ref(v_toSemiring_338_);
v___x_340_ = lean_apply_1(v_ofNat_339_, v_n_336_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(lean_object* v_00_u03b1_341_, lean_object* v_inst_342_, lean_object* v_n_343_, lean_object* v_inst_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(v_n_343_, v_inst_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___boxed(lean_object* v_00_u03b1_346_, lean_object* v_inst_347_, lean_object* v_n_348_, lean_object* v_inst_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(v_00_u03b1_346_, v_inst_347_, v_n_348_, v_inst_349_);
lean_dec_ref(v_inst_347_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(lean_object* v_inst_351_){
_start:
{
lean_object* v_toSemiring_352_; lean_object* v_natCast_353_; 
v_toSemiring_352_ = lean_ctor_get(v_inst_351_, 0);
v_natCast_353_ = lean_ctor_get(v_toSemiring_352_, 2);
lean_inc(v_natCast_353_);
return v_natCast_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg___boxed(lean_object* v_inst_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_354_);
lean_dec_ref(v_inst_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(lean_object* v_00_u03b1_356_, lean_object* v_inst_357_, lean_object* v_inst_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___boxed(lean_object* v_00_u03b1_360_, lean_object* v_inst_361_, lean_object* v_inst_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(v_00_u03b1_360_, v_inst_361_, v_inst_362_);
lean_dec_ref(v_inst_362_);
lean_dec_ref(v_inst_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___redArg(lean_object* v_inst_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_365_, 0, lean_box(0));
lean_closure_set(v___x_365_, 1, v_inst_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(lean_object* v_00_u03b1_366_, lean_object* v_inst_367_, lean_object* v_inst_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_369_, 0, lean_box(0));
lean_closure_set(v___x_369_, 1, v_inst_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___boxed(lean_object* v_00_u03b1_370_, lean_object* v_inst_371_, lean_object* v_inst_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(v_00_u03b1_370_, v_inst_371_, v_inst_372_);
lean_dec_ref(v_inst_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(lean_object* v_inst_374_){
_start:
{
lean_object* v_toSemiring_375_; lean_object* v_npow_376_; 
v_toSemiring_375_ = lean_ctor_get(v_inst_374_, 0);
v_npow_376_ = lean_ctor_get(v_toSemiring_375_, 5);
lean_inc(v_npow_376_);
return v_npow_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg___boxed(lean_object* v_inst_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_377_);
lean_dec_ref(v_inst_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(lean_object* v_00_u03b1_379_, lean_object* v_inst_380_, lean_object* v_inst_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___boxed(lean_object* v_00_u03b1_383_, lean_object* v_inst_384_, lean_object* v_inst_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(v_00_u03b1_383_, v_inst_384_, v_inst_385_);
lean_dec_ref(v_inst_385_);
lean_dec_ref(v_inst_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(lean_object* v_stx_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4));
lean_inc(v_stx_400_);
v___x_404_ = l_Lean_Syntax_isOfKind(v_stx_400_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v_stx_400_);
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_a_402_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = l_Lean_Syntax_getArg(v_stx_400_, v___x_407_);
lean_dec(v_stx_400_);
lean_inc(v___x_408_);
v___x_409_ = l_Lean_Syntax_matchesNull(v___x_408_, v___x_407_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v___x_408_);
v___x_410_ = lean_box(0);
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_a_402_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = l_Lean_Syntax_getArg(v___x_408_, v___x_412_);
lean_dec(v___x_408_);
v___x_414_ = 0;
v___x_415_ = l_Lean_SourceInfo_fromRef(v_a_401_, v___x_414_);
v___x_416_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6));
v___x_417_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7));
lean_inc(v___x_415_);
v___x_418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_415_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = l_Lean_Syntax_node2(v___x_415_, v___x_416_, v___x_418_, v___x_413_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v_a_402_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___boxed(lean_object* v_stx_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(v_stx_421_, v_a_422_, v_a_423_);
lean_dec(v_a_422_);
return v_res_424_;
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
