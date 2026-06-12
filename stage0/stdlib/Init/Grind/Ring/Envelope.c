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
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_obj_once(&l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0, &l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0_once, _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0);
v___x_67_ = lean_int_dec_lt(v_n_64_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v_natCast_68_; lean_object* v_ofNat_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_natCast_68_ = lean_ctor_get(v_inst_63_, 2);
lean_inc(v_natCast_68_);
v_ofNat_69_ = lean_ctor_get(v_inst_63_, 3);
lean_inc(v_ofNat_69_);
lean_dec_ref(v_inst_63_);
v___x_70_ = lean_nat_abs(v_n_64_);
v___x_71_ = lean_apply_1(v_natCast_68_, v___x_70_);
v___x_72_ = lean_apply_1(v_ofNat_69_, v___x_65_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_natCast_74_; lean_object* v_ofNat_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_natCast_74_ = lean_ctor_get(v_inst_63_, 2);
lean_inc(v_natCast_74_);
v_ofNat_75_ = lean_ctor_get(v_inst_63_, 3);
lean_inc(v_ofNat_75_);
lean_dec_ref(v_inst_63_);
v___x_76_ = lean_apply_1(v_ofNat_75_, v___x_65_);
v___x_77_ = lean_nat_abs(v_n_64_);
v___x_78_ = lean_apply_1(v_natCast_74_, v___x_77_);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_76_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg___boxed(lean_object* v_inst_80_, lean_object* v_n_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_80_, v_n_81_);
lean_dec(v_n_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast(lean_object* v_00_u03b1_83_, lean_object* v_inst_84_, lean_object* v_n_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_84_, v_n_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___boxed(lean_object* v_00_u03b1_87_, lean_object* v_inst_88_, lean_object* v_n_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Grind_Ring_OfSemiring_intCast(v_00_u03b1_87_, v_inst_88_, v_n_89_);
lean_dec(v_n_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub___redArg(lean_object* v_inst_91_, lean_object* v_q_u2081_92_, lean_object* v_q_u2082_93_){
_start:
{
lean_object* v_toAdd_94_; lean_object* v_fst_95_; lean_object* v_snd_96_; lean_object* v_fst_97_; lean_object* v_snd_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_107_; 
v_toAdd_94_ = lean_ctor_get(v_inst_91_, 0);
lean_inc(v_toAdd_94_);
lean_dec_ref(v_inst_91_);
v_fst_95_ = lean_ctor_get(v_q_u2081_92_, 0);
lean_inc(v_fst_95_);
v_snd_96_ = lean_ctor_get(v_q_u2081_92_, 1);
lean_inc(v_snd_96_);
lean_dec(v_q_u2081_92_);
v_fst_97_ = lean_ctor_get(v_q_u2082_93_, 0);
v_snd_98_ = lean_ctor_get(v_q_u2082_93_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_q_u2082_93_);
if (v_isSharedCheck_107_ == 0)
{
v___x_100_ = v_q_u2082_93_;
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_snd_98_);
lean_inc(v_fst_97_);
lean_dec(v_q_u2082_93_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
lean_inc(v_toAdd_94_);
v___x_102_ = lean_apply_2(v_toAdd_94_, v_fst_95_, v_snd_98_);
v___x_103_ = lean_apply_2(v_toAdd_94_, v_fst_97_, v_snd_96_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 1, v___x_103_);
lean_ctor_set(v___x_100_, 0, v___x_102_);
v___x_105_ = v___x_100_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub(lean_object* v_00_u03b1_108_, lean_object* v_inst_109_, lean_object* v_q_u2081_110_, lean_object* v_q_u2082_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Grind_Ring_OfSemiring_sub___redArg(v_inst_109_, v_q_u2081_110_, v_q_u2082_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add___redArg(lean_object* v_inst_113_, lean_object* v_q_u2081_114_, lean_object* v_q_u2082_115_){
_start:
{
lean_object* v_toAdd_116_; lean_object* v_fst_117_; lean_object* v_snd_118_; lean_object* v_fst_119_; lean_object* v_snd_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_129_; 
v_toAdd_116_ = lean_ctor_get(v_inst_113_, 0);
lean_inc(v_toAdd_116_);
lean_dec_ref(v_inst_113_);
v_fst_117_ = lean_ctor_get(v_q_u2081_114_, 0);
lean_inc(v_fst_117_);
v_snd_118_ = lean_ctor_get(v_q_u2081_114_, 1);
lean_inc(v_snd_118_);
lean_dec(v_q_u2081_114_);
v_fst_119_ = lean_ctor_get(v_q_u2082_115_, 0);
v_snd_120_ = lean_ctor_get(v_q_u2082_115_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_q_u2082_115_);
if (v_isSharedCheck_129_ == 0)
{
v___x_122_ = v_q_u2082_115_;
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_snd_120_);
lean_inc(v_fst_119_);
lean_dec(v_q_u2082_115_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_toAdd_116_);
v___x_124_ = lean_apply_2(v_toAdd_116_, v_fst_117_, v_fst_119_);
v___x_125_ = lean_apply_2(v_toAdd_116_, v_snd_118_, v_snd_120_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_125_);
lean_ctor_set(v___x_122_, 0, v___x_124_);
v___x_127_ = v___x_122_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add(lean_object* v_00_u03b1_130_, lean_object* v_inst_131_, lean_object* v_q_u2081_132_, lean_object* v_q_u2082_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Grind_Ring_OfSemiring_add___redArg(v_inst_131_, v_q_u2081_132_, v_q_u2082_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul___redArg(lean_object* v_inst_135_, lean_object* v_q_u2081_136_, lean_object* v_q_u2082_137_){
_start:
{
lean_object* v_toAdd_138_; lean_object* v_toMul_139_; lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v_fst_142_; lean_object* v_snd_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_156_; 
v_toAdd_138_ = lean_ctor_get(v_inst_135_, 0);
lean_inc(v_toAdd_138_);
v_toMul_139_ = lean_ctor_get(v_inst_135_, 1);
lean_inc(v_toMul_139_);
lean_dec_ref(v_inst_135_);
v_fst_140_ = lean_ctor_get(v_q_u2081_136_, 0);
lean_inc(v_fst_140_);
v_snd_141_ = lean_ctor_get(v_q_u2081_136_, 1);
lean_inc(v_snd_141_);
lean_dec(v_q_u2081_136_);
v_fst_142_ = lean_ctor_get(v_q_u2082_137_, 0);
v_snd_143_ = lean_ctor_get(v_q_u2082_137_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_q_u2082_137_);
if (v_isSharedCheck_156_ == 0)
{
v___x_145_ = v_q_u2082_137_;
v_isShared_146_ = v_isSharedCheck_156_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_snd_143_);
lean_inc(v_fst_142_);
lean_dec(v_q_u2082_137_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_156_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
lean_inc_n(v_toMul_139_, 3);
lean_inc(v_fst_142_);
lean_inc(v_fst_140_);
v___x_147_ = lean_apply_2(v_toMul_139_, v_fst_140_, v_fst_142_);
lean_inc(v_snd_143_);
lean_inc(v_snd_141_);
v___x_148_ = lean_apply_2(v_toMul_139_, v_snd_141_, v_snd_143_);
lean_inc(v_toAdd_138_);
v___x_149_ = lean_apply_2(v_toAdd_138_, v___x_147_, v___x_148_);
v___x_150_ = lean_apply_2(v_toMul_139_, v_fst_140_, v_snd_143_);
v___x_151_ = lean_apply_2(v_toMul_139_, v_snd_141_, v_fst_142_);
v___x_152_ = lean_apply_2(v_toAdd_138_, v___x_150_, v___x_151_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_152_);
lean_ctor_set(v___x_145_, 0, v___x_149_);
v___x_154_ = v___x_145_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul(lean_object* v_00_u03b1_157_, lean_object* v_inst_158_, lean_object* v_q_u2081_159_, lean_object* v_q_u2082_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_158_, v_q_u2081_159_, v_q_u2082_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___redArg(lean_object* v_q_162_){
_start:
{
lean_object* v_fst_163_; lean_object* v_snd_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v_fst_163_ = lean_ctor_get(v_q_162_, 0);
v_snd_164_ = lean_ctor_get(v_q_162_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_q_162_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v_q_162_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_snd_164_);
lean_inc(v_fst_163_);
lean_dec(v_q_162_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_fst_163_);
lean_ctor_set(v___x_166_, 0, v_snd_164_);
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_snd_164_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_fst_163_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg(lean_object* v_00_u03b1_172_, lean_object* v_inst_173_, lean_object* v_q_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Grind_Ring_OfSemiring_neg___redArg(v_q_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___boxed(lean_object* v_00_u03b1_176_, lean_object* v_inst_177_, lean_object* v_q_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Grind_Ring_OfSemiring_neg(v_00_u03b1_176_, v_inst_177_, v_q_178_);
lean_dec_ref(v_inst_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg(lean_object* v_inst_180_, lean_object* v_a_181_, lean_object* v_n_182_){
_start:
{
lean_object* v_zero_183_; uint8_t v_isZero_184_; 
v_zero_183_ = lean_unsigned_to_nat(0u);
v_isZero_184_ = lean_nat_dec_eq(v_n_182_, v_zero_183_);
if (v_isZero_184_ == 1)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_a_181_);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_180_, v___x_185_);
return v___x_186_;
}
else
{
lean_object* v_one_187_; lean_object* v_n_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_one_187_ = lean_unsigned_to_nat(1u);
v_n_188_ = lean_nat_sub(v_n_182_, v_one_187_);
lean_inc(v_a_181_);
lean_inc_ref(v_inst_180_);
v___x_189_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_180_, v_a_181_, v_n_188_);
lean_dec(v_n_188_);
v___x_190_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_180_, v___x_189_, v_a_181_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg___boxed(lean_object* v_inst_191_, lean_object* v_a_192_, lean_object* v_n_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_191_, v_a_192_, v_n_193_);
lean_dec(v_n_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow(lean_object* v_00_u03b1_195_, lean_object* v_inst_196_, lean_object* v_a_197_, lean_object* v_n_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_196_, v_a_197_, v_n_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___boxed(lean_object* v_00_u03b1_200_, lean_object* v_inst_201_, lean_object* v_a_202_, lean_object* v_n_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Grind_Ring_OfSemiring_npow(v_00_u03b1_200_, v_inst_201_, v_a_202_, v_n_203_);
lean_dec(v_n_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(lean_object* v_inst_205_, lean_object* v_n_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_inc_ref(v_inst_205_);
v___x_208_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_205_, v_n_206_);
v___x_209_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_205_, v___x_208_, v_a_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul(lean_object* v_00_u03b1_210_, lean_object* v_inst_211_, lean_object* v_n_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(v_inst_211_, v_n_212_, v_a_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(lean_object* v_inst_215_, lean_object* v_i_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_inc_ref(v_inst_215_);
v___x_218_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_215_, v_i_216_);
v___x_219_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_215_, v___x_218_, v_a_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg___boxed(lean_object* v_inst_220_, lean_object* v_i_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_220_, v_i_221_, v_a_222_);
lean_dec(v_i_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul(lean_object* v_00_u03b1_224_, lean_object* v_inst_225_, lean_object* v_i_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_225_, v_i_226_, v_a_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___boxed(lean_object* v_00_u03b1_229_, lean_object* v_inst_230_, lean_object* v_i_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Grind_Ring_OfSemiring_zsmul(v_00_u03b1_229_, v_inst_230_, v_i_231_, v_a_232_);
lean_dec(v_i_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0(lean_object* v_inst_234_, lean_object* v_n_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_234_, v_n_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(lean_object* v_inst_237_){
_start:
{
lean_object* v___f_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
lean_inc_ref_n(v_inst_237_, 9);
v___f_238_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0), 2, 1);
lean_closure_set(v___f_238_, 0, v_inst_237_);
v___x_239_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_add), 4, 2);
lean_closure_set(v___x_239_, 0, lean_box(0));
lean_closure_set(v___x_239_, 1, v_inst_237_);
v___x_240_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_mul), 4, 2);
lean_closure_set(v___x_240_, 0, lean_box(0));
lean_closure_set(v___x_240_, 1, v_inst_237_);
v___x_241_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_natCast), 3, 2);
lean_closure_set(v___x_241_, 0, lean_box(0));
lean_closure_set(v___x_241_, 1, v_inst_237_);
v___x_242_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_nsmul), 4, 2);
lean_closure_set(v___x_242_, 0, lean_box(0));
lean_closure_set(v___x_242_, 1, v_inst_237_);
v___x_243_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_npow___boxed), 4, 2);
lean_closure_set(v___x_243_, 0, lean_box(0));
lean_closure_set(v___x_243_, 1, v_inst_237_);
v___x_244_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_244_, 0, v___x_239_);
lean_ctor_set(v___x_244_, 1, v___x_240_);
lean_ctor_set(v___x_244_, 2, v___x_241_);
lean_ctor_set(v___x_244_, 3, v___f_238_);
lean_ctor_set(v___x_244_, 4, v___x_242_);
lean_ctor_set(v___x_244_, 5, v___x_243_);
v___x_245_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_245_, 0, lean_box(0));
lean_closure_set(v___x_245_, 1, v_inst_237_);
v___x_246_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_246_, 0, lean_box(0));
lean_closure_set(v___x_246_, 1, v_inst_237_);
v___x_247_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_247_, 0, lean_box(0));
lean_closure_set(v___x_247_, 1, v_inst_237_);
v___x_248_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_zsmul___boxed), 4, 2);
lean_closure_set(v___x_248_, 0, lean_box(0));
lean_closure_set(v___x_248_, 1, v_inst_237_);
v___x_249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_249_, 0, v___x_244_);
lean_ctor_set(v___x_249_, 1, v___x_245_);
lean_ctor_set(v___x_249_, 2, v___x_246_);
lean_ctor_set(v___x_249_, 3, v___x_247_);
lean_ctor_set(v___x_249_, 4, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring(lean_object* v_00_u03b1_250_, lean_object* v_inst_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ___redArg(lean_object* v_inst_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_ofNat_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_ofNat_255_ = lean_ctor_get(v_inst_253_, 3);
lean_inc(v_ofNat_255_);
lean_dec_ref(v_inst_253_);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_apply_1(v_ofNat_255_, v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_a_254_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ(lean_object* v_00_u03b1_259_, lean_object* v_inst_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Grind_Ring_OfSemiring_toQ___redArg(v_inst_260_, v_a_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_inst_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___boxed(lean_object* v_00_u03b1_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_inst_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(v_00_u03b1_269_, v_inst_270_, v_inst_271_, v_inst_272_, v_inst_273_);
lean_dec_ref(v_inst_270_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(lean_object* v_00_u03b1_275_, lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_inst_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___boxed(lean_object* v_00_u03b1_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_inst_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(v_00_u03b1_281_, v_inst_282_, v_inst_283_, v_inst_284_, v_inst_285_);
lean_dec_ref(v_inst_282_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring___redArg(lean_object* v_inst_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring(lean_object* v_00_u03b1_289_, lean_object* v_inst_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(lean_object* v_inst_292_){
_start:
{
lean_object* v_toSemiring_293_; lean_object* v_toAdd_294_; 
v_toSemiring_293_ = lean_ctor_get(v_inst_292_, 0);
v_toAdd_294_ = lean_ctor_get(v_toSemiring_293_, 0);
lean_inc(v_toAdd_294_);
return v_toAdd_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg___boxed(lean_object* v_inst_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_295_);
lean_dec_ref(v_inst_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_, lean_object* v_inst_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___boxed(lean_object* v_00_u03b1_301_, lean_object* v_inst_302_, lean_object* v_inst_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(v_00_u03b1_301_, v_inst_302_, v_inst_303_);
lean_dec_ref(v_inst_303_);
lean_dec_ref(v_inst_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___redArg(lean_object* v_inst_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_306_, 0, lean_box(0));
lean_closure_set(v___x_306_, 1, v_inst_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(lean_object* v_00_u03b1_307_, lean_object* v_inst_308_, lean_object* v_inst_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(v___x_310_, 0, lean_box(0));
lean_closure_set(v___x_310_, 1, v_inst_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___boxed(lean_object* v_00_u03b1_311_, lean_object* v_inst_312_, lean_object* v_inst_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(v_00_u03b1_311_, v_inst_312_, v_inst_313_);
lean_dec_ref(v_inst_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(lean_object* v_inst_315_){
_start:
{
lean_object* v_toSemiring_316_; lean_object* v_toMul_317_; 
v_toSemiring_316_ = lean_ctor_get(v_inst_315_, 0);
v_toMul_317_ = lean_ctor_get(v_toSemiring_316_, 1);
lean_inc(v_toMul_317_);
return v_toMul_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg___boxed(lean_object* v_inst_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_318_);
lean_dec_ref(v_inst_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(lean_object* v_00_u03b1_320_, lean_object* v_inst_321_, lean_object* v_inst_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___boxed(lean_object* v_00_u03b1_324_, lean_object* v_inst_325_, lean_object* v_inst_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(v_00_u03b1_324_, v_inst_325_, v_inst_326_);
lean_dec_ref(v_inst_326_);
lean_dec_ref(v_inst_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___redArg(lean_object* v_inst_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_329_, 0, lean_box(0));
lean_closure_set(v___x_329_, 1, v_inst_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(lean_object* v_00_u03b1_330_, lean_object* v_inst_331_, lean_object* v_inst_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(v___x_333_, 0, lean_box(0));
lean_closure_set(v___x_333_, 1, v_inst_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___boxed(lean_object* v_00_u03b1_334_, lean_object* v_inst_335_, lean_object* v_inst_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(v_00_u03b1_334_, v_inst_335_, v_inst_336_);
lean_dec_ref(v_inst_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(lean_object* v_n_338_, lean_object* v_inst_339_){
_start:
{
lean_object* v_toSemiring_340_; lean_object* v_ofNat_341_; lean_object* v___x_342_; 
v_toSemiring_340_ = lean_ctor_get(v_inst_339_, 0);
lean_inc_ref(v_toSemiring_340_);
lean_dec_ref(v_inst_339_);
v_ofNat_341_ = lean_ctor_get(v_toSemiring_340_, 3);
lean_inc(v_ofNat_341_);
lean_dec_ref(v_toSemiring_340_);
v___x_342_ = lean_apply_1(v_ofNat_341_, v_n_338_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(lean_object* v_00_u03b1_343_, lean_object* v_inst_344_, lean_object* v_n_345_, lean_object* v_inst_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(v_n_345_, v_inst_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___boxed(lean_object* v_00_u03b1_348_, lean_object* v_inst_349_, lean_object* v_n_350_, lean_object* v_inst_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(v_00_u03b1_348_, v_inst_349_, v_n_350_, v_inst_351_);
lean_dec_ref(v_inst_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(lean_object* v_inst_353_){
_start:
{
lean_object* v_toSemiring_354_; lean_object* v_natCast_355_; 
v_toSemiring_354_ = lean_ctor_get(v_inst_353_, 0);
v_natCast_355_ = lean_ctor_get(v_toSemiring_354_, 2);
lean_inc(v_natCast_355_);
return v_natCast_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg___boxed(lean_object* v_inst_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_356_);
lean_dec_ref(v_inst_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(lean_object* v_00_u03b1_358_, lean_object* v_inst_359_, lean_object* v_inst_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___boxed(lean_object* v_00_u03b1_362_, lean_object* v_inst_363_, lean_object* v_inst_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(v_00_u03b1_362_, v_inst_363_, v_inst_364_);
lean_dec_ref(v_inst_364_);
lean_dec_ref(v_inst_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___redArg(lean_object* v_inst_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_367_, 0, lean_box(0));
lean_closure_set(v___x_367_, 1, v_inst_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(lean_object* v_00_u03b1_368_, lean_object* v_inst_369_, lean_object* v_inst_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(v___x_371_, 0, lean_box(0));
lean_closure_set(v___x_371_, 1, v_inst_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___boxed(lean_object* v_00_u03b1_372_, lean_object* v_inst_373_, lean_object* v_inst_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(v_00_u03b1_372_, v_inst_373_, v_inst_374_);
lean_dec_ref(v_inst_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(lean_object* v_inst_376_){
_start:
{
lean_object* v_toSemiring_377_; lean_object* v_npow_378_; 
v_toSemiring_377_ = lean_ctor_get(v_inst_376_, 0);
v_npow_378_ = lean_ctor_get(v_toSemiring_377_, 5);
lean_inc(v_npow_378_);
return v_npow_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg___boxed(lean_object* v_inst_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_379_);
lean_dec_ref(v_inst_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(lean_object* v_00_u03b1_381_, lean_object* v_inst_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___boxed(lean_object* v_00_u03b1_385_, lean_object* v_inst_386_, lean_object* v_inst_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(v_00_u03b1_385_, v_inst_386_, v_inst_387_);
lean_dec_ref(v_inst_387_);
lean_dec_ref(v_inst_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(lean_object* v_stx_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4));
lean_inc(v_stx_402_);
v___x_406_ = l_Lean_Syntax_isOfKind(v_stx_402_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec(v_stx_402_);
v___x_407_ = lean_box(0);
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v_a_404_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = l_Lean_Syntax_getArg(v_stx_402_, v___x_409_);
lean_dec(v_stx_402_);
lean_inc(v___x_410_);
v___x_411_ = l_Lean_Syntax_matchesNull(v___x_410_, v___x_409_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec(v___x_410_);
v___x_412_ = lean_box(0);
v___x_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_a_404_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = l_Lean_Syntax_getArg(v___x_410_, v___x_414_);
lean_dec(v___x_410_);
v___x_416_ = 0;
v___x_417_ = l_Lean_SourceInfo_fromRef(v_a_403_, v___x_416_);
v___x_418_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6));
v___x_419_ = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7));
lean_inc(v___x_417_);
v___x_420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_417_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = l_Lean_Syntax_node2(v___x_417_, v___x_418_, v___x_420_, v___x_415_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v_a_404_);
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___boxed(lean_object* v_stx_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(v_stx_423_, v_a_424_, v_a_425_);
lean_dec(v_a_424_);
return v_res_426_;
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
