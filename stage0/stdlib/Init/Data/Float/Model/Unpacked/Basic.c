// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Basic
// Imports: public import Init.Data.Float.Model.Unpacked.Sign public import Init.Data.Int.Repr
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
uint8_t l_Float_Model_UnpackedFloat_instBEqSign_beq(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr(uint8_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_infinity_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_infinity_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_notANumber_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_notANumber_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_zero_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_zero_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_finite_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_finite_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Float_Model_instReprUnpackedFloat_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__0 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__0_value;
static const lean_ctor_object l_Float_Model_instReprUnpackedFloat_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__0_value)}};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__1 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__1_value;
static const lean_string_object l_Float_Model_instReprUnpackedFloat_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Float.Model.UnpackedFloat.notANumber"};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__2 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__2_value;
static const lean_ctor_object l_Float_Model_instReprUnpackedFloat_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__2_value)}};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__3 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__3_value;
static const lean_string_object l_Float_Model_instReprUnpackedFloat_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Float.Model.UnpackedFloat.infinity"};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__4 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__4_value;
static const lean_ctor_object l_Float_Model_instReprUnpackedFloat_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__4_value)}};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__5 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__5_value;
static const lean_ctor_object l_Float_Model_instReprUnpackedFloat_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__6 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__6_value;
static lean_once_cell_t l_Float_Model_instReprUnpackedFloat_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__7;
static lean_once_cell_t l_Float_Model_instReprUnpackedFloat_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__8;
static const lean_string_object l_Float_Model_instReprUnpackedFloat_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Float.Model.UnpackedFloat.zero"};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__9 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__9_value;
static const lean_ctor_object l_Float_Model_instReprUnpackedFloat_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__9_value)}};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__10 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__10_value;
static const lean_ctor_object l_Float_Model_instReprUnpackedFloat_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__11 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__11_value;
static const lean_string_object l_Float_Model_instReprUnpackedFloat_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Float.Model.UnpackedFloat.finite"};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__12 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__12_value;
static const lean_ctor_object l_Float_Model_instReprUnpackedFloat_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__12_value)}};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__13 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__13_value;
static const lean_ctor_object l_Float_Model_instReprUnpackedFloat_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__14 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat_repr___closed__14_value;
static lean_once_cell_t l_Float_Model_instReprUnpackedFloat_repr___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_instReprUnpackedFloat_repr___closed__15;
LEAN_EXPORT lean_object* l_Float_Model_instReprUnpackedFloat_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_instReprUnpackedFloat_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_instReprUnpackedFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_instReprUnpackedFloat_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_instReprUnpackedFloat___closed__0 = (const lean_object*)&l_Float_Model_instReprUnpackedFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_instReprUnpackedFloat = (const lean_object*)&l_Float_Model_instReprUnpackedFloat___closed__0_value;
LEAN_EXPORT uint8_t l_Float_Model_instBEqUnpackedFloat_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_instBEqUnpackedFloat_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_instBEqUnpackedFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_instBEqUnpackedFloat_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_instBEqUnpackedFloat___closed__0 = (const lean_object*)&l_Float_Model_instBEqUnpackedFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_instBEqUnpackedFloat = (const lean_object*)&l_Float_Model_instBEqUnpackedFloat___closed__0_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
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
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Float_Model_UnpackedFloat_ctorIdx(v_x_6_);
lean_dec(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
switch(lean_obj_tag(v_t_8_))
{
case 1:
{
return v_k_9_;
}
case 3:
{
uint8_t v_sign_10_; lean_object* v_mantissa_11_; lean_object* v_exponent_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_sign_10_ = lean_ctor_get_uint8(v_t_8_, sizeof(void*)*2);
v_mantissa_11_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_mantissa_11_);
v_exponent_12_ = lean_ctor_get(v_t_8_, 1);
lean_inc(v_exponent_12_);
lean_dec_ref_known(v_t_8_, 2);
v___x_13_ = lean_box(v_sign_10_);
v___x_14_ = lean_apply_4(v_k_9_, v___x_13_, v_mantissa_11_, v_exponent_12_, lean_box(0));
return v___x_14_;
}
default: 
{
uint8_t v_sign_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_sign_15_ = lean_ctor_get_uint8(v_t_8_, 0);
lean_dec(v_t_8_);
v___x_16_ = lean_box(v_sign_15_);
v___x_17_ = lean_apply_1(v_k_9_, v___x_16_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorElim(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Float_Model_UnpackedFloat_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_26_, v_h_27_, v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_infinity_elim___redArg(lean_object* v_t_30_, lean_object* v_infinity_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_30_, v_infinity_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_infinity_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_infinity_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_34_, v_infinity_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_notANumber_elim___redArg(lean_object* v_t_38_, lean_object* v_notANumber_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_38_, v_notANumber_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_notANumber_elim(lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_notANumber_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_42_, v_notANumber_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_zero_elim___redArg(lean_object* v_t_46_, lean_object* v_zero_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_46_, v_zero_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_zero_elim(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_zero_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_50_, v_zero_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_finite_elim___redArg(lean_object* v_t_54_, lean_object* v_finite_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_54_, v_finite_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_finite_elim(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_finite_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_58_, v_finite_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Float_Model_instReprUnpackedFloat_repr___closed__7(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(2u);
v___x_75_ = lean_nat_to_int(v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l_Float_Model_instReprUnpackedFloat_repr___closed__8(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = lean_nat_to_int(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Float_Model_instReprUnpackedFloat_repr___closed__15(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_nat_to_int(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_instReprUnpackedFloat_repr(lean_object* v_x_92_, lean_object* v_prec_93_){
_start:
{
lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_97_; lean_object* v___y_98_; lean_object* v___y_108_; 
switch(lean_obj_tag(v_x_92_))
{
case 0:
{
uint8_t v_sign_114_; lean_object* v___y_116_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_sign_114_ = lean_ctor_get_uint8(v_x_92_, 0);
lean_dec_ref_known(v_x_92_, 0);
v___x_125_ = lean_unsigned_to_nat(1024u);
v___x_126_ = lean_nat_dec_le(v___x_125_, v_prec_93_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__7, &l_Float_Model_instReprUnpackedFloat_repr___closed__7_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__7);
v___y_116_ = v___x_127_;
goto v___jp_115_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__8, &l_Float_Model_instReprUnpackedFloat_repr___closed__8_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__8);
v___y_116_ = v___x_128_;
goto v___jp_115_;
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_117_ = ((lean_object*)(l_Float_Model_instReprUnpackedFloat_repr___closed__6));
v___x_118_ = lean_unsigned_to_nat(1024u);
v___x_119_ = l_Float_Model_UnpackedFloat_instReprSign_repr(v_sign_114_, v___x_118_);
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_117_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
lean_inc(v___y_116_);
v___x_121_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_121_, 0, v___y_116_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = 0;
v___x_123_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*1, v___x_122_);
v___x_124_ = l_Repr_addAppParen(v___x_123_, v_prec_93_);
return v___x_124_;
}
}
case 1:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1024u);
v___x_130_ = lean_nat_dec_le(v___x_129_, v_prec_93_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__7, &l_Float_Model_instReprUnpackedFloat_repr___closed__7_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__7);
v___y_108_ = v___x_131_;
goto v___jp_107_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__8, &l_Float_Model_instReprUnpackedFloat_repr___closed__8_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__8);
v___y_108_ = v___x_132_;
goto v___jp_107_;
}
}
case 2:
{
uint8_t v_sign_133_; lean_object* v___y_135_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_sign_133_ = lean_ctor_get_uint8(v_x_92_, 0);
lean_dec_ref_known(v_x_92_, 0);
v___x_144_ = lean_unsigned_to_nat(1024u);
v___x_145_ = lean_nat_dec_le(v___x_144_, v_prec_93_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__7, &l_Float_Model_instReprUnpackedFloat_repr___closed__7_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__7);
v___y_135_ = v___x_146_;
goto v___jp_134_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__8, &l_Float_Model_instReprUnpackedFloat_repr___closed__8_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__8);
v___y_135_ = v___x_147_;
goto v___jp_134_;
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_136_ = ((lean_object*)(l_Float_Model_instReprUnpackedFloat_repr___closed__11));
v___x_137_ = lean_unsigned_to_nat(1024u);
v___x_138_ = l_Float_Model_UnpackedFloat_instReprSign_repr(v_sign_133_, v___x_137_);
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_136_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
lean_inc(v___y_135_);
v___x_140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_140_, 0, v___y_135_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = 0;
v___x_142_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*1, v___x_141_);
v___x_143_ = l_Repr_addAppParen(v___x_142_, v_prec_93_);
return v___x_143_;
}
}
default: 
{
uint8_t v_sign_148_; lean_object* v_mantissa_149_; lean_object* v_exponent_150_; lean_object* v___y_152_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_sign_148_ = lean_ctor_get_uint8(v_x_92_, sizeof(void*)*2);
v_mantissa_149_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_mantissa_149_);
v_exponent_150_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_exponent_150_);
lean_dec_ref_known(v_x_92_, 2);
v___x_170_ = lean_unsigned_to_nat(1024u);
v___x_171_ = lean_nat_dec_le(v___x_170_, v_prec_93_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__7, &l_Float_Model_instReprUnpackedFloat_repr___closed__7_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__7);
v___y_152_ = v___x_172_;
goto v___jp_151_;
}
else
{
lean_object* v___x_173_; 
v___x_173_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__8, &l_Float_Model_instReprUnpackedFloat_repr___closed__8_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__8);
v___y_152_ = v___x_173_;
goto v___jp_151_;
}
v___jp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_153_ = lean_box(1);
v___x_154_ = ((lean_object*)(l_Float_Model_instReprUnpackedFloat_repr___closed__14));
v___x_155_ = lean_unsigned_to_nat(1024u);
v___x_156_ = l_Float_Model_UnpackedFloat_instReprSign_repr(v_sign_148_, v___x_155_);
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_154_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_153_);
v___x_159_ = l_Nat_reprFast(v_mantissa_149_);
v___x_160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_158_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_153_);
v___x_163_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__15, &l_Float_Model_instReprUnpackedFloat_repr___closed__15_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__15);
v___x_164_ = lean_int_dec_lt(v_exponent_150_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = l_Int_repr(v_exponent_150_);
lean_dec(v_exponent_150_);
v___x_166_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
v___y_95_ = v___y_152_;
v___y_96_ = v___x_162_;
v___y_97_ = v___x_153_;
v___y_98_ = v___x_166_;
goto v___jp_94_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = l_Int_repr(v_exponent_150_);
lean_dec(v_exponent_150_);
v___x_168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
v___x_169_ = l_Repr_addAppParen(v___x_168_, v___x_155_);
v___y_95_ = v___y_152_;
v___y_96_ = v___x_162_;
v___y_97_ = v___x_153_;
v___y_98_ = v___x_169_;
goto v___jp_94_;
}
}
}
}
v___jp_94_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___y_96_);
lean_ctor_set(v___x_99_, 1, v___y_98_);
lean_inc(v___y_97_);
v___x_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___y_97_);
v___x_101_ = ((lean_object*)(l_Float_Model_instReprUnpackedFloat_repr___closed__1));
v___x_102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
lean_inc(v___y_95_);
v___x_103_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_103_, 0, v___y_95_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = 0;
v___x_105_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*1, v___x_104_);
v___x_106_ = l_Repr_addAppParen(v___x_105_, v_prec_93_);
return v___x_106_;
}
v___jp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_109_ = ((lean_object*)(l_Float_Model_instReprUnpackedFloat_repr___closed__3));
lean_inc(v___y_108_);
v___x_110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_110_, 0, v___y_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = 0;
v___x_112_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*1, v___x_111_);
v___x_113_ = l_Repr_addAppParen(v___x_112_, v_prec_93_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_instReprUnpackedFloat_repr___boxed(lean_object* v_x_174_, lean_object* v_prec_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Float_Model_instReprUnpackedFloat_repr(v_x_174_, v_prec_175_);
lean_dec(v_prec_175_);
return v_res_176_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_instBEqUnpackedFloat_beq(lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
switch(lean_obj_tag(v_x_179_))
{
case 0:
{
if (lean_obj_tag(v_x_180_) == 0)
{
uint8_t v_sign_181_; uint8_t v_sign_182_; uint8_t v___x_183_; 
v_sign_181_ = lean_ctor_get_uint8(v_x_179_, 0);
v_sign_182_ = lean_ctor_get_uint8(v_x_180_, 0);
v___x_183_ = l_Float_Model_UnpackedFloat_instBEqSign_beq(v_sign_181_, v_sign_182_);
return v___x_183_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = 0;
return v___x_184_;
}
}
case 1:
{
if (lean_obj_tag(v_x_180_) == 1)
{
uint8_t v___x_185_; 
v___x_185_ = 1;
return v___x_185_;
}
else
{
uint8_t v___x_186_; 
v___x_186_ = 0;
return v___x_186_;
}
}
case 2:
{
if (lean_obj_tag(v_x_180_) == 2)
{
uint8_t v_sign_187_; uint8_t v_sign_188_; uint8_t v___x_189_; 
v_sign_187_ = lean_ctor_get_uint8(v_x_179_, 0);
v_sign_188_ = lean_ctor_get_uint8(v_x_180_, 0);
v___x_189_ = l_Float_Model_UnpackedFloat_instBEqSign_beq(v_sign_187_, v_sign_188_);
return v___x_189_;
}
else
{
uint8_t v___x_190_; 
v___x_190_ = 0;
return v___x_190_;
}
}
default: 
{
if (lean_obj_tag(v_x_180_) == 3)
{
uint8_t v_sign_191_; lean_object* v_mantissa_192_; lean_object* v_exponent_193_; uint8_t v_sign_194_; lean_object* v_mantissa_195_; lean_object* v_exponent_196_; uint8_t v___x_197_; 
v_sign_191_ = lean_ctor_get_uint8(v_x_179_, sizeof(void*)*2);
v_mantissa_192_ = lean_ctor_get(v_x_179_, 0);
v_exponent_193_ = lean_ctor_get(v_x_179_, 1);
v_sign_194_ = lean_ctor_get_uint8(v_x_180_, sizeof(void*)*2);
v_mantissa_195_ = lean_ctor_get(v_x_180_, 0);
v_exponent_196_ = lean_ctor_get(v_x_180_, 1);
v___x_197_ = l_Float_Model_UnpackedFloat_instBEqSign_beq(v_sign_191_, v_sign_194_);
if (v___x_197_ == 0)
{
return v___x_197_;
}
else
{
uint8_t v___x_198_; 
v___x_198_ = lean_nat_dec_eq(v_mantissa_192_, v_mantissa_195_);
if (v___x_198_ == 0)
{
return v___x_198_;
}
else
{
uint8_t v___x_199_; 
v___x_199_ = lean_int_dec_eq(v_exponent_193_, v_exponent_196_);
return v___x_199_;
}
}
}
else
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_instBEqUnpackedFloat_beq___boxed(lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Float_Model_instBEqUnpackedFloat_beq(v_x_201_, v_x_202_);
lean_dec(v_x_202_);
lean_dec(v_x_201_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Sign(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Sign(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Sign(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Sign(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
