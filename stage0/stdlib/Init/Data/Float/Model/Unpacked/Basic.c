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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_instReprSign_repr(uint8_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Float_Model_UnpackedFloat_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 1:
{
return v_k_6_;
}
case 3:
{
uint8_t v_sign_7_; lean_object* v_mantissa_8_; lean_object* v_exponent_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_sign_7_ = lean_ctor_get_uint8(v_t_5_, sizeof(void*)*2);
v_mantissa_8_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_mantissa_8_);
v_exponent_9_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_exponent_9_);
lean_dec_ref_known(v_t_5_, 2);
v___x_10_ = lean_box(v_sign_7_);
v___x_11_ = lean_apply_4(v_k_6_, v___x_10_, v_mantissa_8_, v_exponent_9_, lean_box(0));
return v___x_11_;
}
default: 
{
uint8_t v_sign_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_sign_12_ = lean_ctor_get_uint8(v_t_5_, 0);
lean_dec(v_t_5_);
v___x_13_ = lean_box(v_sign_12_);
v___x_14_ = lean_apply_1(v_k_6_, v___x_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Float_Model_UnpackedFloat_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_infinity_elim___redArg(lean_object* v_t_27_, lean_object* v_infinity_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_27_, v_infinity_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_infinity_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_infinity_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_31_, v_infinity_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_notANumber_elim___redArg(lean_object* v_t_35_, lean_object* v_notANumber_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_35_, v_notANumber_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_notANumber_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_notANumber_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_39_, v_notANumber_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_zero_elim___redArg(lean_object* v_t_43_, lean_object* v_zero_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_43_, v_zero_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_zero_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_zero_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_47_, v_zero_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_finite_elim___redArg(lean_object* v_t_51_, lean_object* v_finite_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_51_, v_finite_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_finite_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_finite_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Float_Model_UnpackedFloat_ctorElim___redArg(v_t_55_, v_finite_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Float_Model_instReprUnpackedFloat_repr___closed__7(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(2u);
v___x_72_ = lean_nat_to_int(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Float_Model_instReprUnpackedFloat_repr___closed__8(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Float_Model_instReprUnpackedFloat_repr___closed__15(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_nat_to_int(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_instReprUnpackedFloat_repr(lean_object* v_x_89_, lean_object* v_prec_90_){
_start:
{
lean_object* v___y_92_; lean_object* v___y_93_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_105_; 
switch(lean_obj_tag(v_x_89_))
{
case 0:
{
uint8_t v_sign_111_; lean_object* v___y_113_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_sign_111_ = lean_ctor_get_uint8(v_x_89_, 0);
lean_dec_ref_known(v_x_89_, 0);
v___x_122_ = lean_unsigned_to_nat(1024u);
v___x_123_ = lean_nat_dec_le(v___x_122_, v_prec_90_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__7, &l_Float_Model_instReprUnpackedFloat_repr___closed__7_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__7);
v___y_113_ = v___x_124_;
goto v___jp_112_;
}
else
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__8, &l_Float_Model_instReprUnpackedFloat_repr___closed__8_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__8);
v___y_113_ = v___x_125_;
goto v___jp_112_;
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_114_ = ((lean_object*)(l_Float_Model_instReprUnpackedFloat_repr___closed__6));
v___x_115_ = lean_unsigned_to_nat(1024u);
v___x_116_ = l_Float_Model_UnpackedFloat_instReprSign_repr(v_sign_111_, v___x_115_);
v___x_117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_114_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
lean_inc(v___y_113_);
v___x_118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_118_, 0, v___y_113_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = 0;
v___x_120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_119_);
v___x_121_ = l_Repr_addAppParen(v___x_120_, v_prec_90_);
return v___x_121_;
}
}
case 1:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1024u);
v___x_127_ = lean_nat_dec_le(v___x_126_, v_prec_90_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__7, &l_Float_Model_instReprUnpackedFloat_repr___closed__7_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__7);
v___y_105_ = v___x_128_;
goto v___jp_104_;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__8, &l_Float_Model_instReprUnpackedFloat_repr___closed__8_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__8);
v___y_105_ = v___x_129_;
goto v___jp_104_;
}
}
case 2:
{
uint8_t v_sign_130_; lean_object* v___y_132_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_sign_130_ = lean_ctor_get_uint8(v_x_89_, 0);
lean_dec_ref_known(v_x_89_, 0);
v___x_141_ = lean_unsigned_to_nat(1024u);
v___x_142_ = lean_nat_dec_le(v___x_141_, v_prec_90_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__7, &l_Float_Model_instReprUnpackedFloat_repr___closed__7_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__7);
v___y_132_ = v___x_143_;
goto v___jp_131_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__8, &l_Float_Model_instReprUnpackedFloat_repr___closed__8_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__8);
v___y_132_ = v___x_144_;
goto v___jp_131_;
}
v___jp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_133_ = ((lean_object*)(l_Float_Model_instReprUnpackedFloat_repr___closed__11));
v___x_134_ = lean_unsigned_to_nat(1024u);
v___x_135_ = l_Float_Model_UnpackedFloat_instReprSign_repr(v_sign_130_, v___x_134_);
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_133_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
lean_inc(v___y_132_);
v___x_137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_137_, 0, v___y_132_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = 0;
v___x_139_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*1, v___x_138_);
v___x_140_ = l_Repr_addAppParen(v___x_139_, v_prec_90_);
return v___x_140_;
}
}
default: 
{
uint8_t v_sign_145_; lean_object* v_mantissa_146_; lean_object* v_exponent_147_; lean_object* v___y_149_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_sign_145_ = lean_ctor_get_uint8(v_x_89_, sizeof(void*)*2);
v_mantissa_146_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_mantissa_146_);
v_exponent_147_ = lean_ctor_get(v_x_89_, 1);
lean_inc(v_exponent_147_);
lean_dec_ref_known(v_x_89_, 2);
v___x_167_ = lean_unsigned_to_nat(1024u);
v___x_168_ = lean_nat_dec_le(v___x_167_, v_prec_90_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
v___x_169_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__7, &l_Float_Model_instReprUnpackedFloat_repr___closed__7_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__7);
v___y_149_ = v___x_169_;
goto v___jp_148_;
}
else
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__8, &l_Float_Model_instReprUnpackedFloat_repr___closed__8_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__8);
v___y_149_ = v___x_170_;
goto v___jp_148_;
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_150_ = lean_box(1);
v___x_151_ = ((lean_object*)(l_Float_Model_instReprUnpackedFloat_repr___closed__14));
v___x_152_ = lean_unsigned_to_nat(1024u);
v___x_153_ = l_Float_Model_UnpackedFloat_instReprSign_repr(v_sign_145_, v___x_152_);
v___x_154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_151_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_150_);
v___x_156_ = l_Nat_reprFast(v_mantissa_146_);
v___x_157_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
v___x_158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_155_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_150_);
v___x_160_ = lean_obj_once(&l_Float_Model_instReprUnpackedFloat_repr___closed__15, &l_Float_Model_instReprUnpackedFloat_repr___closed__15_once, _init_l_Float_Model_instReprUnpackedFloat_repr___closed__15);
v___x_161_ = lean_int_dec_lt(v_exponent_147_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = l_Int_repr(v_exponent_147_);
lean_dec(v_exponent_147_);
v___x_163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
v___y_92_ = v___x_159_;
v___y_93_ = v___y_149_;
v___y_94_ = v___x_150_;
v___y_95_ = v___x_163_;
goto v___jp_91_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = l_Int_repr(v_exponent_147_);
lean_dec(v_exponent_147_);
v___x_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
v___x_166_ = l_Repr_addAppParen(v___x_165_, v___x_152_);
v___y_92_ = v___x_159_;
v___y_93_ = v___y_149_;
v___y_94_ = v___x_150_;
v___y_95_ = v___x_166_;
goto v___jp_91_;
}
}
}
}
v___jp_91_:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___y_92_);
lean_ctor_set(v___x_96_, 1, v___y_95_);
lean_inc(v___y_94_);
v___x_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___y_94_);
v___x_98_ = ((lean_object*)(l_Float_Model_instReprUnpackedFloat_repr___closed__1));
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
lean_inc(v___y_93_);
v___x_100_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_100_, 0, v___y_93_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = 0;
v___x_102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1, v___x_101_);
v___x_103_ = l_Repr_addAppParen(v___x_102_, v_prec_90_);
return v___x_103_;
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_106_ = ((lean_object*)(l_Float_Model_instReprUnpackedFloat_repr___closed__3));
lean_inc(v___y_105_);
v___x_107_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_107_, 0, v___y_105_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = 0;
v___x_109_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*1, v___x_108_);
v___x_110_ = l_Repr_addAppParen(v___x_109_, v_prec_90_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_instReprUnpackedFloat_repr___boxed(lean_object* v_x_171_, lean_object* v_prec_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Float_Model_instReprUnpackedFloat_repr(v_x_171_, v_prec_172_);
lean_dec(v_prec_172_);
return v_res_173_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_instBEqUnpackedFloat_beq(lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
uint8_t v_a_179_; uint8_t v_b_180_; 
switch(lean_obj_tag(v_x_176_))
{
case 0:
{
if (lean_obj_tag(v_x_177_) == 0)
{
uint8_t v_sign_186_; uint8_t v_sign_187_; 
v_sign_186_ = lean_ctor_get_uint8(v_x_176_, 0);
v_sign_187_ = lean_ctor_get_uint8(v_x_177_, 0);
v_a_179_ = v_sign_186_;
v_b_180_ = v_sign_187_;
goto v___jp_178_;
}
else
{
uint8_t v___x_188_; 
v___x_188_ = 0;
return v___x_188_;
}
}
case 1:
{
if (lean_obj_tag(v_x_177_) == 1)
{
uint8_t v___x_189_; 
v___x_189_ = 1;
return v___x_189_;
}
else
{
uint8_t v___x_190_; 
v___x_190_ = 0;
return v___x_190_;
}
}
case 2:
{
if (lean_obj_tag(v_x_177_) == 2)
{
uint8_t v_sign_191_; uint8_t v_sign_192_; 
v_sign_191_ = lean_ctor_get_uint8(v_x_176_, 0);
v_sign_192_ = lean_ctor_get_uint8(v_x_177_, 0);
v_a_179_ = v_sign_191_;
v_b_180_ = v_sign_192_;
goto v___jp_178_;
}
else
{
uint8_t v___x_193_; 
v___x_193_ = 0;
return v___x_193_;
}
}
default: 
{
if (lean_obj_tag(v_x_177_) == 3)
{
uint8_t v_sign_194_; lean_object* v_mantissa_195_; lean_object* v_exponent_196_; uint8_t v_sign_197_; lean_object* v_mantissa_198_; lean_object* v_exponent_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_sign_194_ = lean_ctor_get_uint8(v_x_176_, sizeof(void*)*2);
v_mantissa_195_ = lean_ctor_get(v_x_176_, 0);
v_exponent_196_ = lean_ctor_get(v_x_176_, 1);
v_sign_197_ = lean_ctor_get_uint8(v_x_177_, sizeof(void*)*2);
v_mantissa_198_ = lean_ctor_get(v_x_177_, 0);
v_exponent_199_ = lean_ctor_get(v_x_177_, 1);
v___x_200_ = lean_box(v_sign_194_);
v___x_201_ = lean_obj_tag_nat(v___x_200_);
lean_dec(v___x_200_);
v___x_202_ = lean_box(v_sign_197_);
v___x_203_ = lean_obj_tag_nat(v___x_202_);
lean_dec(v___x_202_);
v___x_204_ = lean_nat_dec_eq(v___x_201_, v___x_203_);
if (v___x_204_ == 0)
{
return v___x_204_;
}
else
{
uint8_t v___x_205_; 
v___x_205_ = lean_nat_dec_eq(v_mantissa_195_, v_mantissa_198_);
if (v___x_205_ == 0)
{
return v___x_205_;
}
else
{
uint8_t v___x_206_; 
v___x_206_ = lean_int_dec_eq(v_exponent_196_, v_exponent_199_);
return v___x_206_;
}
}
}
else
{
uint8_t v___x_207_; 
v___x_207_ = 0;
return v___x_207_;
}
}
}
v___jp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_181_ = lean_box(v_a_179_);
v___x_182_ = lean_obj_tag_nat(v___x_181_);
lean_dec(v___x_181_);
v___x_183_ = lean_box(v_b_180_);
v___x_184_ = lean_obj_tag_nat(v___x_183_);
lean_dec(v___x_183_);
v___x_185_ = lean_nat_dec_eq(v___x_182_, v___x_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_instBEqUnpackedFloat_beq___boxed(lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Float_Model_instBEqUnpackedFloat_beq(v_x_208_, v_x_209_);
lean_dec(v_x_209_);
lean_dec(v_x_208_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Sign(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
