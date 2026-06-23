// Lean compiler output
// Module: Init.Data.Float.Model.Format.Basic
// Imports: public import Init.Data.Nat.Log2 public import Init.Data.Int.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_totalExponent_spec__0(lean_object*);
static lean_once_cell_t l_Float_Model_totalExponent___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_totalExponent___closed__0;
LEAN_EXPORT lean_object* l_Float_Model_totalExponent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_totalExponent___boxed(lean_object*, lean_object*);
static const lean_string_object l_Float_Model_Format_hm___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__0 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__0_value;
static const lean_string_object l_Float_Model_Format_hm___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__1 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__1_value;
static const lean_string_object l_Float_Model_Format_hm___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__2 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__2_value;
static const lean_string_object l_Float_Model_Format_hm___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__3 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__3_value;
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__4_value_aux_0),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__4_value_aux_1),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__4_value_aux_2),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__4 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__4_value;
static const lean_array_object l_Float_Model_Format_hm___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__5 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__5_value;
static const lean_string_object l_Float_Model_Format_hm___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__6 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__6_value;
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__7_value_aux_0),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__7_value_aux_1),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__7_value_aux_2),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__7 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__7_value;
static const lean_string_object l_Float_Model_Format_hm___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__8 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__8_value;
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__9 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__9_value;
static const lean_string_object l_Float_Model_Format_hm___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__10 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__10_value;
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__11_value_aux_0),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__11_value_aux_1),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__11_value_aux_2),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__11 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__11_value;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__12;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__13;
static const lean_string_object l_Float_Model_Format_hm___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__14 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__14_value;
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__15_value_aux_0),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__15_value_aux_1),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__15_value_aux_2),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__15 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__15_value;
static const lean_ctor_object l_Float_Model_Format_hm___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__9_value),((lean_object*)&l_Float_Model_Format_hm___autoParam___closed__5_value)}};
static const lean_object* l_Float_Model_Format_hm___autoParam___closed__16 = (const lean_object*)&l_Float_Model_Format_hm___autoParam___closed__16_value;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__17;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__18;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__19;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__20;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__21;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__22;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__23;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__24;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__25;
static lean_once_cell_t l_Float_Model_Format_hm___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_hm___autoParam___closed__26;
LEAN_EXPORT lean_object* l_Float_Model_Format_hm___autoParam;
LEAN_EXPORT lean_object* l_Float_Model_Format_he___autoParam;
static const lean_ctor_object l_Float_Model_Format_binary32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l_Float_Model_Format_binary32___closed__0 = (const lean_object*)&l_Float_Model_Format_binary32___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_Format_binary32 = (const lean_object*)&l_Float_Model_Format_binary32___closed__0_value;
static const lean_ctor_object l_Float_Model_Format_binary64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)(((size_t)(11) << 1) | 1))}};
static const lean_object* l_Float_Model_Format_binary64___closed__0 = (const lean_object*)&l_Float_Model_Format_binary64___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_Format_binary64 = (const lean_object*)&l_Float_Model_Format_binary64___closed__0_value;
LEAN_EXPORT lean_object* l_Float_Model_Format_numBits(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_Format_numBits___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_Format_mantissaBits(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_Format_mantissaBits___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_Format_exponentBias(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_Format_exponentBias___boxed(lean_object*);
static lean_once_cell_t l_Float_Model_Format_minExponent___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_minExponent___closed__0;
static lean_once_cell_t l_Float_Model_Format_minExponent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_Format_minExponent___closed__1;
LEAN_EXPORT lean_object* l_Float_Model_Format_minExponent(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_Format_minExponent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_Format_targetExponent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_Format_targetExponent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_totalExponent_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Float_Model_totalExponent___closed__0(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_totalExponent(lean_object* v_mantissa_5_, lean_object* v_exponent_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = lean_nat_log2(v_mantissa_5_);
v___x_8_ = lean_nat_to_int(v___x_7_);
v___x_9_ = lean_obj_once(&l_Float_Model_totalExponent___closed__0, &l_Float_Model_totalExponent___closed__0_once, _init_l_Float_Model_totalExponent___closed__0);
v___x_10_ = lean_int_add(v___x_8_, v___x_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_int_add(v___x_10_, v_exponent_6_);
lean_dec(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_totalExponent___boxed(lean_object* v_mantissa_12_, lean_object* v_exponent_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Float_Model_totalExponent(v_mantissa_12_, v_exponent_13_);
lean_dec(v_exponent_13_);
lean_dec(v_mantissa_12_);
return v_res_14_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__12(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__10));
v___x_42_ = l_Lean_mkAtom(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__13(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__12, &l_Float_Model_Format_hm___autoParam___closed__12_once, _init_l_Float_Model_Format_hm___autoParam___closed__12);
v___x_44_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__5));
v___x_45_ = lean_array_push(v___x_44_, v___x_43_);
return v___x_45_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__17(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__16));
v___x_57_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__18(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__17, &l_Float_Model_Format_hm___autoParam___closed__17_once, _init_l_Float_Model_Format_hm___autoParam___closed__17);
v___x_60_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__15));
v___x_61_ = lean_box(2);
v___x_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__19(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__18, &l_Float_Model_Format_hm___autoParam___closed__18_once, _init_l_Float_Model_Format_hm___autoParam___closed__18);
v___x_64_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__13, &l_Float_Model_Format_hm___autoParam___closed__13_once, _init_l_Float_Model_Format_hm___autoParam___closed__13);
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__20(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__19, &l_Float_Model_Format_hm___autoParam___closed__19_once, _init_l_Float_Model_Format_hm___autoParam___closed__19);
v___x_67_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__11));
v___x_68_ = lean_box(2);
v___x_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__21(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__20, &l_Float_Model_Format_hm___autoParam___closed__20_once, _init_l_Float_Model_Format_hm___autoParam___closed__20);
v___x_71_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__5));
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__22(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__21, &l_Float_Model_Format_hm___autoParam___closed__21_once, _init_l_Float_Model_Format_hm___autoParam___closed__21);
v___x_74_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__9));
v___x_75_ = lean_box(2);
v___x_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__23(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__22, &l_Float_Model_Format_hm___autoParam___closed__22_once, _init_l_Float_Model_Format_hm___autoParam___closed__22);
v___x_78_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__5));
v___x_79_ = lean_array_push(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__24(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_80_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__23, &l_Float_Model_Format_hm___autoParam___closed__23_once, _init_l_Float_Model_Format_hm___autoParam___closed__23);
v___x_81_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__7));
v___x_82_ = lean_box(2);
v___x_83_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_81_);
lean_ctor_set(v___x_83_, 2, v___x_80_);
return v___x_83_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__25(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__24, &l_Float_Model_Format_hm___autoParam___closed__24_once, _init_l_Float_Model_Format_hm___autoParam___closed__24);
v___x_85_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__5));
v___x_86_ = lean_array_push(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam___closed__26(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__25, &l_Float_Model_Format_hm___autoParam___closed__25_once, _init_l_Float_Model_Format_hm___autoParam___closed__25);
v___x_88_ = ((lean_object*)(l_Float_Model_Format_hm___autoParam___closed__4));
v___x_89_ = lean_box(2);
v___x_90_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_87_);
return v___x_90_;
}
}
static lean_object* _init_l_Float_Model_Format_hm___autoParam(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__26, &l_Float_Model_Format_hm___autoParam___closed__26_once, _init_l_Float_Model_Format_hm___autoParam___closed__26);
return v___x_91_;
}
}
static lean_object* _init_l_Float_Model_Format_he___autoParam(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_once(&l_Float_Model_Format_hm___autoParam___closed__26, &l_Float_Model_Format_hm___autoParam___closed__26_once, _init_l_Float_Model_Format_hm___autoParam___closed__26);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_Format_numBits(lean_object* v_spec_101_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_102_; lean_object* v_exponentBits_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_mantissaBitsWithoutImplicit_102_ = lean_ctor_get(v_spec_101_, 0);
v_exponentBits_103_ = lean_ctor_get(v_spec_101_, 1);
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = lean_nat_add(v___x_104_, v_exponentBits_103_);
v___x_106_ = lean_nat_add(v___x_105_, v_mantissaBitsWithoutImplicit_102_);
lean_dec(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_Format_numBits___boxed(lean_object* v_spec_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Float_Model_Format_numBits(v_spec_107_);
lean_dec_ref(v_spec_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_Format_mantissaBits(lean_object* v_spec_109_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_mantissaBitsWithoutImplicit_110_ = lean_ctor_get(v_spec_109_, 0);
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v___x_111_, v_mantissaBitsWithoutImplicit_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_Format_mantissaBits___boxed(lean_object* v_spec_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Float_Model_Format_mantissaBits(v_spec_113_);
lean_dec_ref(v_spec_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_Format_exponentBias(lean_object* v_spec_115_){
_start:
{
lean_object* v_exponentBits_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_exponentBits_116_ = lean_ctor_get(v_spec_115_, 1);
v___x_117_ = lean_unsigned_to_nat(2u);
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_sub(v_exponentBits_116_, v___x_118_);
v___x_120_ = lean_nat_pow(v___x_117_, v___x_119_);
lean_dec(v___x_119_);
v___x_121_ = lean_nat_sub(v___x_120_, v___x_118_);
lean_dec(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_Format_exponentBias___boxed(lean_object* v_spec_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Float_Model_Format_exponentBias(v_spec_122_);
lean_dec_ref(v_spec_122_);
return v_res_123_;
}
}
static lean_object* _init_l_Float_Model_Format_minExponent___closed__0(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(3u);
v___x_125_ = lean_nat_to_int(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Float_Model_Format_minExponent___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(2u);
v___x_127_ = lean_nat_to_int(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_Format_minExponent(lean_object* v_spec_128_){
_start:
{
lean_object* v_exponentBits_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_exponentBits_129_ = lean_ctor_get(v_spec_128_, 1);
v___x_130_ = lean_obj_once(&l_Float_Model_Format_minExponent___closed__0, &l_Float_Model_Format_minExponent___closed__0_once, _init_l_Float_Model_Format_minExponent___closed__0);
v___x_131_ = lean_obj_once(&l_Float_Model_Format_minExponent___closed__1, &l_Float_Model_Format_minExponent___closed__1_once, _init_l_Float_Model_Format_minExponent___closed__1);
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_sub(v_exponentBits_129_, v___x_132_);
v___x_134_ = l_Int_pow(v___x_131_, v___x_133_);
lean_dec(v___x_133_);
v___x_135_ = lean_int_sub(v___x_130_, v___x_134_);
lean_dec(v___x_134_);
v___x_136_ = l_Float_Model_Format_mantissaBits(v_spec_128_);
v___x_137_ = lean_nat_to_int(v___x_136_);
v___x_138_ = lean_int_sub(v___x_135_, v___x_137_);
lean_dec(v___x_137_);
lean_dec(v___x_135_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_Format_minExponent___boxed(lean_object* v_spec_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Float_Model_Format_minExponent(v_spec_139_);
lean_dec_ref(v_spec_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_Format_targetExponent(lean_object* v_spec_141_, lean_object* v_totalExponent_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_143_ = l_Float_Model_Format_mantissaBits(v_spec_141_);
v___x_144_ = lean_nat_to_int(v___x_143_);
v___x_145_ = lean_int_sub(v_totalExponent_142_, v___x_144_);
lean_dec(v___x_144_);
v___x_146_ = l_Float_Model_Format_minExponent(v_spec_141_);
v___x_147_ = lean_int_dec_le(v___x_145_, v___x_146_);
if (v___x_147_ == 0)
{
lean_dec(v___x_146_);
return v___x_145_;
}
else
{
lean_dec(v___x_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_Format_targetExponent___boxed(lean_object* v_spec_148_, lean_object* v_totalExponent_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Float_Model_Format_targetExponent(v_spec_148_, v_totalExponent_149_);
lean_dec(v_totalExponent_149_);
lean_dec_ref(v_spec_148_);
return v_res_150_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Format_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Format_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Float_Model_Format_hm___autoParam = _init_l_Float_Model_Format_hm___autoParam();
lean_mark_persistent(l_Float_Model_Format_hm___autoParam);
l_Float_Model_Format_he___autoParam = _init_l_Float_Model_Format_he___autoParam();
lean_mark_persistent(l_Float_Model_Format_he___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Format_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Format_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
