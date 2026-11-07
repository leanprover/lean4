// Lean compiler output
// Module: Lean.Meta.Sym.LitValues
// Imports: public import Lean.Expr public import Init.Data.Rat
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int8_of_int(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
uint64_t lean_int64_of_int(lean_object*);
uint32_t lean_int32_of_int(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
uint16_t lean_int16_of_int(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatValue_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isNatValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isNatValue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getIntValue_x3f_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ofNatLT"};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 44, 243, 4, 118, 78, 150, 28)}};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_Sym_getFinValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_getFinValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l_Lean_Meta_Sym_getFinValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getFinValue_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Lean_Meta_Sym_getCharValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_Meta_Sym_getCharValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getBoolValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Sym_getBoolValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getBoolValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getBoolValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Sym_getBoolValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getBoolValue_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_getBoolValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Sym_getBoolValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getBoolValue_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolValue_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object* v_e_6_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = l_Lean_Expr_cleanupAnnotations(v_e_6_);
v___x_8_ = l_Lean_Expr_isApp(v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_dec_ref(v___x_7_);
v___x_9_ = lean_box(0);
return v___x_9_;
}
else
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7_);
lean_dec_ref(v___x_7_);
v___x_11_ = l_Lean_Expr_isApp(v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; 
lean_dec_ref(v___x_10_);
v___x_12_ = lean_box(0);
return v___x_12_;
}
else
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = l_Lean_Expr_appFnCleanup___redArg(v___x_10_);
v___x_14_ = l_Lean_Expr_isApp(v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
lean_dec_ref(v___x_13_);
lean_dec_ref(v___x_10_);
v___x_15_ = lean_box(0);
return v___x_15_;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_16_ = l_Lean_Expr_appFnCleanup___redArg(v___x_13_);
lean_dec_ref(v___x_13_);
v___x_17_ = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
v___x_18_ = l_Lean_Expr_isConstOf(v___x_16_, v___x_17_);
lean_dec_ref(v___x_16_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
lean_dec_ref(v___x_10_);
v___x_19_ = lean_box(0);
return v___x_19_;
}
else
{
lean_object* v_arg_20_; 
v_arg_20_ = lean_ctor_get(v___x_10_, 1);
lean_inc_ref(v_arg_20_);
lean_dec_ref(v___x_10_);
if (lean_obj_tag(v_arg_20_) == 9)
{
lean_object* v_a_21_; 
v_a_21_ = lean_ctor_get(v_arg_20_, 0);
lean_inc_ref(v_a_21_);
lean_dec_ref_known(v_arg_20_, 1);
if (lean_obj_tag(v_a_21_) == 0)
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
v_val_22_ = lean_ctor_get(v_a_21_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_a_21_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_a_21_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_a_21_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set_tag(v___x_24_, 1);
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
else
{
lean_object* v___x_30_; 
lean_dec_ref(v_a_21_);
v___x_30_ = lean_box(0);
return v___x_30_;
}
}
else
{
lean_object* v___x_31_; 
lean_dec_ref(v_arg_20_);
v___x_31_ = lean_box(0);
return v___x_31_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatValue_x3f___boxed(lean_object* v_e_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_32_);
lean_dec_ref(v_e_32_);
return v_res_33_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isNatValue(lean_object* v_e_34_){
_start:
{
lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_35_ = l_Lean_Expr_cleanupAnnotations(v_e_34_);
v___x_36_ = l_Lean_Expr_isApp(v___x_35_);
if (v___x_36_ == 0)
{
lean_dec_ref(v___x_35_);
return v___x_36_;
}
else
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = l_Lean_Expr_appFnCleanup___redArg(v___x_35_);
lean_dec_ref(v___x_35_);
v___x_38_ = l_Lean_Expr_isApp(v___x_37_);
if (v___x_38_ == 0)
{
lean_dec_ref(v___x_37_);
return v___x_38_;
}
else
{
lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_39_ = l_Lean_Expr_appFnCleanup___redArg(v___x_37_);
v___x_40_ = l_Lean_Expr_isApp(v___x_39_);
if (v___x_40_ == 0)
{
lean_dec_ref(v___x_39_);
lean_dec_ref(v___x_37_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_41_ = l_Lean_Expr_appFnCleanup___redArg(v___x_39_);
lean_dec_ref(v___x_39_);
v___x_42_ = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
v___x_43_ = l_Lean_Expr_isConstOf(v___x_41_, v___x_42_);
lean_dec_ref(v___x_41_);
if (v___x_43_ == 0)
{
lean_dec_ref(v___x_37_);
return v___x_43_;
}
else
{
lean_object* v_arg_44_; uint8_t v___x_45_; 
v_arg_44_ = lean_ctor_get(v___x_37_, 1);
lean_inc_ref(v_arg_44_);
lean_dec_ref(v___x_37_);
v___x_45_ = l_Lean_Expr_isRawNatLit(v_arg_44_);
lean_dec_ref(v_arg_44_);
return v___x_45_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isNatValue___boxed(lean_object* v_e_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_Lean_Meta_Sym_isNatValue(v_e_46_);
lean_dec_ref(v_e_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getIntValue_x3f_spec__0(lean_object* v_a_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_nat_to_int(v_a_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object* v_e_56_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = l_Lean_Expr_cleanupAnnotations(v_e_56_);
v___x_70_ = l_Lean_Expr_isApp(v___x_69_);
if (v___x_70_ == 0)
{
lean_dec_ref(v___x_69_);
goto v___jp_57_;
}
else
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = l_Lean_Expr_appFnCleanup___redArg(v___x_69_);
v___x_72_ = l_Lean_Expr_isApp(v___x_71_);
if (v___x_72_ == 0)
{
lean_dec_ref(v___x_71_);
lean_dec_ref(v___x_69_);
goto v___jp_57_;
}
else
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = l_Lean_Expr_appFnCleanup___redArg(v___x_71_);
lean_dec_ref(v___x_71_);
v___x_74_ = l_Lean_Expr_isApp(v___x_73_);
if (v___x_74_ == 0)
{
lean_dec_ref(v___x_73_);
lean_dec_ref(v___x_69_);
goto v___jp_57_;
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = l_Lean_Expr_appFnCleanup___redArg(v___x_73_);
lean_dec_ref(v___x_73_);
v___x_76_ = ((lean_object*)(l_Lean_Meta_Sym_getIntValue_x3f___closed__2));
v___x_77_ = l_Lean_Expr_isConstOf(v___x_75_, v___x_76_);
lean_dec_ref(v___x_75_);
if (v___x_77_ == 0)
{
lean_dec_ref(v___x_69_);
goto v___jp_57_;
}
else
{
lean_object* v_arg_78_; lean_object* v___x_79_; 
v_arg_78_ = lean_ctor_get(v___x_69_, 1);
lean_inc_ref(v_arg_78_);
lean_dec_ref(v___x_69_);
v___x_79_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_78_);
lean_dec_ref(v_arg_78_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(0);
return v___x_80_;
}
else
{
lean_object* v_val_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_90_; 
v_val_81_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_90_ == 0)
{
v___x_83_ = v___x_79_;
v_isShared_84_ = v_isSharedCheck_90_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_val_81_);
lean_dec(v___x_79_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_90_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_85_ = lean_nat_to_int(v_val_81_);
v___x_86_ = lean_int_neg(v___x_85_);
lean_dec(v___x_85_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_86_);
v___x_88_ = v___x_83_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
}
}
v___jp_57_:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_56_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v___x_59_; 
v___x_59_ = lean_box(0);
return v___x_59_;
}
else
{
lean_object* v_val_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_68_; 
v_val_60_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_68_ == 0)
{
v___x_62_ = v___x_58_;
v_isShared_63_ = v_isSharedCheck_68_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_val_60_);
lean_dec(v___x_58_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_68_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_64_ = lean_nat_to_int(v_val_60_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_64_);
v___x_66_ = v___x_62_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f___boxed(lean_object* v_e_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_91_);
lean_dec_ref(v_e_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__0(lean_object* v_a_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Rat_ofInt(v_a_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(lean_object* v_a_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_nat_to_int(v_a_95_);
v___x_97_ = l_Rat_ofInt(v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f(lean_object* v_e_103_){
_start:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = l_Lean_Expr_cleanupAnnotations(v_e_103_);
v___x_117_ = l_Lean_Expr_isApp(v___x_116_);
if (v___x_117_ == 0)
{
lean_dec_ref(v___x_116_);
goto v___jp_104_;
}
else
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = l_Lean_Expr_appFnCleanup___redArg(v___x_116_);
v___x_119_ = l_Lean_Expr_isApp(v___x_118_);
if (v___x_119_ == 0)
{
lean_dec_ref(v___x_118_);
lean_dec_ref(v___x_116_);
goto v___jp_104_;
}
else
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = l_Lean_Expr_appFnCleanup___redArg(v___x_118_);
v___x_121_ = l_Lean_Expr_isApp(v___x_120_);
if (v___x_121_ == 0)
{
lean_dec_ref(v___x_120_);
lean_dec_ref(v___x_118_);
lean_dec_ref(v___x_116_);
goto v___jp_104_;
}
else
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_120_);
lean_dec_ref(v___x_120_);
v___x_123_ = l_Lean_Expr_isApp(v___x_122_);
if (v___x_123_ == 0)
{
lean_dec_ref(v___x_122_);
lean_dec_ref(v___x_118_);
lean_dec_ref(v___x_116_);
goto v___jp_104_;
}
else
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = l_Lean_Expr_appFnCleanup___redArg(v___x_122_);
lean_dec_ref(v___x_122_);
v___x_125_ = l_Lean_Expr_isApp(v___x_124_);
if (v___x_125_ == 0)
{
lean_dec_ref(v___x_124_);
lean_dec_ref(v___x_118_);
lean_dec_ref(v___x_116_);
goto v___jp_104_;
}
else
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = l_Lean_Expr_appFnCleanup___redArg(v___x_124_);
lean_dec_ref(v___x_124_);
v___x_127_ = l_Lean_Expr_isApp(v___x_126_);
if (v___x_127_ == 0)
{
lean_dec_ref(v___x_126_);
lean_dec_ref(v___x_118_);
lean_dec_ref(v___x_116_);
goto v___jp_104_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_128_ = l_Lean_Expr_appFnCleanup___redArg(v___x_126_);
lean_dec_ref(v___x_126_);
v___x_129_ = ((lean_object*)(l_Lean_Meta_Sym_getRatValue_x3f___closed__2));
v___x_130_ = l_Lean_Expr_isConstOf(v___x_128_, v___x_129_);
lean_dec_ref(v___x_128_);
if (v___x_130_ == 0)
{
lean_dec_ref(v___x_118_);
lean_dec_ref(v___x_116_);
goto v___jp_104_;
}
else
{
lean_object* v_arg_131_; lean_object* v___x_132_; 
v_arg_131_ = lean_ctor_get(v___x_118_, 1);
lean_inc_ref(v_arg_131_);
lean_dec_ref(v___x_118_);
v___x_132_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_131_);
lean_dec_ref(v_arg_131_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v___x_133_; 
lean_dec_ref(v___x_116_);
v___x_133_ = lean_box(0);
return v___x_133_;
}
else
{
lean_object* v_val_134_; lean_object* v_arg_135_; lean_object* v___x_136_; 
v_val_134_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_134_);
lean_dec_ref_known(v___x_132_, 1);
v_arg_135_ = lean_ctor_get(v___x_116_, 1);
lean_inc_ref(v_arg_135_);
lean_dec_ref(v___x_116_);
v___x_136_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_135_);
lean_dec_ref(v_arg_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v___x_137_; 
lean_dec(v_val_134_);
v___x_137_ = lean_box(0);
return v___x_137_;
}
else
{
lean_object* v_val_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_148_; 
v_val_138_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_148_ == 0)
{
v___x_140_ = v___x_136_;
v_isShared_141_ = v_isSharedCheck_148_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_val_138_);
lean_dec(v___x_136_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_148_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_142_ = l_Rat_ofInt(v_val_134_);
v___x_143_ = l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(v_val_138_);
v___x_144_ = l_Rat_div(v___x_142_, v___x_143_);
lean_dec_ref(v___x_142_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_144_);
v___x_146_ = v___x_140_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
}
}
}
}
}
}
v___jp_104_:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_103_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(0);
return v___x_106_;
}
else
{
lean_object* v_val_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_115_; 
v_val_107_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_115_ == 0)
{
v___x_109_ = v___x_105_;
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_val_107_);
lean_dec(v___x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = l_Rat_ofInt(v_val_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f___boxed(lean_object* v_e_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Meta_Sym_getRatValue_x3f(v_e_149_);
lean_dec_ref(v_e_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object* v_e_161_){
_start:
{
lean_object* v_nExpr_163_; lean_object* v_vExpr_164_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = l_Lean_Expr_cleanupAnnotations(v_e_161_);
v___x_181_ = l_Lean_Expr_isApp(v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec_ref(v___x_180_);
v___x_182_ = lean_box(0);
return v___x_182_;
}
else
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = l_Lean_Expr_appFnCleanup___redArg(v___x_180_);
v___x_184_ = l_Lean_Expr_isApp(v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
lean_dec_ref(v___x_183_);
lean_dec_ref(v___x_180_);
v___x_185_ = lean_box(0);
return v___x_185_;
}
else
{
lean_object* v_arg_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_arg_186_ = lean_ctor_get(v___x_183_, 1);
lean_inc_ref(v_arg_186_);
v___x_187_ = l_Lean_Expr_appFnCleanup___redArg(v___x_183_);
lean_dec_ref(v___x_183_);
v___x_188_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1));
v___x_189_ = l_Lean_Expr_isConstOf(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; 
lean_dec_ref(v___x_180_);
v___x_190_ = l_Lean_Expr_isApp(v___x_187_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
lean_dec_ref(v___x_187_);
lean_dec_ref(v_arg_186_);
v___x_191_ = lean_box(0);
return v___x_191_;
}
else
{
lean_object* v_arg_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_arg_192_ = lean_ctor_get(v___x_187_, 1);
lean_inc_ref(v_arg_192_);
v___x_193_ = l_Lean_Expr_appFnCleanup___redArg(v___x_187_);
lean_dec_ref(v___x_187_);
v___x_194_ = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
v___x_195_ = l_Lean_Expr_isConstOf(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3));
v___x_197_ = l_Lean_Expr_isConstOf(v___x_193_, v___x_196_);
lean_dec_ref(v___x_193_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_186_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
v_nExpr_163_ = v_arg_192_;
v_vExpr_164_ = v_arg_186_;
goto v___jp_162_;
}
}
else
{
lean_object* v___x_199_; uint8_t v___x_200_; 
lean_dec_ref(v___x_193_);
v___x_199_ = l_Lean_Expr_cleanupAnnotations(v_arg_192_);
lean_dec_ref(v_arg_192_);
v___x_200_ = l_Lean_Expr_isApp(v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_dec_ref(v___x_199_);
lean_dec_ref(v_arg_186_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_202_ = l_Lean_Expr_appFnCleanup___redArg(v___x_199_);
v___x_203_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4));
v___x_204_ = l_Lean_Expr_isConstOf(v___x_202_, v___x_203_);
lean_dec_ref(v___x_202_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec_ref(v___x_199_);
lean_dec_ref(v_arg_186_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v_arg_206_; lean_object* v___x_207_; 
v_arg_206_ = lean_ctor_get(v___x_199_, 1);
lean_inc_ref(v_arg_206_);
lean_dec_ref(v___x_199_);
v___x_207_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_206_);
lean_dec_ref(v_arg_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v___x_208_; 
lean_dec_ref(v_arg_186_);
v___x_208_ = lean_box(0);
return v___x_208_;
}
else
{
if (lean_obj_tag(v_arg_186_) == 9)
{
lean_object* v_a_209_; 
v_a_209_ = lean_ctor_get(v_arg_186_, 0);
lean_inc_ref(v_a_209_);
lean_dec_ref_known(v_arg_186_, 1);
if (lean_obj_tag(v_a_209_) == 0)
{
lean_object* v_val_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_220_; 
v_val_210_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_220_ == 0)
{
v___x_212_ = v___x_207_;
v_isShared_213_ = v_isSharedCheck_220_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_val_210_);
lean_dec(v___x_207_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_220_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_val_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
v_val_214_ = lean_ctor_get(v_a_209_, 0);
lean_inc(v_val_214_);
lean_dec_ref_known(v_a_209_, 1);
v___x_215_ = l_BitVec_ofNat(v_val_210_, v_val_214_);
lean_dec(v_val_214_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_val_210_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_216_);
v___x_218_ = v___x_212_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_object* v___x_221_; 
lean_dec_ref(v_a_209_);
lean_dec_ref_known(v___x_207_, 1);
v___x_221_ = lean_box(0);
return v___x_221_;
}
}
else
{
lean_object* v___x_222_; 
lean_dec_ref_known(v___x_207_, 1);
lean_dec_ref(v_arg_186_);
v___x_222_ = lean_box(0);
return v___x_222_;
}
}
}
}
}
}
}
else
{
lean_object* v_arg_223_; 
lean_dec_ref(v___x_187_);
v_arg_223_ = lean_ctor_get(v___x_180_, 1);
lean_inc_ref(v_arg_223_);
lean_dec_ref(v___x_180_);
v_nExpr_163_ = v_arg_186_;
v_vExpr_164_ = v_arg_223_;
goto v___jp_162_;
}
}
}
v___jp_162_:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Meta_Sym_getNatValue_x3f(v_nExpr_163_);
lean_dec_ref(v_nExpr_163_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v___x_166_; 
lean_dec_ref(v_vExpr_164_);
v___x_166_ = lean_box(0);
return v___x_166_;
}
else
{
lean_object* v_val_167_; lean_object* v___x_168_; 
v_val_167_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_val_167_);
lean_dec_ref_known(v___x_165_, 1);
v___x_168_ = l_Lean_Meta_Sym_getNatValue_x3f(v_vExpr_164_);
lean_dec_ref(v_vExpr_164_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v___x_169_; 
lean_dec(v_val_167_);
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v_val_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_179_; 
v_val_170_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_179_ == 0)
{
v___x_172_ = v___x_168_;
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_val_170_);
lean_dec(v___x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_174_ = l_BitVec_ofNat(v_val_167_, v_val_170_);
lean_dec(v_val_170_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_val_167_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_177_ = v___x_172_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___boxed(lean_object* v_e_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_e_224_);
lean_dec_ref(v_e_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object* v_e_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; 
v___x_228_ = lean_box(0);
return v___x_228_;
}
else
{
lean_object* v_val_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_238_; 
v_val_229_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_238_ == 0)
{
v___x_231_ = v___x_227_;
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_val_229_);
lean_dec(v___x_227_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_233_ = lean_uint8_of_nat(v_val_229_);
lean_dec(v_val_229_);
v___x_234_ = lean_box(v___x_233_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f___boxed(lean_object* v_e_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v_e_239_);
lean_dec_ref(v_e_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object* v_e_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_241_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v___x_243_; 
v___x_243_ = lean_box(0);
return v___x_243_;
}
else
{
lean_object* v_val_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_253_; 
v_val_244_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_253_ == 0)
{
v___x_246_ = v___x_242_;
v_isShared_247_ = v_isSharedCheck_253_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_val_244_);
lean_dec(v___x_242_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_253_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint16_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_248_ = lean_uint16_of_nat(v_val_244_);
lean_dec(v_val_244_);
v___x_249_ = lean_box(v___x_248_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_249_);
v___x_251_ = v___x_246_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f___boxed(lean_object* v_e_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v_e_254_);
lean_dec_ref(v_e_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object* v_e_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_256_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_box(0);
return v___x_258_;
}
else
{
lean_object* v_val_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_268_; 
v_val_259_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_268_ == 0)
{
v___x_261_ = v___x_257_;
v_isShared_262_ = v_isSharedCheck_268_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_val_259_);
lean_dec(v___x_257_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_268_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
uint32_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_263_ = lean_uint32_of_nat(v_val_259_);
lean_dec(v_val_259_);
v___x_264_ = lean_box_uint32(v___x_263_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_264_);
v___x_266_ = v___x_261_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f___boxed(lean_object* v_e_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v_e_269_);
lean_dec_ref(v_e_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object* v_e_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_271_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_box(0);
return v___x_273_;
}
else
{
lean_object* v_val_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_283_; 
v_val_274_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_283_ == 0)
{
v___x_276_ = v___x_272_;
v_isShared_277_ = v_isSharedCheck_283_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_val_274_);
lean_dec(v___x_272_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_283_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
uint64_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_278_ = lean_uint64_of_nat(v_val_274_);
lean_dec(v_val_274_);
v___x_279_ = lean_box_uint64(v___x_278_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_279_);
v___x_281_ = v___x_276_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f___boxed(lean_object* v_e_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v_e_284_);
lean_dec_ref(v_e_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object* v_e_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_286_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_288_; 
v___x_288_ = lean_box(0);
return v___x_288_;
}
else
{
lean_object* v_val_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_298_; 
v_val_289_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_298_ == 0)
{
v___x_291_ = v___x_287_;
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_val_289_);
lean_dec(v___x_287_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_293_ = lean_int8_of_int(v_val_289_);
lean_dec(v_val_289_);
v___x_294_ = lean_box(v___x_293_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_294_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f___boxed(lean_object* v_e_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_Sym_getInt8Value_x3f(v_e_299_);
lean_dec_ref(v_e_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object* v_e_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_301_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v___x_303_; 
v___x_303_ = lean_box(0);
return v___x_303_;
}
else
{
lean_object* v_val_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_313_; 
v_val_304_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_313_ == 0)
{
v___x_306_ = v___x_302_;
v_isShared_307_ = v_isSharedCheck_313_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_val_304_);
lean_dec(v___x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_313_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint16_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_308_ = lean_int16_of_int(v_val_304_);
lean_dec(v_val_304_);
v___x_309_ = lean_box(v___x_308_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_309_);
v___x_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f___boxed(lean_object* v_e_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Meta_Sym_getInt16Value_x3f(v_e_314_);
lean_dec_ref(v_e_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object* v_e_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_316_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(0);
return v___x_318_;
}
else
{
lean_object* v_val_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_328_; 
v_val_319_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_328_ == 0)
{
v___x_321_ = v___x_317_;
v_isShared_322_ = v_isSharedCheck_328_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_val_319_);
lean_dec(v___x_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_328_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
uint32_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_323_ = lean_int32_of_int(v_val_319_);
lean_dec(v_val_319_);
v___x_324_ = lean_box_uint32(v___x_323_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_324_);
v___x_326_ = v___x_321_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f___boxed(lean_object* v_e_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Meta_Sym_getInt32Value_x3f(v_e_329_);
lean_dec_ref(v_e_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object* v_e_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_331_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_box(0);
return v___x_333_;
}
else
{
lean_object* v_val_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_343_; 
v_val_334_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_343_ == 0)
{
v___x_336_ = v___x_332_;
v_isShared_337_ = v_isSharedCheck_343_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_val_334_);
lean_dec(v___x_332_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_343_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
uint64_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_338_ = lean_int64_of_int(v_val_334_);
lean_dec(v_val_334_);
v___x_339_ = lean_box_uint64(v___x_338_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_339_);
v___x_341_ = v___x_336_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f___boxed(lean_object* v_e_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Meta_Sym_getInt64Value_x3f(v_e_344_);
lean_dec_ref(v_e_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object* v_e_349_){
_start:
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = l_Lean_Expr_cleanupAnnotations(v_e_349_);
v___x_351_ = l_Lean_Expr_isApp(v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec_ref(v___x_350_);
v___x_352_ = lean_box(0);
return v___x_352_;
}
else
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = l_Lean_Expr_appFnCleanup___redArg(v___x_350_);
lean_dec_ref(v___x_350_);
v___x_354_ = l_Lean_Expr_isApp(v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec_ref(v___x_353_);
v___x_355_ = lean_box(0);
return v___x_355_;
}
else
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = l_Lean_Expr_appFnCleanup___redArg(v___x_353_);
v___x_357_ = l_Lean_Expr_isApp(v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec_ref(v___x_356_);
lean_dec_ref(v___x_353_);
v___x_358_ = lean_box(0);
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_359_ = l_Lean_Expr_appFnCleanup___redArg(v___x_356_);
v___x_360_ = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
v___x_361_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_360_);
lean_dec_ref(v___x_359_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec_ref(v___x_356_);
lean_dec_ref(v___x_353_);
v___x_362_ = lean_box(0);
return v___x_362_;
}
else
{
lean_object* v_arg_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_arg_363_ = lean_ctor_get(v___x_356_, 1);
lean_inc_ref(v_arg_363_);
lean_dec_ref(v___x_356_);
v___x_364_ = l_Lean_Expr_cleanupAnnotations(v_arg_363_);
lean_dec_ref(v_arg_363_);
v___x_365_ = l_Lean_Expr_isApp(v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec_ref(v___x_364_);
lean_dec_ref(v___x_353_);
v___x_366_ = lean_box(0);
return v___x_366_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_367_ = l_Lean_Expr_appFnCleanup___redArg(v___x_364_);
v___x_368_ = ((lean_object*)(l_Lean_Meta_Sym_getFinValue_x3f___closed__1));
v___x_369_ = l_Lean_Expr_isConstOf(v___x_367_, v___x_368_);
lean_dec_ref(v___x_367_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec_ref(v___x_364_);
lean_dec_ref(v___x_353_);
v___x_370_ = lean_box(0);
return v___x_370_;
}
else
{
lean_object* v_arg_371_; lean_object* v___x_372_; 
v_arg_371_ = lean_ctor_get(v___x_364_, 1);
lean_inc_ref(v_arg_371_);
lean_dec_ref(v___x_364_);
v___x_372_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_371_);
lean_dec_ref(v_arg_371_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; 
lean_dec_ref(v___x_353_);
v___x_373_ = lean_box(0);
return v___x_373_;
}
else
{
lean_object* v_arg_374_; 
v_arg_374_ = lean_ctor_get(v___x_353_, 1);
lean_inc_ref(v_arg_374_);
lean_dec_ref(v___x_353_);
if (lean_obj_tag(v_arg_374_) == 9)
{
lean_object* v_a_375_; 
v_a_375_ = lean_ctor_get(v_arg_374_, 0);
lean_inc_ref(v_a_375_);
lean_dec_ref_known(v_arg_374_, 1);
if (lean_obj_tag(v_a_375_) == 0)
{
lean_object* v_val_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_389_; 
v_val_376_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_389_ == 0)
{
v___x_378_ = v___x_372_;
v_isShared_379_ = v_isSharedCheck_389_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_val_376_);
lean_dec(v___x_372_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_389_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v_val_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_val_380_ = lean_ctor_get(v_a_375_, 0);
lean_inc(v_val_380_);
lean_dec_ref_known(v_a_375_, 1);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = lean_nat_dec_eq(v_val_376_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_383_ = lean_nat_mod(v_val_380_, v_val_376_);
lean_dec(v_val_380_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_val_376_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_384_);
v___x_386_ = v___x_378_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
else
{
lean_object* v___x_388_; 
lean_dec(v_val_380_);
lean_del_object(v___x_378_);
lean_dec(v_val_376_);
v___x_388_ = lean_box(0);
return v___x_388_;
}
}
}
else
{
lean_object* v___x_390_; 
lean_dec_ref(v_a_375_);
lean_dec_ref_known(v___x_372_, 1);
v___x_390_ = lean_box(0);
return v___x_390_;
}
}
else
{
lean_object* v___x_391_; 
lean_dec_ref(v_arg_374_);
lean_dec_ref_known(v___x_372_, 1);
v___x_391_ = lean_box(0);
return v___x_391_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f___boxed(lean_object* v_e_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Meta_Sym_getFinValue_x3f(v_e_392_);
lean_dec_ref(v_e_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object* v_e_398_){
_start:
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = l_Lean_Expr_cleanupAnnotations(v_e_398_);
v___x_400_ = l_Lean_Expr_isApp(v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
lean_dec_ref(v___x_399_);
v___x_401_ = lean_box(0);
return v___x_401_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_402_ = l_Lean_Expr_appFnCleanup___redArg(v___x_399_);
v___x_403_ = ((lean_object*)(l_Lean_Meta_Sym_getCharValue_x3f___closed__1));
v___x_404_ = l_Lean_Expr_isConstOf(v___x_402_, v___x_403_);
lean_dec_ref(v___x_402_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_dec_ref(v___x_399_);
v___x_405_ = lean_box(0);
return v___x_405_;
}
else
{
lean_object* v_arg_406_; 
v_arg_406_ = lean_ctor_get(v___x_399_, 1);
lean_inc_ref(v_arg_406_);
lean_dec_ref(v___x_399_);
if (lean_obj_tag(v_arg_406_) == 9)
{
lean_object* v_a_407_; 
v_a_407_ = lean_ctor_get(v_arg_406_, 0);
lean_inc_ref(v_a_407_);
lean_dec_ref_known(v_arg_406_, 1);
if (lean_obj_tag(v_a_407_) == 0)
{
lean_object* v_val_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_417_; 
v_val_408_ = lean_ctor_get(v_a_407_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_a_407_);
if (v_isSharedCheck_417_ == 0)
{
v___x_410_ = v_a_407_;
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_val_408_);
lean_dec(v_a_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
uint32_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_412_ = l_Char_ofNat(v_val_408_);
lean_dec(v_val_408_);
v___x_413_ = lean_box_uint32(v___x_412_);
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 1);
lean_ctor_set(v___x_410_, 0, v___x_413_);
v___x_415_ = v___x_410_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
else
{
lean_object* v___x_418_; 
lean_dec_ref(v_a_407_);
v___x_418_ = lean_box(0);
return v___x_418_;
}
}
else
{
lean_object* v___x_419_; 
lean_dec_ref(v_arg_406_);
v___x_419_ = lean_box(0);
return v___x_419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f___boxed(lean_object* v_e_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_Sym_getCharValue_x3f(v_e_420_);
lean_dec_ref(v_e_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object* v_e_422_){
_start:
{
if (lean_obj_tag(v_e_422_) == 9)
{
lean_object* v_a_423_; 
v_a_423_ = lean_ctor_get(v_e_422_, 0);
lean_inc_ref(v_a_423_);
lean_dec_ref_known(v_e_422_, 1);
if (lean_obj_tag(v_a_423_) == 1)
{
lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_val_424_ = lean_ctor_get(v_a_423_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_a_423_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v_a_423_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_dec(v_a_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_val_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_object* v___x_432_; 
lean_dec_ref(v_a_423_);
v___x_432_ = lean_box(0);
return v___x_432_;
}
}
else
{
lean_object* v___x_433_; 
lean_dec_ref(v_e_422_);
v___x_433_ = lean_box(0);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolValue_x3f(lean_object* v_e_437_){
_start:
{
if (lean_obj_tag(v_e_437_) == 4)
{
lean_object* v_declName_438_; 
v_declName_438_ = lean_ctor_get(v_e_437_, 0);
if (lean_obj_tag(v_declName_438_) == 1)
{
lean_object* v_pre_439_; 
v_pre_439_ = lean_ctor_get(v_declName_438_, 0);
if (lean_obj_tag(v_pre_439_) == 1)
{
lean_object* v_pre_440_; 
v_pre_440_ = lean_ctor_get(v_pre_439_, 0);
if (lean_obj_tag(v_pre_440_) == 0)
{
lean_object* v_us_441_; lean_object* v_str_442_; lean_object* v_str_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_us_441_ = lean_ctor_get(v_e_437_, 1);
v_str_442_ = lean_ctor_get(v_declName_438_, 1);
v_str_443_ = lean_ctor_get(v_pre_439_, 1);
v___x_444_ = ((lean_object*)(l_Lean_Meta_Sym_getBoolValue_x3f___closed__0));
v___x_445_ = lean_string_dec_eq(v_str_443_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
v___x_446_ = lean_box(0);
return v___x_446_;
}
else
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_Meta_Sym_getBoolValue_x3f___closed__1));
v___x_448_ = lean_string_dec_eq(v_str_442_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_Meta_Sym_getBoolValue_x3f___closed__2));
v___x_450_ = lean_string_dec_eq(v_str_442_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
v___x_451_ = lean_box(0);
return v___x_451_;
}
else
{
if (lean_obj_tag(v_us_441_) == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_box(v___x_448_);
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; 
v___x_454_ = lean_box(0);
return v___x_454_;
}
}
}
else
{
if (lean_obj_tag(v_us_441_) == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_box(v___x_448_);
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = lean_box(0);
return v___x_457_;
}
}
}
}
else
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(0);
return v___x_458_;
}
}
else
{
lean_object* v___x_459_; 
v___x_459_ = lean_box(0);
return v___x_459_;
}
}
else
{
lean_object* v___x_460_; 
v___x_460_ = lean_box(0);
return v___x_460_;
}
}
else
{
lean_object* v___x_461_; 
v___x_461_ = lean_box(0);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolValue_x3f___boxed(lean_object* v_e_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_Sym_getBoolValue_x3f(v_e_462_);
lean_dec_ref(v_e_462_);
return v_res_463_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Init_Data_Rat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_LitValues(builtin);
}
#ifdef __cplusplus
}
#endif
