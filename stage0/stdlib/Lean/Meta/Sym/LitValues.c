// Lean compiler output
// Module: Lean.Meta.Sym.LitValues
// Imports: public import Lean.Expr public import Init.Data.Rat import Lean.Util.SafeExponentiation
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
uint8_t l_Lean_isSafeBitVecWidth(lean_object*);
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
lean_object* v_nExpr_163_; lean_object* v_vExpr_164_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = l_Lean_Expr_cleanupAnnotations(v_e_161_);
v___x_183_ = l_Lean_Expr_isApp(v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
lean_dec_ref(v___x_182_);
v___x_184_ = lean_box(0);
return v___x_184_;
}
else
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = l_Lean_Expr_appFnCleanup___redArg(v___x_182_);
v___x_186_ = l_Lean_Expr_isApp(v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_dec_ref(v___x_185_);
lean_dec_ref(v___x_182_);
v___x_187_ = lean_box(0);
return v___x_187_;
}
else
{
lean_object* v_arg_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_arg_188_ = lean_ctor_get(v___x_185_, 1);
lean_inc_ref(v_arg_188_);
v___x_189_ = l_Lean_Expr_appFnCleanup___redArg(v___x_185_);
lean_dec_ref(v___x_185_);
v___x_190_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1));
v___x_191_ = l_Lean_Expr_isConstOf(v___x_189_, v___x_190_);
if (v___x_191_ == 0)
{
uint8_t v___x_192_; 
lean_dec_ref(v___x_182_);
v___x_192_ = l_Lean_Expr_isApp(v___x_189_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
lean_dec_ref(v___x_189_);
lean_dec_ref(v_arg_188_);
v___x_193_ = lean_box(0);
return v___x_193_;
}
else
{
lean_object* v_arg_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_arg_194_ = lean_ctor_get(v___x_189_, 1);
lean_inc_ref(v_arg_194_);
v___x_195_ = l_Lean_Expr_appFnCleanup___redArg(v___x_189_);
lean_dec_ref(v___x_189_);
v___x_196_ = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
v___x_197_ = l_Lean_Expr_isConstOf(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3));
v___x_199_ = l_Lean_Expr_isConstOf(v___x_195_, v___x_198_);
lean_dec_ref(v___x_195_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; 
lean_dec_ref(v_arg_194_);
lean_dec_ref(v_arg_188_);
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
v_nExpr_163_ = v_arg_194_;
v_vExpr_164_ = v_arg_188_;
goto v___jp_162_;
}
}
else
{
lean_object* v___x_201_; uint8_t v___x_202_; 
lean_dec_ref(v___x_195_);
v___x_201_ = l_Lean_Expr_cleanupAnnotations(v_arg_194_);
lean_dec_ref(v_arg_194_);
v___x_202_ = l_Lean_Expr_isApp(v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_dec_ref(v___x_201_);
lean_dec_ref(v_arg_188_);
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_201_);
v___x_205_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4));
v___x_206_ = l_Lean_Expr_isConstOf(v___x_204_, v___x_205_);
lean_dec_ref(v___x_204_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
lean_dec_ref(v___x_201_);
lean_dec_ref(v_arg_188_);
v___x_207_ = lean_box(0);
return v___x_207_;
}
else
{
lean_object* v_arg_208_; lean_object* v___x_209_; 
v_arg_208_ = lean_ctor_get(v___x_201_, 1);
lean_inc_ref(v_arg_208_);
lean_dec_ref(v___x_201_);
v___x_209_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_208_);
lean_dec_ref(v_arg_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_210_; 
lean_dec_ref(v_arg_188_);
v___x_210_ = lean_box(0);
return v___x_210_;
}
else
{
lean_object* v_val_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_226_; 
v_val_211_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_226_ == 0)
{
v___x_213_ = v___x_209_;
v_isShared_214_ = v_isSharedCheck_226_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_val_211_);
lean_dec(v___x_209_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_226_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
uint8_t v___x_215_; 
v___x_215_ = l_Lean_isSafeBitVecWidth(v_val_211_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
lean_del_object(v___x_213_);
lean_dec(v_val_211_);
lean_dec_ref(v_arg_188_);
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
if (lean_obj_tag(v_arg_188_) == 9)
{
lean_object* v_a_217_; 
v_a_217_ = lean_ctor_get(v_arg_188_, 0);
lean_inc_ref(v_a_217_);
lean_dec_ref_known(v_arg_188_, 1);
if (lean_obj_tag(v_a_217_) == 0)
{
lean_object* v_val_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v_val_218_ = lean_ctor_get(v_a_217_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v_a_217_, 1);
v___x_219_ = l_BitVec_ofNat(v_val_211_, v_val_218_);
lean_dec(v_val_218_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v_val_211_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_220_);
v___x_222_ = v___x_213_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
else
{
lean_object* v___x_224_; 
lean_dec_ref(v_a_217_);
lean_del_object(v___x_213_);
lean_dec(v_val_211_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
}
else
{
lean_object* v___x_225_; 
lean_del_object(v___x_213_);
lean_dec(v_val_211_);
lean_dec_ref(v_arg_188_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_arg_227_; 
lean_dec_ref(v___x_189_);
v_arg_227_ = lean_ctor_get(v___x_182_, 1);
lean_inc_ref(v_arg_227_);
lean_dec_ref(v___x_182_);
v_nExpr_163_ = v_arg_188_;
v_vExpr_164_ = v_arg_227_;
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
lean_object* v_val_167_; uint8_t v___x_168_; 
v_val_167_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_val_167_);
lean_dec_ref_known(v___x_165_, 1);
v___x_168_ = l_Lean_isSafeBitVecWidth(v_val_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
lean_dec(v_val_167_);
lean_dec_ref(v_vExpr_164_);
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Meta_Sym_getNatValue_x3f(v_vExpr_164_);
lean_dec_ref(v_vExpr_164_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v___x_171_; 
lean_dec(v_val_167_);
v___x_171_ = lean_box(0);
return v___x_171_;
}
else
{
lean_object* v_val_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_181_; 
v_val_172_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_181_ == 0)
{
v___x_174_ = v___x_170_;
v_isShared_175_ = v_isSharedCheck_181_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_val_172_);
lean_dec(v___x_170_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_181_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_176_ = l_BitVec_ofNat(v_val_167_, v_val_172_);
lean_dec(v_val_172_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_val_167_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_177_);
v___x_179_ = v___x_174_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___boxed(lean_object* v_e_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_e_228_);
lean_dec_ref(v_e_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object* v_e_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; 
v___x_232_ = lean_box(0);
return v___x_232_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_242_; 
v_val_233_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_242_ == 0)
{
v___x_235_ = v___x_231_;
v_isShared_236_ = v_isSharedCheck_242_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_val_233_);
lean_dec(v___x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_242_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_237_ = lean_uint8_of_nat(v_val_233_);
lean_dec(v_val_233_);
v___x_238_ = lean_box(v___x_237_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_238_);
v___x_240_ = v___x_235_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f___boxed(lean_object* v_e_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v_e_243_);
lean_dec_ref(v_e_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object* v_e_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_245_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v___x_247_; 
v___x_247_ = lean_box(0);
return v___x_247_;
}
else
{
lean_object* v_val_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_257_; 
v_val_248_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_257_ == 0)
{
v___x_250_ = v___x_246_;
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_val_248_);
lean_dec(v___x_246_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
uint16_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_252_ = lean_uint16_of_nat(v_val_248_);
lean_dec(v_val_248_);
v___x_253_ = lean_box(v___x_252_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_253_);
v___x_255_ = v___x_250_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f___boxed(lean_object* v_e_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v_e_258_);
lean_dec_ref(v_e_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object* v_e_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_260_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_box(0);
return v___x_262_;
}
else
{
lean_object* v_val_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_272_; 
v_val_263_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_272_ == 0)
{
v___x_265_ = v___x_261_;
v_isShared_266_ = v_isSharedCheck_272_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_val_263_);
lean_dec(v___x_261_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_272_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
uint32_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_267_ = lean_uint32_of_nat(v_val_263_);
lean_dec(v_val_263_);
v___x_268_ = lean_box_uint32(v___x_267_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_268_);
v___x_270_ = v___x_265_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f___boxed(lean_object* v_e_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v_e_273_);
lean_dec_ref(v_e_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object* v_e_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; 
v___x_277_ = lean_box(0);
return v___x_277_;
}
else
{
lean_object* v_val_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_287_; 
v_val_278_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_287_ == 0)
{
v___x_280_ = v___x_276_;
v_isShared_281_ = v_isSharedCheck_287_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_val_278_);
lean_dec(v___x_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_287_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
uint64_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_282_ = lean_uint64_of_nat(v_val_278_);
lean_dec(v_val_278_);
v___x_283_ = lean_box_uint64(v___x_282_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_283_);
v___x_285_ = v___x_280_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f___boxed(lean_object* v_e_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v_e_288_);
lean_dec_ref(v_e_288_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object* v_e_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_290_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v___x_292_; 
v___x_292_ = lean_box(0);
return v___x_292_;
}
else
{
lean_object* v_val_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_302_; 
v_val_293_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_302_ == 0)
{
v___x_295_ = v___x_291_;
v_isShared_296_ = v_isSharedCheck_302_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_val_293_);
lean_dec(v___x_291_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_302_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_297_ = lean_int8_of_int(v_val_293_);
lean_dec(v_val_293_);
v___x_298_ = lean_box(v___x_297_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_298_);
v___x_300_ = v___x_295_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f___boxed(lean_object* v_e_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Sym_getInt8Value_x3f(v_e_303_);
lean_dec_ref(v_e_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object* v_e_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_305_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; 
v___x_307_ = lean_box(0);
return v___x_307_;
}
else
{
lean_object* v_val_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_317_; 
v_val_308_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_317_ == 0)
{
v___x_310_ = v___x_306_;
v_isShared_311_ = v_isSharedCheck_317_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_val_308_);
lean_dec(v___x_306_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_317_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint16_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_312_ = lean_int16_of_int(v_val_308_);
lean_dec(v_val_308_);
v___x_313_ = lean_box(v___x_312_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_313_);
v___x_315_ = v___x_310_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f___boxed(lean_object* v_e_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Meta_Sym_getInt16Value_x3f(v_e_318_);
lean_dec_ref(v_e_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object* v_e_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_320_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_box(0);
return v___x_322_;
}
else
{
lean_object* v_val_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_332_; 
v_val_323_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_332_ == 0)
{
v___x_325_ = v___x_321_;
v_isShared_326_ = v_isSharedCheck_332_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_val_323_);
lean_dec(v___x_321_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_332_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
uint32_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_327_ = lean_int32_of_int(v_val_323_);
lean_dec(v_val_323_);
v___x_328_ = lean_box_uint32(v___x_327_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_328_);
v___x_330_ = v___x_325_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f___boxed(lean_object* v_e_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Meta_Sym_getInt32Value_x3f(v_e_333_);
lean_dec_ref(v_e_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object* v_e_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_335_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v___x_337_; 
v___x_337_ = lean_box(0);
return v___x_337_;
}
else
{
lean_object* v_val_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_347_; 
v_val_338_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_347_ == 0)
{
v___x_340_ = v___x_336_;
v_isShared_341_ = v_isSharedCheck_347_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_val_338_);
lean_dec(v___x_336_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_347_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
uint64_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_342_ = lean_int64_of_int(v_val_338_);
lean_dec(v_val_338_);
v___x_343_ = lean_box_uint64(v___x_342_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_343_);
v___x_345_ = v___x_340_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f___boxed(lean_object* v_e_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Meta_Sym_getInt64Value_x3f(v_e_348_);
lean_dec_ref(v_e_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object* v_e_353_){
_start:
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = l_Lean_Expr_cleanupAnnotations(v_e_353_);
v___x_355_ = l_Lean_Expr_isApp(v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec_ref(v___x_354_);
v___x_356_ = lean_box(0);
return v___x_356_;
}
else
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = l_Lean_Expr_appFnCleanup___redArg(v___x_354_);
lean_dec_ref(v___x_354_);
v___x_358_ = l_Lean_Expr_isApp(v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
lean_dec_ref(v___x_357_);
v___x_359_ = lean_box(0);
return v___x_359_;
}
else
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = l_Lean_Expr_appFnCleanup___redArg(v___x_357_);
v___x_361_ = l_Lean_Expr_isApp(v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec_ref(v___x_360_);
lean_dec_ref(v___x_357_);
v___x_362_ = lean_box(0);
return v___x_362_;
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_363_ = l_Lean_Expr_appFnCleanup___redArg(v___x_360_);
v___x_364_ = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
v___x_365_ = l_Lean_Expr_isConstOf(v___x_363_, v___x_364_);
lean_dec_ref(v___x_363_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec_ref(v___x_360_);
lean_dec_ref(v___x_357_);
v___x_366_ = lean_box(0);
return v___x_366_;
}
else
{
lean_object* v_arg_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_arg_367_ = lean_ctor_get(v___x_360_, 1);
lean_inc_ref(v_arg_367_);
lean_dec_ref(v___x_360_);
v___x_368_ = l_Lean_Expr_cleanupAnnotations(v_arg_367_);
lean_dec_ref(v_arg_367_);
v___x_369_ = l_Lean_Expr_isApp(v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec_ref(v___x_368_);
lean_dec_ref(v___x_357_);
v___x_370_ = lean_box(0);
return v___x_370_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_371_ = l_Lean_Expr_appFnCleanup___redArg(v___x_368_);
v___x_372_ = ((lean_object*)(l_Lean_Meta_Sym_getFinValue_x3f___closed__1));
v___x_373_ = l_Lean_Expr_isConstOf(v___x_371_, v___x_372_);
lean_dec_ref(v___x_371_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec_ref(v___x_368_);
lean_dec_ref(v___x_357_);
v___x_374_ = lean_box(0);
return v___x_374_;
}
else
{
lean_object* v_arg_375_; lean_object* v___x_376_; 
v_arg_375_ = lean_ctor_get(v___x_368_, 1);
lean_inc_ref(v_arg_375_);
lean_dec_ref(v___x_368_);
v___x_376_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_375_);
lean_dec_ref(v_arg_375_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_377_; 
lean_dec_ref(v___x_357_);
v___x_377_ = lean_box(0);
return v___x_377_;
}
else
{
lean_object* v_arg_378_; 
v_arg_378_ = lean_ctor_get(v___x_357_, 1);
lean_inc_ref(v_arg_378_);
lean_dec_ref(v___x_357_);
if (lean_obj_tag(v_arg_378_) == 9)
{
lean_object* v_a_379_; 
v_a_379_ = lean_ctor_get(v_arg_378_, 0);
lean_inc_ref(v_a_379_);
lean_dec_ref_known(v_arg_378_, 1);
if (lean_obj_tag(v_a_379_) == 0)
{
lean_object* v_val_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_393_; 
v_val_380_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_393_ == 0)
{
v___x_382_ = v___x_376_;
v_isShared_383_ = v_isSharedCheck_393_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_val_380_);
lean_dec(v___x_376_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_393_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_val_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v_val_384_ = lean_ctor_get(v_a_379_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v_a_379_, 1);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_nat_dec_eq(v_val_380_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = lean_nat_mod(v_val_384_, v_val_380_);
lean_dec(v_val_384_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_val_380_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_388_);
v___x_390_ = v___x_382_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
else
{
lean_object* v___x_392_; 
lean_dec(v_val_384_);
lean_del_object(v___x_382_);
lean_dec(v_val_380_);
v___x_392_ = lean_box(0);
return v___x_392_;
}
}
}
else
{
lean_object* v___x_394_; 
lean_dec_ref(v_a_379_);
lean_dec_ref_known(v___x_376_, 1);
v___x_394_ = lean_box(0);
return v___x_394_;
}
}
else
{
lean_object* v___x_395_; 
lean_dec_ref_known(v___x_376_, 1);
lean_dec_ref(v_arg_378_);
v___x_395_ = lean_box(0);
return v___x_395_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f___boxed(lean_object* v_e_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Meta_Sym_getFinValue_x3f(v_e_396_);
lean_dec_ref(v_e_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object* v_e_402_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = l_Lean_Expr_cleanupAnnotations(v_e_402_);
v___x_404_ = l_Lean_Expr_isApp(v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_dec_ref(v___x_403_);
v___x_405_ = lean_box(0);
return v___x_405_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_403_);
v___x_407_ = ((lean_object*)(l_Lean_Meta_Sym_getCharValue_x3f___closed__1));
v___x_408_ = l_Lean_Expr_isConstOf(v___x_406_, v___x_407_);
lean_dec_ref(v___x_406_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_dec_ref(v___x_403_);
v___x_409_ = lean_box(0);
return v___x_409_;
}
else
{
lean_object* v_arg_410_; 
v_arg_410_ = lean_ctor_get(v___x_403_, 1);
lean_inc_ref(v_arg_410_);
lean_dec_ref(v___x_403_);
if (lean_obj_tag(v_arg_410_) == 9)
{
lean_object* v_a_411_; 
v_a_411_ = lean_ctor_get(v_arg_410_, 0);
lean_inc_ref(v_a_411_);
lean_dec_ref_known(v_arg_410_, 1);
if (lean_obj_tag(v_a_411_) == 0)
{
lean_object* v_val_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_421_; 
v_val_412_ = lean_ctor_get(v_a_411_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_a_411_);
if (v_isSharedCheck_421_ == 0)
{
v___x_414_ = v_a_411_;
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_val_412_);
lean_dec(v_a_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint32_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_416_ = l_Char_ofNat(v_val_412_);
lean_dec(v_val_412_);
v___x_417_ = lean_box_uint32(v___x_416_);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 1);
lean_ctor_set(v___x_414_, 0, v___x_417_);
v___x_419_ = v___x_414_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_object* v___x_422_; 
lean_dec_ref(v_a_411_);
v___x_422_ = lean_box(0);
return v___x_422_;
}
}
else
{
lean_object* v___x_423_; 
lean_dec_ref(v_arg_410_);
v___x_423_ = lean_box(0);
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f___boxed(lean_object* v_e_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_Sym_getCharValue_x3f(v_e_424_);
lean_dec_ref(v_e_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object* v_e_426_){
_start:
{
if (lean_obj_tag(v_e_426_) == 9)
{
lean_object* v_a_427_; 
v_a_427_ = lean_ctor_get(v_e_426_, 0);
lean_inc_ref(v_a_427_);
lean_dec_ref_known(v_e_426_, 1);
if (lean_obj_tag(v_a_427_) == 1)
{
lean_object* v_val_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_val_428_ = lean_ctor_get(v_a_427_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v_a_427_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_val_428_);
lean_dec(v_a_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_val_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
else
{
lean_object* v___x_436_; 
lean_dec_ref(v_a_427_);
v___x_436_ = lean_box(0);
return v___x_436_;
}
}
else
{
lean_object* v___x_437_; 
lean_dec_ref(v_e_426_);
v___x_437_ = lean_box(0);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolValue_x3f(lean_object* v_e_441_){
_start:
{
if (lean_obj_tag(v_e_441_) == 4)
{
lean_object* v_declName_442_; 
v_declName_442_ = lean_ctor_get(v_e_441_, 0);
if (lean_obj_tag(v_declName_442_) == 1)
{
lean_object* v_pre_443_; 
v_pre_443_ = lean_ctor_get(v_declName_442_, 0);
if (lean_obj_tag(v_pre_443_) == 1)
{
lean_object* v_pre_444_; 
v_pre_444_ = lean_ctor_get(v_pre_443_, 0);
if (lean_obj_tag(v_pre_444_) == 0)
{
lean_object* v_us_445_; lean_object* v_str_446_; lean_object* v_str_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_us_445_ = lean_ctor_get(v_e_441_, 1);
v_str_446_ = lean_ctor_get(v_declName_442_, 1);
v_str_447_ = lean_ctor_get(v_pre_443_, 1);
v___x_448_ = ((lean_object*)(l_Lean_Meta_Sym_getBoolValue_x3f___closed__0));
v___x_449_ = lean_string_dec_eq(v_str_447_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_box(0);
return v___x_450_;
}
else
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = ((lean_object*)(l_Lean_Meta_Sym_getBoolValue_x3f___closed__1));
v___x_452_ = lean_string_dec_eq(v_str_446_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lean_Meta_Sym_getBoolValue_x3f___closed__2));
v___x_454_ = lean_string_dec_eq(v_str_446_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_box(0);
return v___x_455_;
}
else
{
if (lean_obj_tag(v_us_445_) == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_box(v___x_452_);
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(0);
return v___x_458_;
}
}
}
else
{
if (lean_obj_tag(v_us_445_) == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_box(v___x_452_);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = lean_box(0);
return v___x_461_;
}
}
}
}
else
{
lean_object* v___x_462_; 
v___x_462_ = lean_box(0);
return v___x_462_;
}
}
else
{
lean_object* v___x_463_; 
v___x_463_ = lean_box(0);
return v___x_463_;
}
}
else
{
lean_object* v___x_464_; 
v___x_464_ = lean_box(0);
return v___x_464_;
}
}
else
{
lean_object* v___x_465_; 
v___x_465_ = lean_box(0);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolValue_x3f___boxed(lean_object* v_e_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_Sym_getBoolValue_x3f(v_e_466_);
lean_dec_ref(v_e_466_);
return v_res_467_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
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
res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
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
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
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
res = initialize_Lean_Util_SafeExponentiation(builtin);
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
