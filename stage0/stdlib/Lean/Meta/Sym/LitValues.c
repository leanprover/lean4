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
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getIntValue_x3f_spec__0(lean_object* v_a_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_nat_to_int(v_a_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object* v_e_41_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = l_Lean_Expr_cleanupAnnotations(v_e_41_);
v___x_55_ = l_Lean_Expr_isApp(v___x_54_);
if (v___x_55_ == 0)
{
lean_dec_ref(v___x_54_);
goto v___jp_42_;
}
else
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = l_Lean_Expr_appFnCleanup___redArg(v___x_54_);
v___x_57_ = l_Lean_Expr_isApp(v___x_56_);
if (v___x_57_ == 0)
{
lean_dec_ref(v___x_56_);
lean_dec_ref(v___x_54_);
goto v___jp_42_;
}
else
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = l_Lean_Expr_appFnCleanup___redArg(v___x_56_);
lean_dec_ref(v___x_56_);
v___x_59_ = l_Lean_Expr_isApp(v___x_58_);
if (v___x_59_ == 0)
{
lean_dec_ref(v___x_58_);
lean_dec_ref(v___x_54_);
goto v___jp_42_;
}
else
{
lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_60_ = l_Lean_Expr_appFnCleanup___redArg(v___x_58_);
lean_dec_ref(v___x_58_);
v___x_61_ = ((lean_object*)(l_Lean_Meta_Sym_getIntValue_x3f___closed__2));
v___x_62_ = l_Lean_Expr_isConstOf(v___x_60_, v___x_61_);
lean_dec_ref(v___x_60_);
if (v___x_62_ == 0)
{
lean_dec_ref(v___x_54_);
goto v___jp_42_;
}
else
{
lean_object* v_arg_63_; lean_object* v___x_64_; 
v_arg_63_ = lean_ctor_get(v___x_54_, 1);
lean_inc_ref(v_arg_63_);
lean_dec_ref(v___x_54_);
v___x_64_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_63_);
lean_dec_ref(v_arg_63_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(0);
return v___x_65_;
}
else
{
lean_object* v_val_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_75_; 
v_val_66_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_75_ == 0)
{
v___x_68_ = v___x_64_;
v_isShared_69_ = v_isSharedCheck_75_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_val_66_);
lean_dec(v___x_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_75_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_70_ = lean_nat_to_int(v_val_66_);
v___x_71_ = lean_int_neg(v___x_70_);
lean_dec(v___x_70_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_71_);
v___x_73_ = v___x_68_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
}
}
v___jp_42_:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_41_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
else
{
lean_object* v_val_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_53_; 
v_val_45_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_53_ == 0)
{
v___x_47_ = v___x_43_;
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_val_45_);
lean_dec(v___x_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_51_; 
v___x_49_ = lean_nat_to_int(v_val_45_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v___x_49_);
v___x_51_ = v___x_47_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_49_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f___boxed(lean_object* v_e_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_76_);
lean_dec_ref(v_e_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__0(lean_object* v_a_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Rat_ofInt(v_a_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(lean_object* v_a_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_nat_to_int(v_a_80_);
v___x_82_ = l_Rat_ofInt(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f(lean_object* v_e_88_){
_start:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = l_Lean_Expr_cleanupAnnotations(v_e_88_);
v___x_102_ = l_Lean_Expr_isApp(v___x_101_);
if (v___x_102_ == 0)
{
lean_dec_ref(v___x_101_);
goto v___jp_89_;
}
else
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = l_Lean_Expr_appFnCleanup___redArg(v___x_101_);
v___x_104_ = l_Lean_Expr_isApp(v___x_103_);
if (v___x_104_ == 0)
{
lean_dec_ref(v___x_103_);
lean_dec_ref(v___x_101_);
goto v___jp_89_;
}
else
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_103_);
v___x_106_ = l_Lean_Expr_isApp(v___x_105_);
if (v___x_106_ == 0)
{
lean_dec_ref(v___x_105_);
lean_dec_ref(v___x_103_);
lean_dec_ref(v___x_101_);
goto v___jp_89_;
}
else
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_105_);
lean_dec_ref(v___x_105_);
v___x_108_ = l_Lean_Expr_isApp(v___x_107_);
if (v___x_108_ == 0)
{
lean_dec_ref(v___x_107_);
lean_dec_ref(v___x_103_);
lean_dec_ref(v___x_101_);
goto v___jp_89_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_107_);
lean_dec_ref(v___x_107_);
v___x_110_ = l_Lean_Expr_isApp(v___x_109_);
if (v___x_110_ == 0)
{
lean_dec_ref(v___x_109_);
lean_dec_ref(v___x_103_);
lean_dec_ref(v___x_101_);
goto v___jp_89_;
}
else
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = l_Lean_Expr_appFnCleanup___redArg(v___x_109_);
lean_dec_ref(v___x_109_);
v___x_112_ = l_Lean_Expr_isApp(v___x_111_);
if (v___x_112_ == 0)
{
lean_dec_ref(v___x_111_);
lean_dec_ref(v___x_103_);
lean_dec_ref(v___x_101_);
goto v___jp_89_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_111_);
lean_dec_ref(v___x_111_);
v___x_114_ = ((lean_object*)(l_Lean_Meta_Sym_getRatValue_x3f___closed__2));
v___x_115_ = l_Lean_Expr_isConstOf(v___x_113_, v___x_114_);
lean_dec_ref(v___x_113_);
if (v___x_115_ == 0)
{
lean_dec_ref(v___x_103_);
lean_dec_ref(v___x_101_);
goto v___jp_89_;
}
else
{
lean_object* v_arg_116_; lean_object* v___x_117_; 
v_arg_116_ = lean_ctor_get(v___x_103_, 1);
lean_inc_ref(v_arg_116_);
lean_dec_ref(v___x_103_);
v___x_117_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_116_);
lean_dec_ref(v_arg_116_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v___x_118_; 
lean_dec_ref(v___x_101_);
v___x_118_ = lean_box(0);
return v___x_118_;
}
else
{
lean_object* v_val_119_; lean_object* v_arg_120_; lean_object* v___x_121_; 
v_val_119_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_val_119_);
lean_dec_ref_known(v___x_117_, 1);
v_arg_120_ = lean_ctor_get(v___x_101_, 1);
lean_inc_ref(v_arg_120_);
lean_dec_ref(v___x_101_);
v___x_121_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_120_);
lean_dec_ref(v_arg_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v___x_122_; 
lean_dec(v_val_119_);
v___x_122_ = lean_box(0);
return v___x_122_;
}
else
{
lean_object* v_val_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_133_; 
v_val_123_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_133_ == 0)
{
v___x_125_ = v___x_121_;
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_val_123_);
lean_dec(v___x_121_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_127_ = l_Rat_ofInt(v_val_119_);
v___x_128_ = l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(v_val_123_);
v___x_129_ = l_Rat_div(v___x_127_, v___x_128_);
lean_dec_ref(v___x_127_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_129_);
v___x_131_ = v___x_125_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
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
v___jp_89_:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_88_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
lean_object* v_val_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_val_92_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_100_ == 0)
{
v___x_94_ = v___x_90_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_val_92_);
lean_dec(v___x_90_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = l_Rat_ofInt(v_val_92_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_96_);
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f___boxed(lean_object* v_e_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Meta_Sym_getRatValue_x3f(v_e_134_);
lean_dec_ref(v_e_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object* v_e_146_){
_start:
{
lean_object* v_nExpr_148_; lean_object* v_vExpr_149_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = l_Lean_Expr_cleanupAnnotations(v_e_146_);
v___x_166_ = l_Lean_Expr_isApp(v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
lean_dec_ref(v___x_165_);
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = l_Lean_Expr_appFnCleanup___redArg(v___x_165_);
v___x_169_ = l_Lean_Expr_isApp(v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_dec_ref(v___x_168_);
lean_dec_ref(v___x_165_);
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
lean_object* v_arg_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_arg_171_ = lean_ctor_get(v___x_168_, 1);
lean_inc_ref(v_arg_171_);
v___x_172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_168_);
lean_dec_ref(v___x_168_);
v___x_173_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1));
v___x_174_ = l_Lean_Expr_isConstOf(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
uint8_t v___x_175_; 
lean_dec_ref(v___x_165_);
v___x_175_ = l_Lean_Expr_isApp(v___x_172_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
lean_dec_ref(v___x_172_);
lean_dec_ref(v_arg_171_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v_arg_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_arg_177_ = lean_ctor_get(v___x_172_, 1);
lean_inc_ref(v_arg_177_);
v___x_178_ = l_Lean_Expr_appFnCleanup___redArg(v___x_172_);
lean_dec_ref(v___x_172_);
v___x_179_ = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
v___x_180_ = l_Lean_Expr_isConstOf(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3));
v___x_182_ = l_Lean_Expr_isConstOf(v___x_178_, v___x_181_);
lean_dec_ref(v___x_178_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
lean_dec_ref(v_arg_177_);
lean_dec_ref(v_arg_171_);
v___x_183_ = lean_box(0);
return v___x_183_;
}
else
{
v_nExpr_148_ = v_arg_177_;
v_vExpr_149_ = v_arg_171_;
goto v___jp_147_;
}
}
else
{
lean_object* v___x_184_; uint8_t v___x_185_; 
lean_dec_ref(v___x_178_);
v___x_184_ = l_Lean_Expr_cleanupAnnotations(v_arg_177_);
lean_dec_ref(v_arg_177_);
v___x_185_ = l_Lean_Expr_isApp(v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
lean_dec_ref(v___x_184_);
lean_dec_ref(v_arg_171_);
v___x_186_ = lean_box(0);
return v___x_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_187_ = l_Lean_Expr_appFnCleanup___redArg(v___x_184_);
v___x_188_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4));
v___x_189_ = l_Lean_Expr_isConstOf(v___x_187_, v___x_188_);
lean_dec_ref(v___x_187_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
lean_dec_ref(v___x_184_);
lean_dec_ref(v_arg_171_);
v___x_190_ = lean_box(0);
return v___x_190_;
}
else
{
lean_object* v_arg_191_; lean_object* v___x_192_; 
v_arg_191_ = lean_ctor_get(v___x_184_, 1);
lean_inc_ref(v_arg_191_);
lean_dec_ref(v___x_184_);
v___x_192_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_191_);
lean_dec_ref(v_arg_191_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v___x_193_; 
lean_dec_ref(v_arg_171_);
v___x_193_ = lean_box(0);
return v___x_193_;
}
else
{
if (lean_obj_tag(v_arg_171_) == 9)
{
lean_object* v_a_194_; 
v_a_194_ = lean_ctor_get(v_arg_171_, 0);
lean_inc_ref(v_a_194_);
lean_dec_ref_known(v_arg_171_, 1);
if (lean_obj_tag(v_a_194_) == 0)
{
lean_object* v_val_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_205_; 
v_val_195_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_205_ == 0)
{
v___x_197_ = v___x_192_;
v_isShared_198_ = v_isSharedCheck_205_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_val_195_);
lean_dec(v___x_192_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_205_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v_val_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v_val_199_ = lean_ctor_get(v_a_194_, 0);
lean_inc(v_val_199_);
lean_dec_ref_known(v_a_194_, 1);
v___x_200_ = l_BitVec_ofNat(v_val_195_, v_val_199_);
lean_dec(v_val_199_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v_val_195_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_201_);
v___x_203_ = v___x_197_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
lean_object* v___x_206_; 
lean_dec_ref(v_a_194_);
lean_dec_ref_known(v___x_192_, 1);
v___x_206_ = lean_box(0);
return v___x_206_;
}
}
else
{
lean_object* v___x_207_; 
lean_dec_ref_known(v___x_192_, 1);
lean_dec_ref(v_arg_171_);
v___x_207_ = lean_box(0);
return v___x_207_;
}
}
}
}
}
}
}
else
{
lean_object* v_arg_208_; 
lean_dec_ref(v___x_172_);
v_arg_208_ = lean_ctor_get(v___x_165_, 1);
lean_inc_ref(v_arg_208_);
lean_dec_ref(v___x_165_);
v_nExpr_148_ = v_arg_171_;
v_vExpr_149_ = v_arg_208_;
goto v___jp_147_;
}
}
}
v___jp_147_:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_Sym_getNatValue_x3f(v_nExpr_148_);
lean_dec_ref(v_nExpr_148_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v___x_151_; 
lean_dec_ref(v_vExpr_149_);
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
lean_object* v_val_152_; lean_object* v___x_153_; 
v_val_152_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v___x_150_, 1);
v___x_153_ = l_Lean_Meta_Sym_getNatValue_x3f(v_vExpr_149_);
lean_dec_ref(v_vExpr_149_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v___x_154_; 
lean_dec(v_val_152_);
v___x_154_ = lean_box(0);
return v___x_154_;
}
else
{
lean_object* v_val_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_164_; 
v_val_155_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_164_ == 0)
{
v___x_157_ = v___x_153_;
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_val_155_);
lean_dec(v___x_153_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_159_ = l_BitVec_ofNat(v_val_152_, v_val_155_);
lean_dec(v_val_155_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v_val_152_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_160_);
v___x_162_ = v___x_157_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___boxed(lean_object* v_e_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_e_209_);
lean_dec_ref(v_e_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object* v_e_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_211_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_box(0);
return v___x_213_;
}
else
{
lean_object* v_val_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_223_; 
v_val_214_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_223_ == 0)
{
v___x_216_ = v___x_212_;
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_val_214_);
lean_dec(v___x_212_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_218_ = lean_uint8_of_nat(v_val_214_);
lean_dec(v_val_214_);
v___x_219_ = lean_box(v___x_218_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_219_);
v___x_221_ = v___x_216_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f___boxed(lean_object* v_e_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v_e_224_);
lean_dec_ref(v_e_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object* v_e_226_){
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
uint16_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_233_ = lean_uint16_of_nat(v_val_229_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f___boxed(lean_object* v_e_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v_e_239_);
lean_dec_ref(v_e_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object* v_e_241_){
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
uint32_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_248_ = lean_uint32_of_nat(v_val_244_);
lean_dec(v_val_244_);
v___x_249_ = lean_box_uint32(v___x_248_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f___boxed(lean_object* v_e_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v_e_254_);
lean_dec_ref(v_e_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object* v_e_256_){
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
uint64_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_263_ = lean_uint64_of_nat(v_val_259_);
lean_dec(v_val_259_);
v___x_264_ = lean_box_uint64(v___x_263_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f___boxed(lean_object* v_e_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v_e_269_);
lean_dec_ref(v_e_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object* v_e_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_271_);
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
uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_278_ = lean_int8_of_int(v_val_274_);
lean_dec(v_val_274_);
v___x_279_ = lean_box(v___x_278_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f___boxed(lean_object* v_e_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Meta_Sym_getInt8Value_x3f(v_e_284_);
lean_dec_ref(v_e_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object* v_e_286_){
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
uint16_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_293_ = lean_int16_of_int(v_val_289_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f___boxed(lean_object* v_e_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_Sym_getInt16Value_x3f(v_e_299_);
lean_dec_ref(v_e_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object* v_e_301_){
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
uint32_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_308_ = lean_int32_of_int(v_val_304_);
lean_dec(v_val_304_);
v___x_309_ = lean_box_uint32(v___x_308_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f___boxed(lean_object* v_e_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Meta_Sym_getInt32Value_x3f(v_e_314_);
lean_dec_ref(v_e_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object* v_e_316_){
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
uint64_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_323_ = lean_int64_of_int(v_val_319_);
lean_dec(v_val_319_);
v___x_324_ = lean_box_uint64(v___x_323_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f___boxed(lean_object* v_e_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Meta_Sym_getInt64Value_x3f(v_e_329_);
lean_dec_ref(v_e_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object* v_e_334_){
_start:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = l_Lean_Expr_cleanupAnnotations(v_e_334_);
v___x_336_ = l_Lean_Expr_isApp(v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
lean_dec_ref(v___x_335_);
v___x_337_ = lean_box(0);
return v___x_337_;
}
else
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_335_);
lean_dec_ref(v___x_335_);
v___x_339_ = l_Lean_Expr_isApp(v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
lean_dec_ref(v___x_338_);
v___x_340_ = lean_box(0);
return v___x_340_;
}
else
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_338_);
v___x_342_ = l_Lean_Expr_isApp(v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec_ref(v___x_341_);
lean_dec_ref(v___x_338_);
v___x_343_ = lean_box(0);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_341_);
v___x_345_ = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
v___x_346_ = l_Lean_Expr_isConstOf(v___x_344_, v___x_345_);
lean_dec_ref(v___x_344_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_dec_ref(v___x_341_);
lean_dec_ref(v___x_338_);
v___x_347_ = lean_box(0);
return v___x_347_;
}
else
{
lean_object* v_arg_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_arg_348_ = lean_ctor_get(v___x_341_, 1);
lean_inc_ref(v_arg_348_);
lean_dec_ref(v___x_341_);
v___x_349_ = l_Lean_Expr_cleanupAnnotations(v_arg_348_);
lean_dec_ref(v_arg_348_);
v___x_350_ = l_Lean_Expr_isApp(v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; 
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_338_);
v___x_351_ = lean_box(0);
return v___x_351_;
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_352_ = l_Lean_Expr_appFnCleanup___redArg(v___x_349_);
v___x_353_ = ((lean_object*)(l_Lean_Meta_Sym_getFinValue_x3f___closed__1));
v___x_354_ = l_Lean_Expr_isConstOf(v___x_352_, v___x_353_);
lean_dec_ref(v___x_352_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_338_);
v___x_355_ = lean_box(0);
return v___x_355_;
}
else
{
lean_object* v_arg_356_; lean_object* v___x_357_; 
v_arg_356_ = lean_ctor_get(v___x_349_, 1);
lean_inc_ref(v_arg_356_);
lean_dec_ref(v___x_349_);
v___x_357_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_356_);
lean_dec_ref(v_arg_356_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v___x_358_; 
lean_dec_ref(v___x_338_);
v___x_358_ = lean_box(0);
return v___x_358_;
}
else
{
lean_object* v_arg_359_; 
v_arg_359_ = lean_ctor_get(v___x_338_, 1);
lean_inc_ref(v_arg_359_);
lean_dec_ref(v___x_338_);
if (lean_obj_tag(v_arg_359_) == 9)
{
lean_object* v_a_360_; 
v_a_360_ = lean_ctor_get(v_arg_359_, 0);
lean_inc_ref(v_a_360_);
lean_dec_ref_known(v_arg_359_, 1);
if (lean_obj_tag(v_a_360_) == 0)
{
lean_object* v_val_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_374_; 
v_val_361_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_374_ == 0)
{
v___x_363_ = v___x_357_;
v_isShared_364_ = v_isSharedCheck_374_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_val_361_);
lean_dec(v___x_357_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_374_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v_val_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_val_365_ = lean_ctor_get(v_a_360_, 0);
lean_inc(v_val_365_);
lean_dec_ref_known(v_a_360_, 1);
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_nat_dec_eq(v_val_361_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_368_ = lean_nat_mod(v_val_365_, v_val_361_);
lean_dec(v_val_365_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_val_361_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_369_);
v___x_371_ = v___x_363_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
else
{
lean_object* v___x_373_; 
lean_dec(v_val_365_);
lean_del_object(v___x_363_);
lean_dec(v_val_361_);
v___x_373_ = lean_box(0);
return v___x_373_;
}
}
}
else
{
lean_object* v___x_375_; 
lean_dec_ref(v_a_360_);
lean_dec_ref_known(v___x_357_, 1);
v___x_375_ = lean_box(0);
return v___x_375_;
}
}
else
{
lean_object* v___x_376_; 
lean_dec_ref_known(v___x_357_, 1);
lean_dec_ref(v_arg_359_);
v___x_376_ = lean_box(0);
return v___x_376_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f___boxed(lean_object* v_e_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_Sym_getFinValue_x3f(v_e_377_);
lean_dec_ref(v_e_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object* v_e_383_){
_start:
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = l_Lean_Expr_cleanupAnnotations(v_e_383_);
v___x_385_ = l_Lean_Expr_isApp(v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec_ref(v___x_384_);
v___x_386_ = lean_box(0);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_387_ = l_Lean_Expr_appFnCleanup___redArg(v___x_384_);
v___x_388_ = ((lean_object*)(l_Lean_Meta_Sym_getCharValue_x3f___closed__1));
v___x_389_ = l_Lean_Expr_isConstOf(v___x_387_, v___x_388_);
lean_dec_ref(v___x_387_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
lean_dec_ref(v___x_384_);
v___x_390_ = lean_box(0);
return v___x_390_;
}
else
{
lean_object* v_arg_391_; 
v_arg_391_ = lean_ctor_get(v___x_384_, 1);
lean_inc_ref(v_arg_391_);
lean_dec_ref(v___x_384_);
if (lean_obj_tag(v_arg_391_) == 9)
{
lean_object* v_a_392_; 
v_a_392_ = lean_ctor_get(v_arg_391_, 0);
lean_inc_ref(v_a_392_);
lean_dec_ref_known(v_arg_391_, 1);
if (lean_obj_tag(v_a_392_) == 0)
{
lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_402_; 
v_val_393_ = lean_ctor_get(v_a_392_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_a_392_);
if (v_isSharedCheck_402_ == 0)
{
v___x_395_ = v_a_392_;
v_isShared_396_ = v_isSharedCheck_402_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_dec(v_a_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_402_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
uint32_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_397_ = l_Char_ofNat(v_val_393_);
lean_dec(v_val_393_);
v___x_398_ = lean_box_uint32(v___x_397_);
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 1);
lean_ctor_set(v___x_395_, 0, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_object* v___x_403_; 
lean_dec_ref(v_a_392_);
v___x_403_ = lean_box(0);
return v___x_403_;
}
}
else
{
lean_object* v___x_404_; 
lean_dec_ref(v_arg_391_);
v___x_404_ = lean_box(0);
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f___boxed(lean_object* v_e_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Meta_Sym_getCharValue_x3f(v_e_405_);
lean_dec_ref(v_e_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object* v_e_407_){
_start:
{
if (lean_obj_tag(v_e_407_) == 9)
{
lean_object* v_a_408_; 
v_a_408_ = lean_ctor_get(v_e_407_, 0);
lean_inc_ref(v_a_408_);
lean_dec_ref_known(v_e_407_, 1);
if (lean_obj_tag(v_a_408_) == 1)
{
lean_object* v_val_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
v_val_409_ = lean_ctor_get(v_a_408_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v_a_408_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v_a_408_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_val_409_);
lean_dec(v_a_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_val_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
else
{
lean_object* v___x_417_; 
lean_dec_ref(v_a_408_);
v___x_417_ = lean_box(0);
return v___x_417_;
}
}
else
{
lean_object* v___x_418_; 
lean_dec_ref(v_e_407_);
v___x_418_ = lean_box(0);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolValue_x3f(lean_object* v_e_422_){
_start:
{
if (lean_obj_tag(v_e_422_) == 4)
{
lean_object* v_declName_423_; 
v_declName_423_ = lean_ctor_get(v_e_422_, 0);
if (lean_obj_tag(v_declName_423_) == 1)
{
lean_object* v_pre_424_; 
v_pre_424_ = lean_ctor_get(v_declName_423_, 0);
if (lean_obj_tag(v_pre_424_) == 1)
{
lean_object* v_pre_425_; 
v_pre_425_ = lean_ctor_get(v_pre_424_, 0);
if (lean_obj_tag(v_pre_425_) == 0)
{
lean_object* v_us_426_; lean_object* v_str_427_; lean_object* v_str_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_us_426_ = lean_ctor_get(v_e_422_, 1);
v_str_427_ = lean_ctor_get(v_declName_423_, 1);
v_str_428_ = lean_ctor_get(v_pre_424_, 1);
v___x_429_ = ((lean_object*)(l_Lean_Meta_Sym_getBoolValue_x3f___closed__0));
v___x_430_ = lean_string_dec_eq(v_str_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_box(0);
return v___x_431_;
}
else
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Meta_Sym_getBoolValue_x3f___closed__1));
v___x_433_ = lean_string_dec_eq(v_str_427_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Meta_Sym_getBoolValue_x3f___closed__2));
v___x_435_ = lean_string_dec_eq(v_str_427_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_box(0);
return v___x_436_;
}
else
{
if (lean_obj_tag(v_us_426_) == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_box(v___x_433_);
v___x_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; 
v___x_439_ = lean_box(0);
return v___x_439_;
}
}
}
else
{
if (lean_obj_tag(v_us_426_) == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_box(v___x_433_);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
else
{
lean_object* v___x_442_; 
v___x_442_ = lean_box(0);
return v___x_442_;
}
}
}
}
else
{
lean_object* v___x_443_; 
v___x_443_ = lean_box(0);
return v___x_443_;
}
}
else
{
lean_object* v___x_444_; 
v___x_444_ = lean_box(0);
return v___x_444_;
}
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_box(0);
return v___x_445_;
}
}
else
{
lean_object* v___x_446_; 
v___x_446_ = lean_box(0);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolValue_x3f___boxed(lean_object* v_e_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Meta_Sym_getBoolValue_x3f(v_e_447_);
lean_dec_ref(v_e_447_);
return v_res_448_;
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
