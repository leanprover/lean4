// Lean compiler output
// Module: Lean.Meta.LitValues
// Imports: public import Lean.Meta.Basic import Init.While
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Rat_neg(lean_object*);
uint64_t lean_int64_of_nat(lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Rat_ofScientific(lean_object*, uint8_t, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
uint32_t lean_int32_of_int(lean_object*);
float lean_float32_of_nat(lean_object*);
float l_Float32_ofScientific(lean_object*, uint8_t, lean_object*);
float lean_float32_negate(float);
uint32_t lean_float32_to_bits(float);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
double lean_float_of_nat(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_negate(double);
uint64_t lean_float_to_bits(double);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint16_to_nat(uint16_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_int8_of_int(lean_object*);
uint8_t lean_int8_of_nat(lean_object*);
uint8_t lean_int8_dec_le(uint8_t, uint8_t);
lean_object* lean_int8_to_int(uint8_t);
lean_object* l_Lean_instToExprInt8_mkNat(lean_object*);
uint16_t lean_int16_of_int(lean_object*);
uint16_t lean_int16_of_nat(lean_object*);
uint8_t lean_int16_dec_le(uint16_t, uint16_t);
lean_object* lean_int16_to_int(uint16_t);
lean_object* l_Lean_instToExprInt16_mkNat(lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
uint8_t lean_int32_dec_le(uint32_t, uint32_t);
lean_object* lean_int32_to_int(uint32_t);
lean_object* l_Lean_instToExprInt32_mkNat(lean_object*);
uint64_t lean_int64_of_int(lean_object*);
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
lean_object* lean_int64_to_int_sint(uint64_t);
lean_object* l_Lean_instToExprInt64_mkNat(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getRawNatValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getRawNatValue_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_getOfNatValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_getOfNatValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getOfNatValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_getOfNatValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_getOfNatValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getOfNatValue_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_getOfNatValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getOfNatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_getOfNatValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getOfNatValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_getOfNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_getOfNatValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_getOfNatValue_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getNatValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_getNatValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getNatValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getNatValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getNatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_getNatValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getNatValue_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getNatValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isNatValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isNatValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isNonZeroNatValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isNonZeroNatValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_getIntValue_x3f_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_getIntValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_getIntValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getIntValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_getIntValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_getIntValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_getIntValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_getIntValue_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_getIntValue_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_getIntValue_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_getIntValue_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_getIntValue_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getIntValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isIntValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isIntValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rat"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "OfScientific"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ofScientific"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 219, 72, 84, 44, 38, 226, 47)}};
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 32, 126, 239, 82, 155, 222, 105)}};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getRatValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_Meta_getRatValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getRatValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_getRatValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_Meta_getRatValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getRatValue_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_getRatValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getRatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_Meta_getRatValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getRatValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_getRatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_Meta_getRatValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_getRatValue_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getRatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getRatValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getCharValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Lean_Meta_getCharValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getCharValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getCharValue_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getCharValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_getCharValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getCharValue_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_getOfNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_Meta_getCharValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getCharValue_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getStringValue_x3f(lean_object*);
static const lean_string_object l_Lean_Meta_getFinValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_getFinValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getFinValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getFinValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getFinValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l_Lean_Meta_getFinValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getFinValue_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getBitVecValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_getBitVecValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getBitVecValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getBitVecValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Meta_getBitVecValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getBitVecValue_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_getBitVecValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_getBitVecValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getBitVecValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_getOfNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_getBitVecValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_getBitVecValue_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_getBitVecValue_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ofNatLT"};
static const lean_object* l_Lean_Meta_getBitVecValue_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_getBitVecValue_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_getBitVecValue_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_getBitVecValue_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getBitVecValue_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_getBitVecValue_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 44, 243, 4, 118, 78, 150, 28)}};
static const lean_object* l_Lean_Meta_getBitVecValue_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_getBitVecValue_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_getLitValueModulus_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__0;
static lean_once_cell_t l_Lean_Meta_getLitValueModulus_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__1;
static lean_once_cell_t l_Lean_Meta_getLitValueModulus_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__2;
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(65536) << 1) | 1))}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1))}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__4_value;
static const lean_string_object l_Lean_Meta_getLitValueModulus_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__5_value;
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__6_value;
static const lean_string_object l_Lean_Meta_getLitValueModulus_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_getLitValueModulus_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__10_value;
static const lean_string_object l_Lean_Meta_getLitValueModulus_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__11_value;
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__12_value;
static const lean_string_object l_Lean_Meta_getLitValueModulus_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__13_value;
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__14_value;
static const lean_string_object l_Lean_Meta_getLitValueModulus_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__15_value;
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__16_value;
static const lean_string_object l_Lean_Meta_getLitValueModulus_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__17_value;
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__18_value;
static const lean_string_object l_Lean_Meta_getLitValueModulus_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__19_value;
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__20 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__20_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getLitValueModulus_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLitValueModulus_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInt8Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInt8Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInt16Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInt16Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInt32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInt32Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInt64Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInt64Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 69, 114, 85, 163, 177, 220, 67)}};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 232, 182, 48, 64, 193, 160, 231)}};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_floatLitValuesEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_floatLitValuesEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__0;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__1;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__2;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__3;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__4;
static const lean_string_object l_Lean_Meta_normLitValue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_normLitValue___closed__5 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__5_value;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__5_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__6 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__6_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__7;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__8;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__9;
static const lean_string_object l_Lean_Meta_normLitValue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l_Lean_Meta_normLitValue___closed__10 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__10_value;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getFinValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__10_value),LEAN_SCALAR_PTR_LITERAL(92, 84, 52, 176, 228, 163, 228, 83)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__11 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__11_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__12;
static const lean_string_object l_Lean_Meta_normLitValue___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNeZeroSucc"};
static const lean_object* l_Lean_Meta_normLitValue___closed__13 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__13_value;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getNatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__13_value),LEAN_SCALAR_PTR_LITERAL(163, 205, 35, 215, 215, 220, 7, 150)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__14 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__14_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__15;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__16;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__17;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__18;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__10_value),LEAN_SCALAR_PTR_LITERAL(106, 22, 191, 22, 91, 53, 63, 20)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__19 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__19_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__20;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__21;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__10_value),LEAN_SCALAR_PTR_LITERAL(100, 85, 82, 103, 43, 170, 82, 231)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__22 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__22_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__23;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__24;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__10_value),LEAN_SCALAR_PTR_LITERAL(112, 78, 205, 187, 174, 188, 116, 224)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__25 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__25_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__26;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__27;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__10_value),LEAN_SCALAR_PTR_LITERAL(8, 204, 85, 89, 36, 115, 101, 7)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__28 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__28_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__29;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Meta_normLitValue___closed__30;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__31;
static const lean_string_object l_Lean_Meta_normLitValue___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instNeg"};
static const lean_object* l_Lean_Meta_normLitValue___closed__32 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__32_value;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__32_value),LEAN_SCALAR_PTR_LITERAL(50, 136, 113, 74, 244, 2, 252, 64)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__33 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__33_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__34;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_Meta_normLitValue___closed__35;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__36;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__37_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__32_value),LEAN_SCALAR_PTR_LITERAL(62, 21, 130, 152, 152, 188, 226, 171)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__37 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__37_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__38;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Meta_normLitValue___closed__39;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__40;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__32_value),LEAN_SCALAR_PTR_LITERAL(133, 86, 165, 75, 15, 11, 161, 233)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__41 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__41_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__42;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_normLitValue___closed__43;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__44;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__45_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__32_value),LEAN_SCALAR_PTR_LITERAL(24, 152, 19, 102, 101, 167, 71, 92)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__45 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__45_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__46;
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__0 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__1 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_litToCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Lean_Meta_litToCtor___closed__0 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__0_value;
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getNatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_litToCtor___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_litToCtor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Lean_Meta_litToCtor___closed__1 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__1_value;
static lean_once_cell_t l_Lean_Meta_litToCtor___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_litToCtor___closed__2;
static const lean_string_object l_Lean_Meta_litToCtor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Meta_litToCtor___closed__3 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__3_value;
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getNatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_litToCtor___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_litToCtor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l_Lean_Meta_litToCtor___closed__4 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__4_value;
static lean_once_cell_t l_Lean_Meta_litToCtor___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_litToCtor___closed__5;
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_litToCtor___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_getOfNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(192, 66, 133, 102, 95, 170, 134, 92)}};
static const lean_object* l_Lean_Meta_litToCtor___closed__6 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__6_value;
static lean_once_cell_t l_Lean_Meta_litToCtor___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_litToCtor___closed__7;
static const lean_string_object l_Lean_Meta_litToCtor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l_Lean_Meta_litToCtor___closed__8 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__8_value;
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getIntValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_litToCtor___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_litToCtor___closed__8_value),LEAN_SCALAR_PTR_LITERAL(181, 236, 205, 0, 179, 53, 99, 201)}};
static const lean_object* l_Lean_Meta_litToCtor___closed__9 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__9_value;
static lean_once_cell_t l_Lean_Meta_litToCtor___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_litToCtor___closed__10;
static lean_once_cell_t l_Lean_Meta_litToCtor___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_litToCtor___closed__11;
static const lean_string_object l_Lean_Meta_litToCtor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_litToCtor___closed__12 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__12_value;
static const lean_string_object l_Lean_Meta_litToCtor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_litToCtor___closed__13 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__13_value;
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_litToCtor___closed__12_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_litToCtor___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_litToCtor___closed__13_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_litToCtor___closed__14 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__14_value;
static lean_once_cell_t l_Lean_Meta_litToCtor___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_litToCtor___closed__15;
static lean_once_cell_t l_Lean_Meta_litToCtor___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_litToCtor___closed__16;
static const lean_string_object l_Lean_Meta_litToCtor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTNat"};
static const lean_object* l_Lean_Meta_litToCtor___closed__17 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__17_value;
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_litToCtor___closed__17_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 201, 217, 48, 203, 85, 203)}};
static const lean_object* l_Lean_Meta_litToCtor___closed__18 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__18_value;
static lean_once_cell_t l_Lean_Meta_litToCtor___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_litToCtor___closed__19;
static const lean_string_object l_Lean_Meta_litToCtor___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "of_decide_eq_true"};
static const lean_object* l_Lean_Meta_litToCtor___closed__20 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__20_value;
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_litToCtor___closed__20_value),LEAN_SCALAR_PTR_LITERAL(199, 143, 142, 104, 169, 34, 63, 25)}};
static const lean_object* l_Lean_Meta_litToCtor___closed__21 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__21_value;
static lean_once_cell_t l_Lean_Meta_litToCtor___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_litToCtor___closed__22;
static const lean_string_object l_Lean_Meta_litToCtor___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decLt"};
static const lean_object* l_Lean_Meta_litToCtor___closed__23 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__23_value;
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getNatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_litToCtor___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_litToCtor___closed__23_value),LEAN_SCALAR_PTR_LITERAL(70, 116, 195, 81, 41, 93, 3, 179)}};
static const lean_object* l_Lean_Meta_litToCtor___closed__24 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__24_value;
static lean_once_cell_t l_Lean_Meta_litToCtor___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_litToCtor___closed__25;
static const lean_string_object l_Lean_Meta_litToCtor___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Meta_litToCtor___closed__26 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__26_value;
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getFinValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Meta_litToCtor___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_litToCtor___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_litToCtor___closed__26_value),LEAN_SCALAR_PTR_LITERAL(30, 240, 210, 97, 67, 170, 216, 80)}};
static const lean_object* l_Lean_Meta_litToCtor___closed__27 = (const lean_object*)&l_Lean_Meta_litToCtor___closed__27_value;
static lean_once_cell_t l_Lean_Meta_litToCtor___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_litToCtor___closed__28;
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_getListLitOf_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_getListLitOf_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_getListLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getListLit_x3f___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_getListLit_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getListLit_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getRawNatValue_x3f(lean_object* v_e_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Lean_Expr_consumeMData(v_e_1_);
if (lean_obj_tag(v___x_2_) == 9)
{
lean_object* v_a_3_; 
v_a_3_ = lean_ctor_get(v___x_2_, 0);
lean_inc_ref(v_a_3_);
lean_dec_ref_known(v___x_2_, 1);
if (lean_obj_tag(v_a_3_) == 0)
{
lean_object* v_val_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_11_; 
v_val_4_ = lean_ctor_get(v_a_3_, 0);
v_isSharedCheck_11_ = !lean_is_exclusive(v_a_3_);
if (v_isSharedCheck_11_ == 0)
{
v___x_6_ = v_a_3_;
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_val_4_);
lean_dec(v_a_3_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_9_; 
if (v_isShared_7_ == 0)
{
lean_ctor_set_tag(v___x_6_, 1);
v___x_9_ = v___x_6_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v_val_4_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
else
{
lean_object* v___x_12_; 
lean_dec_ref(v_a_3_);
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
else
{
lean_object* v___x_13_; 
lean_dec_ref(v___x_2_);
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getRawNatValue_x3f___boxed(lean_object* v_e_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Meta_getRawNatValue_x3f(v_e_14_);
lean_dec_ref(v_e_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f(lean_object* v_e_21_, lean_object* v_typeDeclName_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_21_, v_a_24_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v_a_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_a_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_a_35_);
lean_dec_ref_known(v___x_34_, 1);
v___x_36_ = l_Lean_Expr_cleanupAnnotations(v_a_35_);
lean_dec(v_a_35_);
v___x_37_ = l_Lean_Expr_isApp(v___x_36_);
if (v___x_37_ == 0)
{
lean_dec_ref(v___x_36_);
goto v___jp_28_;
}
else
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = l_Lean_Expr_appFnCleanup___redArg(v___x_36_);
lean_dec_ref(v___x_36_);
v___x_39_ = l_Lean_Expr_isApp(v___x_38_);
if (v___x_39_ == 0)
{
lean_dec_ref(v___x_38_);
goto v___jp_28_;
}
else
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = l_Lean_Expr_appFnCleanup___redArg(v___x_38_);
v___x_41_ = l_Lean_Expr_isApp(v___x_40_);
if (v___x_41_ == 0)
{
lean_dec_ref(v___x_40_);
lean_dec_ref(v___x_38_);
goto v___jp_28_;
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_42_ = l_Lean_Expr_appFnCleanup___redArg(v___x_40_);
v___x_43_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_44_ = l_Lean_Expr_isConstOf(v___x_42_, v___x_43_);
lean_dec_ref(v___x_42_);
if (v___x_44_ == 0)
{
lean_dec_ref(v___x_40_);
lean_dec_ref(v___x_38_);
goto v___jp_28_;
}
else
{
lean_object* v_arg_45_; lean_object* v_arg_46_; lean_object* v___x_47_; 
v_arg_45_ = lean_ctor_get(v___x_38_, 1);
lean_inc_ref(v_arg_45_);
lean_dec_ref(v___x_38_);
v_arg_46_ = lean_ctor_get(v___x_40_, 1);
lean_inc_ref(v_arg_46_);
lean_dec_ref(v___x_40_);
v___x_47_ = l_Lean_Meta_whnfD(v_arg_46_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_72_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_72_ == 0)
{
v___x_50_ = v___x_47_;
v_isShared_51_ = v_isSharedCheck_72_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_72_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = l_Lean_Expr_getAppFn(v_a_48_);
v___x_53_ = l_Lean_Expr_isConstOf(v___x_52_, v_typeDeclName_22_);
lean_dec_ref(v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_56_; 
lean_dec(v_a_48_);
lean_dec_ref(v_arg_45_);
v___x_54_ = lean_box(0);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 0, v___x_54_);
v___x_56_ = v___x_50_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_54_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
else
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Expr_consumeMData(v_arg_45_);
lean_dec_ref(v_arg_45_);
if (lean_obj_tag(v___x_58_) == 9)
{
lean_object* v_a_59_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc_ref(v_a_59_);
lean_dec_ref_known(v___x_58_, 1);
if (lean_obj_tag(v_a_59_) == 0)
{
lean_object* v_val_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_71_; 
v_val_60_ = lean_ctor_get(v_a_59_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v_a_59_);
if (v_isSharedCheck_71_ == 0)
{
v___x_62_ = v_a_59_;
v_isShared_63_ = v_isSharedCheck_71_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_val_60_);
lean_dec(v_a_59_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_71_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v_val_60_);
lean_ctor_set(v___x_64_, 1, v_a_48_);
if (v_isShared_63_ == 0)
{
lean_ctor_set_tag(v___x_62_, 1);
lean_ctor_set(v___x_62_, 0, v___x_64_);
v___x_66_ = v___x_62_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_70_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_68_; 
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 0, v___x_66_);
v___x_68_ = v___x_50_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
else
{
lean_dec_ref(v_a_59_);
lean_del_object(v___x_50_);
lean_dec(v_a_48_);
goto v___jp_31_;
}
}
else
{
lean_dec_ref(v___x_58_);
lean_del_object(v___x_50_);
lean_dec(v_a_48_);
goto v___jp_31_;
}
}
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
lean_dec_ref(v_arg_45_);
v_a_73_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_47_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_47_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
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
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
v_a_81_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_34_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_34_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
v___jp_28_:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_box(0);
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
v___jp_31_:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_box(0);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f___boxed(lean_object* v_e_89_, lean_object* v_typeDeclName_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_getOfNatValue_x3f(v_e_89_, v_typeDeclName_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_typeDeclName_90_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getNatValue_x3f(lean_object* v_e_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_e_106_; lean_object* v___x_107_; 
v_e_106_ = l_Lean_Expr_consumeMData(v_e_100_);
v___x_107_ = l_Lean_Meta_getRawNatValue_x3f(v_e_106_);
if (lean_obj_tag(v___x_107_) == 1)
{
lean_object* v___x_108_; 
lean_dec_ref(v_e_106_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v___x_107_);
v___x_109_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_110_ = l_Lean_Meta_getOfNatValue_x3f(v_e_106_, v___x_109_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_131_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_131_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_131_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_131_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
if (lean_obj_tag(v_a_111_) == 1)
{
lean_object* v_val_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_126_; 
v_val_115_ = lean_ctor_get(v_a_111_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v_a_111_);
if (v_isSharedCheck_126_ == 0)
{
v___x_117_ = v_a_111_;
v_isShared_118_ = v_isSharedCheck_126_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_val_115_);
lean_dec(v_a_111_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_126_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_fst_119_; lean_object* v___x_121_; 
v_fst_119_ = lean_ctor_get(v_val_115_, 0);
lean_inc(v_fst_119_);
lean_dec(v_val_115_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v_fst_119_);
v___x_121_ = v___x_117_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_fst_119_);
v___x_121_ = v_reuseFailAlloc_125_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_123_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_121_);
v___x_123_ = v___x_113_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
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
else
{
lean_object* v___x_127_; lean_object* v___x_129_; 
lean_dec(v_a_111_);
v___x_127_ = lean_box(0);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_127_);
v___x_129_ = v___x_113_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
v_a_132_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_110_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_110_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getNatValue_x3f___boxed(lean_object* v_e_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Meta_getNatValue_x3f(v_e_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec_ref(v_e_140_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isNatValue(lean_object* v_e_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_e_153_; uint8_t v___x_154_; 
v_e_153_ = l_Lean_Expr_consumeMData(v_e_147_);
v___x_154_ = l_Lean_Expr_isRawNatLit(v_e_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_153_, v_a_149_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_214_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_214_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_214_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_214_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = l_Lean_Expr_cleanupAnnotations(v_a_156_);
lean_dec(v_a_156_);
v___x_161_ = l_Lean_Expr_isApp(v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_164_; 
lean_dec_ref(v___x_160_);
v___x_162_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_162_);
v___x_164_ = v___x_158_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
else
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = l_Lean_Expr_appFnCleanup___redArg(v___x_160_);
lean_dec_ref(v___x_160_);
v___x_167_ = l_Lean_Expr_isApp(v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_170_; 
lean_dec_ref(v___x_166_);
v___x_168_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_168_);
v___x_170_ = v___x_158_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
else
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_166_);
v___x_173_ = l_Lean_Expr_isApp(v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_176_; 
lean_dec_ref(v___x_172_);
lean_dec_ref(v___x_166_);
v___x_174_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_174_);
v___x_176_ = v___x_158_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_178_ = l_Lean_Expr_appFnCleanup___redArg(v___x_172_);
v___x_179_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_180_ = l_Lean_Expr_isConstOf(v___x_178_, v___x_179_);
lean_dec_ref(v___x_178_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_183_; 
lean_dec_ref(v___x_172_);
lean_dec_ref(v___x_166_);
v___x_181_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_181_);
v___x_183_ = v___x_158_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
else
{
lean_object* v_arg_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_arg_185_ = lean_ctor_get(v___x_166_, 1);
lean_inc_ref(v_arg_185_);
lean_dec_ref(v___x_166_);
v___x_186_ = l_Lean_Expr_consumeMData(v_arg_185_);
lean_dec_ref(v_arg_185_);
v___x_187_ = l_Lean_Expr_isRawNatLit(v___x_186_);
lean_dec_ref(v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_190_; 
lean_dec_ref(v___x_172_);
v___x_188_ = lean_box(v___x_187_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_188_);
v___x_190_ = v___x_158_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
else
{
lean_object* v_arg_192_; lean_object* v___x_193_; 
lean_del_object(v___x_158_);
v_arg_192_ = lean_ctor_get(v___x_172_, 1);
lean_inc_ref(v_arg_192_);
lean_dec_ref(v___x_172_);
v___x_193_ = l_Lean_Meta_whnfD(v_arg_192_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_205_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_205_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_205_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_205_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_198_ = l_Lean_Expr_getAppFn(v_a_194_);
lean_dec(v_a_194_);
v___x_199_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_200_ = l_Lean_Expr_isConstOf(v___x_198_, v___x_199_);
lean_dec_ref(v___x_198_);
v___x_201_ = lean_box(v___x_200_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_201_);
v___x_203_ = v___x_196_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
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
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_a_206_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_193_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_193_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
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
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
v_a_215_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_155_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_155_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec_ref(v_e_153_);
v___x_223_ = lean_box(v___x_154_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isNatValue___boxed(lean_object* v_e_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Meta_isNatValue(v_e_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec_ref(v_e_225_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isNonZeroNatValue(lean_object* v_e_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_e_246_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; 
v_e_246_ = l_Lean_Expr_consumeMData(v_e_232_);
if (lean_obj_tag(v_e_246_) == 9)
{
lean_object* v_a_308_; 
v_a_308_ = lean_ctor_get(v_e_246_, 0);
lean_inc_ref(v_a_308_);
if (lean_obj_tag(v_a_308_) == 0)
{
lean_object* v_val_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref_known(v_e_246_, 1);
v_val_309_ = lean_ctor_get(v_a_308_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v_a_308_);
if (v_isSharedCheck_325_ == 0)
{
v___x_311_ = v_a_308_;
v_isShared_312_ = v_isSharedCheck_325_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_val_309_);
lean_dec(v_a_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_325_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_nat_dec_eq(v_val_309_, v___x_313_);
lean_dec(v_val_309_);
if (v___x_314_ == 0)
{
uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_315_ = 1;
v___x_316_ = lean_box(v___x_315_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_316_);
v___x_318_ = v___x_311_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_320_ = 0;
v___x_321_ = lean_box(v___x_320_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_321_);
v___x_323_ = v___x_311_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_dec_ref(v_a_308_);
v___y_248_ = v_a_233_;
v___y_249_ = v_a_234_;
v___y_250_ = v_a_235_;
v___y_251_ = v_a_236_;
goto v___jp_247_;
}
}
else
{
v___y_248_ = v_a_233_;
v___y_249_ = v_a_234_;
v___y_250_ = v_a_235_;
v___y_251_ = v_a_236_;
goto v___jp_247_;
}
v___jp_238_:
{
uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = 0;
v___x_240_ = lean_box(v___x_239_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
v___jp_242_:
{
uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = 0;
v___x_244_ = lean_box(v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
v___jp_247_:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_246_, v___y_249_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_299_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_299_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_299_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_299_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = l_Lean_Expr_cleanupAnnotations(v_a_253_);
lean_dec(v_a_253_);
v___x_258_ = l_Lean_Expr_isApp(v___x_257_);
if (v___x_258_ == 0)
{
lean_dec_ref(v___x_257_);
lean_del_object(v___x_255_);
goto v___jp_242_;
}
else
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = l_Lean_Expr_appFnCleanup___redArg(v___x_257_);
lean_dec_ref(v___x_257_);
v___x_260_ = l_Lean_Expr_isApp(v___x_259_);
if (v___x_260_ == 0)
{
lean_dec_ref(v___x_259_);
lean_del_object(v___x_255_);
goto v___jp_242_;
}
else
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = l_Lean_Expr_appFnCleanup___redArg(v___x_259_);
v___x_262_ = l_Lean_Expr_isApp(v___x_261_);
if (v___x_262_ == 0)
{
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_259_);
lean_del_object(v___x_255_);
goto v___jp_242_;
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_261_);
v___x_264_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_265_ = l_Lean_Expr_isConstOf(v___x_263_, v___x_264_);
lean_dec_ref(v___x_263_);
if (v___x_265_ == 0)
{
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_259_);
lean_del_object(v___x_255_);
goto v___jp_242_;
}
else
{
lean_object* v_arg_266_; lean_object* v___x_267_; 
v_arg_266_ = lean_ctor_get(v___x_259_, 1);
lean_inc_ref(v_arg_266_);
lean_dec_ref(v___x_259_);
v___x_267_ = l_Lean_Expr_consumeMData(v_arg_266_);
lean_dec_ref(v_arg_266_);
if (lean_obj_tag(v___x_267_) == 9)
{
lean_object* v_a_268_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_a_268_);
lean_dec_ref_known(v___x_267_, 1);
if (lean_obj_tag(v_a_268_) == 0)
{
lean_object* v_val_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_val_269_ = lean_ctor_get(v_a_268_, 0);
lean_inc(v_val_269_);
lean_dec_ref_known(v_a_268_, 1);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_nat_dec_eq(v_val_269_, v___x_270_);
lean_dec(v_val_269_);
if (v___x_271_ == 0)
{
lean_object* v_arg_272_; lean_object* v___x_273_; 
lean_del_object(v___x_255_);
v_arg_272_ = lean_ctor_get(v___x_261_, 1);
lean_inc_ref(v_arg_272_);
lean_dec_ref(v___x_261_);
v___x_273_ = l_Lean_Meta_whnfD(v_arg_272_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_285_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_285_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_285_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_285_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_278_ = l_Lean_Expr_getAppFn(v_a_274_);
lean_dec(v_a_274_);
v___x_279_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_280_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_279_);
lean_dec_ref(v___x_278_);
v___x_281_ = lean_box(v___x_280_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_281_);
v___x_283_ = v___x_276_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_a_286_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_273_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_273_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
lean_dec_ref(v___x_261_);
v___x_294_ = 0;
v___x_295_ = lean_box(v___x_294_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_295_);
v___x_297_ = v___x_255_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_dec_ref(v_a_268_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_255_);
goto v___jp_238_;
}
}
else
{
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_255_);
goto v___jp_238_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_a_300_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_252_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_252_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isNonZeroNatValue___boxed(lean_object* v_e_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Meta_isNonZeroNatValue(v_e_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec_ref(v_e_326_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_getIntValue_x3f_spec__0(lean_object* v_a_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_nat_to_int(v_a_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntValue_x3f(lean_object* v_e_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
lean_inc_ref(v_e_343_);
v___x_353_ = l_Lean_Meta_getOfNatValue_x3f(v_e_343_, v___x_352_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_423_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_423_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_423_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_423_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
if (lean_obj_tag(v_a_354_) == 1)
{
lean_object* v_val_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref(v_e_343_);
v_val_358_ = lean_ctor_get(v_a_354_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v_a_354_);
if (v_isSharedCheck_370_ == 0)
{
v___x_360_ = v_a_354_;
v_isShared_361_ = v_isSharedCheck_370_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_val_358_);
lean_dec(v_a_354_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_370_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_fst_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v_fst_362_ = lean_ctor_get(v_val_358_, 0);
lean_inc(v_fst_362_);
lean_dec(v_val_358_);
v___x_363_ = lean_nat_to_int(v_fst_362_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_363_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_365_);
v___x_367_ = v___x_356_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
else
{
lean_object* v___x_371_; 
lean_del_object(v___x_356_);
lean_dec(v_a_354_);
v___x_371_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_343_, v_a_345_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = l_Lean_Expr_cleanupAnnotations(v_a_372_);
lean_dec(v_a_372_);
v___x_374_ = l_Lean_Expr_isApp(v___x_373_);
if (v___x_374_ == 0)
{
lean_dec_ref(v___x_373_);
goto v___jp_349_;
}
else
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_373_);
v___x_376_ = l_Lean_Expr_isApp(v___x_375_);
if (v___x_376_ == 0)
{
lean_dec_ref(v___x_375_);
lean_dec_ref(v___x_373_);
goto v___jp_349_;
}
else
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = l_Lean_Expr_appFnCleanup___redArg(v___x_375_);
lean_dec_ref(v___x_375_);
v___x_378_ = l_Lean_Expr_isApp(v___x_377_);
if (v___x_378_ == 0)
{
lean_dec_ref(v___x_377_);
lean_dec_ref(v___x_373_);
goto v___jp_349_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_377_);
lean_dec_ref(v___x_377_);
v___x_380_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_381_ = l_Lean_Expr_isConstOf(v___x_379_, v___x_380_);
lean_dec_ref(v___x_379_);
if (v___x_381_ == 0)
{
lean_dec_ref(v___x_373_);
goto v___jp_349_;
}
else
{
lean_object* v_arg_382_; lean_object* v___x_383_; 
v_arg_382_ = lean_ctor_get(v___x_373_, 1);
lean_inc_ref(v_arg_382_);
lean_dec_ref(v___x_373_);
v___x_383_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_382_, v___x_352_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_406_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_406_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_406_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_406_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
if (lean_obj_tag(v_a_384_) == 1)
{
lean_object* v_val_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_401_; 
v_val_388_ = lean_ctor_get(v_a_384_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_a_384_);
if (v_isSharedCheck_401_ == 0)
{
v___x_390_ = v_a_384_;
v_isShared_391_ = v_isSharedCheck_401_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_val_388_);
lean_dec(v_a_384_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_401_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v_fst_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v_fst_392_ = lean_ctor_get(v_val_388_, 0);
lean_inc(v_fst_392_);
lean_dec(v_val_388_);
v___x_393_ = lean_nat_to_int(v_fst_392_);
v___x_394_ = lean_int_neg(v___x_393_);
lean_dec(v___x_393_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_394_);
v___x_396_ = v___x_390_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_400_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_398_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_396_);
v___x_398_ = v___x_386_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_dec(v_a_384_);
v___x_402_ = lean_box(0);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_402_);
v___x_404_ = v___x_386_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_383_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_383_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
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
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_a_415_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_371_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_371_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec_ref(v_e_343_);
v_a_424_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_353_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_353_);
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
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
v___jp_349_:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_box(0);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntValue_x3f___boxed(lean_object* v_e_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_getIntValue_x3f(v_e_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatValue(lean_object* v_e_439_, lean_object* v_typeDeclName_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_439_, v_a_442_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_492_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_492_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_492_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_492_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = l_Lean_Expr_cleanupAnnotations(v_a_451_);
lean_dec(v_a_451_);
v___x_456_ = l_Lean_Expr_isApp(v___x_455_);
if (v___x_456_ == 0)
{
lean_dec_ref(v___x_455_);
lean_del_object(v___x_453_);
goto v___jp_446_;
}
else
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = l_Lean_Expr_appFnCleanup___redArg(v___x_455_);
lean_dec_ref(v___x_455_);
v___x_458_ = l_Lean_Expr_isApp(v___x_457_);
if (v___x_458_ == 0)
{
lean_dec_ref(v___x_457_);
lean_del_object(v___x_453_);
goto v___jp_446_;
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = l_Lean_Expr_appFnCleanup___redArg(v___x_457_);
v___x_460_ = l_Lean_Expr_isApp(v___x_459_);
if (v___x_460_ == 0)
{
lean_dec_ref(v___x_459_);
lean_dec_ref(v___x_457_);
lean_del_object(v___x_453_);
goto v___jp_446_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_461_ = l_Lean_Expr_appFnCleanup___redArg(v___x_459_);
v___x_462_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_463_ = l_Lean_Expr_isConstOf(v___x_461_, v___x_462_);
lean_dec_ref(v___x_461_);
if (v___x_463_ == 0)
{
lean_dec_ref(v___x_459_);
lean_dec_ref(v___x_457_);
lean_del_object(v___x_453_);
goto v___jp_446_;
}
else
{
lean_object* v_arg_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_arg_464_ = lean_ctor_get(v___x_457_, 1);
lean_inc_ref(v_arg_464_);
lean_dec_ref(v___x_457_);
v___x_465_ = l_Lean_Expr_consumeMData(v_arg_464_);
lean_dec_ref(v_arg_464_);
v___x_466_ = l_Lean_Expr_isRawNatLit(v___x_465_);
lean_dec_ref(v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_dec_ref(v___x_459_);
v___x_467_ = lean_box(v___x_466_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_467_);
v___x_469_ = v___x_453_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
else
{
lean_object* v_arg_471_; lean_object* v___x_472_; 
lean_del_object(v___x_453_);
v_arg_471_ = lean_ctor_get(v___x_459_, 1);
lean_inc_ref(v_arg_471_);
lean_dec_ref(v___x_459_);
v___x_472_ = l_Lean_Meta_whnfD(v_arg_471_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_483_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_483_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_483_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_483_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_477_ = l_Lean_Expr_getAppFn(v_a_473_);
lean_dec(v_a_473_);
v___x_478_ = l_Lean_Expr_isConstOf(v___x_477_, v_typeDeclName_440_);
lean_dec_ref(v___x_477_);
v___x_479_ = lean_box(v___x_478_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_479_);
v___x_481_ = v___x_475_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_a_484_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_472_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_472_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
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
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_a_493_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_450_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_450_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
v___jp_446_:
{
uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = 0;
v___x_448_ = lean_box(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatValue___boxed(lean_object* v_e_501_, lean_object* v_typeDeclName_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatValue(v_e_501_, v_typeDeclName_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_typeDeclName_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isIntValue(lean_object* v_e_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
lean_inc_ref(v_e_509_);
v___x_516_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatValue(v_e_509_, v___x_515_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; uint8_t v___x_518_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v___x_518_ = lean_unbox(v_a_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v___x_519_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_509_, v_a_511_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_547_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_547_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_547_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_547_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = l_Lean_Expr_cleanupAnnotations(v_a_520_);
lean_dec(v_a_520_);
v___x_525_ = l_Lean_Expr_isApp(v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_527_; 
lean_dec_ref(v___x_524_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v_a_517_);
v___x_527_ = v___x_522_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_517_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = l_Lean_Expr_appFnCleanup___redArg(v___x_524_);
v___x_530_ = l_Lean_Expr_isApp(v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_532_; 
lean_dec_ref(v___x_529_);
lean_dec_ref(v___x_524_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v_a_517_);
v___x_532_ = v___x_522_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_517_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
else
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = l_Lean_Expr_appFnCleanup___redArg(v___x_529_);
lean_dec_ref(v___x_529_);
v___x_535_ = l_Lean_Expr_isApp(v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_537_; 
lean_dec_ref(v___x_534_);
lean_dec_ref(v___x_524_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v_a_517_);
v___x_537_ = v___x_522_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_517_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_539_ = l_Lean_Expr_appFnCleanup___redArg(v___x_534_);
lean_dec_ref(v___x_534_);
v___x_540_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_541_ = l_Lean_Expr_isConstOf(v___x_539_, v___x_540_);
lean_dec_ref(v___x_539_);
if (v___x_541_ == 0)
{
lean_object* v___x_543_; 
lean_dec_ref(v___x_524_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v_a_517_);
v___x_543_ = v___x_522_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_517_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
else
{
lean_object* v_arg_545_; lean_object* v___x_546_; 
lean_del_object(v___x_522_);
lean_dec(v_a_517_);
v_arg_545_ = lean_ctor_get(v___x_524_, 1);
lean_inc_ref(v_arg_545_);
lean_dec_ref(v___x_524_);
v___x_546_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatValue(v_arg_545_, v___x_515_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
return v___x_546_;
}
}
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v_a_517_);
v_a_548_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_519_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_519_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_dec_ref(v_e_509_);
return v___x_516_;
}
}
else
{
lean_dec_ref(v_e_509_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isIntValue___boxed(lean_object* v_e_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Meta_isIntValue(v_e_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(lean_object* v_e_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Expr_consumeMData(v_e_566_);
if (lean_obj_tag(v___x_567_) == 4)
{
lean_object* v_declName_568_; 
v_declName_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_declName_568_);
lean_dec_ref_known(v___x_567_, 2);
if (lean_obj_tag(v_declName_568_) == 1)
{
lean_object* v_pre_569_; 
v_pre_569_ = lean_ctor_get(v_declName_568_, 0);
lean_inc(v_pre_569_);
if (lean_obj_tag(v_pre_569_) == 1)
{
lean_object* v_pre_570_; 
v_pre_570_ = lean_ctor_get(v_pre_569_, 0);
if (lean_obj_tag(v_pre_570_) == 0)
{
lean_object* v_str_571_; lean_object* v_str_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_str_571_ = lean_ctor_get(v_declName_568_, 1);
lean_inc_ref(v_str_571_);
lean_dec_ref_known(v_declName_568_, 2);
v_str_572_ = lean_ctor_get(v_pre_569_, 1);
lean_inc_ref(v_str_572_);
lean_dec_ref_known(v_pre_569_, 2);
v___x_573_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0));
v___x_574_ = lean_string_dec_eq(v_str_572_, v___x_573_);
lean_dec_ref(v_str_572_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
lean_dec_ref(v_str_571_);
v___x_575_ = lean_box(0);
return v___x_575_;
}
else
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1));
v___x_577_ = lean_string_dec_eq(v_str_571_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2));
v___x_579_ = lean_string_dec_eq(v_str_571_, v___x_578_);
lean_dec_ref(v_str_571_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_box(0);
return v___x_580_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_box(v___x_577_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec_ref(v_str_571_);
v___x_583_ = lean_box(v___x_577_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
}
else
{
lean_object* v___x_585_; 
lean_dec_ref_known(v_pre_569_, 2);
lean_dec_ref_known(v_declName_568_, 2);
v___x_585_ = lean_box(0);
return v___x_585_;
}
}
else
{
lean_object* v___x_586_; 
lean_dec(v_pre_569_);
lean_dec_ref_known(v_declName_568_, 2);
v___x_586_ = lean_box(0);
return v___x_586_;
}
}
else
{
lean_object* v___x_587_; 
lean_dec(v_declName_568_);
v___x_587_ = lean_box(0);
return v___x_587_;
}
}
else
{
lean_object* v___x_588_; 
lean_dec_ref(v___x_567_);
v___x_588_ = lean_box(0);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___boxed(lean_object* v_e_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_e_589_);
lean_dec_ref(v_e_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f_spec__0(lean_object* v_a_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_nat_to_int(v_a_591_);
v___x_593_ = l_Rat_ofInt(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(lean_object* v_e_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___x_645_; 
lean_inc_ref(v_e_602_);
v___x_645_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_602_, v_a_604_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = l_Lean_Expr_cleanupAnnotations(v_a_646_);
lean_dec(v_a_646_);
v___x_648_ = l_Lean_Expr_isApp(v___x_647_);
if (v___x_648_ == 0)
{
lean_dec_ref(v___x_647_);
v___y_609_ = v_a_603_;
v___y_610_ = v_a_604_;
v___y_611_ = v_a_605_;
v___y_612_ = v_a_606_;
goto v___jp_608_;
}
else
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = l_Lean_Expr_appFnCleanup___redArg(v___x_647_);
v___x_650_ = l_Lean_Expr_isApp(v___x_649_);
if (v___x_650_ == 0)
{
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_647_);
v___y_609_ = v_a_603_;
v___y_610_ = v_a_604_;
v___y_611_ = v_a_605_;
v___y_612_ = v_a_606_;
goto v___jp_608_;
}
else
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = l_Lean_Expr_appFnCleanup___redArg(v___x_649_);
v___x_652_ = l_Lean_Expr_isApp(v___x_651_);
if (v___x_652_ == 0)
{
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_647_);
v___y_609_ = v_a_603_;
v___y_610_ = v_a_604_;
v___y_611_ = v_a_605_;
v___y_612_ = v_a_606_;
goto v___jp_608_;
}
else
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = l_Lean_Expr_appFnCleanup___redArg(v___x_651_);
v___x_654_ = l_Lean_Expr_isApp(v___x_653_);
if (v___x_654_ == 0)
{
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_647_);
v___y_609_ = v_a_603_;
v___y_610_ = v_a_604_;
v___y_611_ = v_a_605_;
v___y_612_ = v_a_606_;
goto v___jp_608_;
}
else
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = l_Lean_Expr_appFnCleanup___redArg(v___x_653_);
lean_dec_ref(v___x_653_);
v___x_656_ = l_Lean_Expr_isApp(v___x_655_);
if (v___x_656_ == 0)
{
lean_dec_ref(v___x_655_);
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_647_);
v___y_609_ = v_a_603_;
v___y_610_ = v_a_604_;
v___y_611_ = v_a_605_;
v___y_612_ = v_a_606_;
goto v___jp_608_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_655_);
v___x_658_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_659_ = l_Lean_Expr_isConstOf(v___x_657_, v___x_658_);
lean_dec_ref(v___x_657_);
if (v___x_659_ == 0)
{
lean_dec_ref(v___x_655_);
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_647_);
v___y_609_ = v_a_603_;
v___y_610_ = v_a_604_;
v___y_611_ = v_a_605_;
v___y_612_ = v_a_606_;
goto v___jp_608_;
}
else
{
lean_object* v_arg_660_; lean_object* v_arg_661_; lean_object* v_arg_662_; lean_object* v_arg_663_; lean_object* v___x_664_; 
lean_dec_ref(v_e_602_);
v_arg_660_ = lean_ctor_get(v___x_647_, 1);
lean_inc_ref(v_arg_660_);
lean_dec_ref(v___x_647_);
v_arg_661_ = lean_ctor_get(v___x_649_, 1);
lean_inc_ref(v_arg_661_);
lean_dec_ref(v___x_649_);
v_arg_662_ = lean_ctor_get(v___x_651_, 1);
lean_inc_ref(v_arg_662_);
lean_dec_ref(v___x_651_);
v_arg_663_ = lean_ctor_get(v___x_655_, 1);
lean_inc_ref(v_arg_663_);
lean_dec_ref(v___x_655_);
v___x_664_ = l_Lean_Meta_whnfD(v_arg_663_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_731_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_731_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_731_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_731_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_670_ = l_Lean_Expr_isConstOf(v_a_665_, v___x_669_);
lean_dec(v_a_665_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_673_; 
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_661_);
lean_dec_ref(v_arg_660_);
v___x_671_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_671_);
v___x_673_ = v___x_667_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
else
{
lean_object* v___x_675_; 
v___x_675_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_661_);
lean_dec_ref(v_arg_661_);
if (lean_obj_tag(v___x_675_) == 1)
{
lean_object* v_val_676_; lean_object* v___x_677_; 
lean_del_object(v___x_667_);
v_val_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_val_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_677_ = l_Lean_Meta_getNatValue_x3f(v_arg_662_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
lean_dec_ref(v_arg_662_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_718_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_718_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_718_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_718_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
if (lean_obj_tag(v_a_678_) == 0)
{
lean_object* v___x_682_; lean_object* v___x_684_; 
lean_dec(v_val_676_);
lean_dec_ref(v_arg_660_);
v___x_682_ = lean_box(0);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
else
{
lean_object* v_val_686_; lean_object* v___x_687_; 
lean_del_object(v___x_680_);
v_val_686_ = lean_ctor_get(v_a_678_, 0);
lean_inc(v_val_686_);
lean_dec_ref_known(v_a_678_, 1);
v___x_687_ = l_Lean_Meta_getNatValue_x3f(v_arg_660_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
lean_dec_ref(v_arg_660_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_709_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_709_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_709_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_709_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
if (lean_obj_tag(v_a_688_) == 0)
{
lean_object* v___x_692_; lean_object* v___x_694_; 
lean_dec(v_val_686_);
lean_dec(v_val_676_);
v___x_692_ = lean_box(0);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
else
{
lean_object* v_val_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_708_; 
v_val_696_ = lean_ctor_get(v_a_688_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_688_);
if (v_isSharedCheck_708_ == 0)
{
v___x_698_ = v_a_688_;
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_val_696_);
lean_dec(v_a_688_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_700_ = lean_unbox(v_val_676_);
lean_dec(v_val_676_);
v___x_701_ = l_Rat_ofScientific(v_val_686_, v___x_700_, v_val_696_);
lean_dec(v_val_696_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_701_);
v___x_703_ = v___x_698_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_703_);
v___x_705_ = v___x_690_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v_val_686_);
lean_dec(v_val_676_);
v_a_710_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_687_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_687_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_val_676_);
lean_dec_ref(v_arg_660_);
v_a_719_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_677_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_677_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_729_; 
lean_dec(v___x_675_);
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_660_);
v___x_727_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_727_);
v___x_729_ = v___x_667_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_661_);
lean_dec_ref(v_arg_660_);
v_a_732_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_664_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_664_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
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
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v_e_602_);
v_a_740_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_645_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_645_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
v___jp_608_:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_614_ = l_Lean_Meta_getOfNatValue_x3f(v_e_602_, v___x_613_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_636_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_636_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_636_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_636_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
if (lean_obj_tag(v_a_615_) == 0)
{
lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_619_ = lean_box(0);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_619_);
v___x_621_ = v___x_617_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v_val_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_635_; 
v_val_623_ = lean_ctor_get(v_a_615_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v_a_615_);
if (v_isSharedCheck_635_ == 0)
{
v___x_625_ = v_a_615_;
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_val_623_);
lean_dec(v_a_615_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v_fst_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v_fst_627_ = lean_ctor_get(v_val_623_, 0);
lean_inc(v_fst_627_);
lean_dec(v_val_623_);
v___x_628_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f_spec__0(v_fst_627_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_628_);
v___x_630_ = v___x_625_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_634_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_632_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_630_);
v___x_632_ = v___x_617_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
v_a_637_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_614_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_614_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___boxed(lean_object* v_e_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(lean_object* v_e_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
lean_inc_ref(v_e_755_);
v___x_765_ = l_Lean_Meta_getOfNatValue_x3f(v_e_755_, v___x_764_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_835_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_835_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_835_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_835_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
if (lean_obj_tag(v_a_766_) == 1)
{
lean_object* v_val_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_782_; 
lean_dec_ref(v_e_755_);
v_val_770_ = lean_ctor_get(v_a_766_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v_a_766_);
if (v_isSharedCheck_782_ == 0)
{
v___x_772_ = v_a_766_;
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_val_770_);
lean_dec(v_a_766_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_fst_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v_fst_774_ = lean_ctor_get(v_val_770_, 0);
lean_inc(v_fst_774_);
lean_dec(v_val_770_);
v___x_775_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f_spec__0(v_fst_774_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_775_);
v___x_777_ = v___x_772_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_781_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_779_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_777_);
v___x_779_ = v___x_768_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v___x_783_; 
lean_del_object(v___x_768_);
lean_dec(v_a_766_);
v___x_783_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_755_, v_a_757_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v___x_785_ = l_Lean_Expr_cleanupAnnotations(v_a_784_);
lean_dec(v_a_784_);
v___x_786_ = l_Lean_Expr_isApp(v___x_785_);
if (v___x_786_ == 0)
{
lean_dec_ref(v___x_785_);
goto v___jp_761_;
}
else
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = l_Lean_Expr_appFnCleanup___redArg(v___x_785_);
v___x_788_ = l_Lean_Expr_isApp(v___x_787_);
if (v___x_788_ == 0)
{
lean_dec_ref(v___x_787_);
lean_dec_ref(v___x_785_);
goto v___jp_761_;
}
else
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_787_);
lean_dec_ref(v___x_787_);
v___x_790_ = l_Lean_Expr_isApp(v___x_789_);
if (v___x_790_ == 0)
{
lean_dec_ref(v___x_789_);
lean_dec_ref(v___x_785_);
goto v___jp_761_;
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_791_ = l_Lean_Expr_appFnCleanup___redArg(v___x_789_);
lean_dec_ref(v___x_789_);
v___x_792_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_793_ = l_Lean_Expr_isConstOf(v___x_791_, v___x_792_);
lean_dec_ref(v___x_791_);
if (v___x_793_ == 0)
{
lean_dec_ref(v___x_785_);
goto v___jp_761_;
}
else
{
lean_object* v_arg_794_; lean_object* v___x_795_; 
v_arg_794_ = lean_ctor_get(v___x_785_, 1);
lean_inc_ref(v_arg_794_);
lean_dec_ref(v___x_785_);
v___x_795_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_794_, v___x_764_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_818_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_818_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_818_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_818_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
if (lean_obj_tag(v_a_796_) == 1)
{
lean_object* v_val_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_813_; 
v_val_800_ = lean_ctor_get(v_a_796_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_a_796_);
if (v_isSharedCheck_813_ == 0)
{
v___x_802_ = v_a_796_;
v_isShared_803_ = v_isSharedCheck_813_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_val_800_);
lean_dec(v_a_796_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_813_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_fst_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v_fst_804_ = lean_ctor_get(v_val_800_, 0);
lean_inc(v_fst_804_);
lean_dec(v_val_800_);
v___x_805_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f_spec__0(v_fst_804_);
v___x_806_ = l_Rat_neg(v___x_805_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_806_);
v___x_808_ = v___x_802_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_812_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_808_);
v___x_810_ = v___x_798_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v_a_796_);
v___x_814_ = lean_box(0);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_814_);
v___x_816_ = v___x_798_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
v_a_819_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_795_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_795_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
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
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_783_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_783_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec_ref(v_e_755_);
v_a_836_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_765_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_765_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
v___jp_761_:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_box(0);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___boxed(lean_object* v_e_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getRatValue_x3f(lean_object* v_e_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
lean_inc_ref(v_e_856_);
v___x_862_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_856_, v_a_858_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = l_Lean_Expr_cleanupAnnotations(v_a_863_);
lean_dec(v_a_863_);
v___x_865_ = l_Lean_Expr_isApp(v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; 
lean_dec_ref(v___x_864_);
v___x_866_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = l_Lean_Expr_appFnCleanup___redArg(v___x_864_);
v___x_868_ = l_Lean_Expr_isApp(v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
lean_dec_ref(v___x_867_);
lean_dec_ref(v___x_864_);
v___x_869_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = l_Lean_Expr_appFnCleanup___redArg(v___x_867_);
v___x_871_ = l_Lean_Expr_isApp(v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
lean_dec_ref(v___x_870_);
lean_dec_ref(v___x_867_);
lean_dec_ref(v___x_864_);
v___x_872_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_872_;
}
else
{
lean_object* v_arg_873_; lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v_arg_873_ = lean_ctor_get(v___x_864_, 1);
lean_inc_ref(v_arg_873_);
lean_dec_ref(v___x_864_);
v___x_874_ = l_Lean_Expr_appFnCleanup___redArg(v___x_870_);
lean_dec_ref(v___x_870_);
v___x_875_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_876_ = l_Lean_Expr_isConstOf(v___x_874_, v___x_875_);
if (v___x_876_ == 0)
{
uint8_t v___x_877_; 
v___x_877_ = l_Lean_Expr_isApp(v___x_874_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
lean_dec_ref(v___x_874_);
lean_dec_ref(v_arg_873_);
lean_dec_ref(v___x_867_);
v___x_878_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = l_Lean_Expr_appFnCleanup___redArg(v___x_874_);
lean_dec_ref(v___x_874_);
v___x_880_ = l_Lean_Expr_isApp(v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_dec_ref(v___x_879_);
lean_dec_ref(v_arg_873_);
lean_dec_ref(v___x_867_);
v___x_881_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_881_;
}
else
{
lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_882_ = l_Lean_Expr_appFnCleanup___redArg(v___x_879_);
lean_dec_ref(v___x_879_);
v___x_883_ = l_Lean_Expr_isApp(v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; 
lean_dec_ref(v___x_882_);
lean_dec_ref(v_arg_873_);
lean_dec_ref(v___x_867_);
v___x_884_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = l_Lean_Expr_appFnCleanup___redArg(v___x_882_);
lean_dec_ref(v___x_882_);
v___x_886_ = ((lean_object*)(l_Lean_Meta_getRatValue_x3f___closed__2));
v___x_887_ = l_Lean_Expr_isConstOf(v___x_885_, v___x_886_);
lean_dec_ref(v___x_885_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec_ref(v_arg_873_);
lean_dec_ref(v___x_867_);
v___x_888_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_888_;
}
else
{
lean_object* v_arg_889_; lean_object* v___x_890_; 
lean_dec_ref(v_e_856_);
v_arg_889_ = lean_ctor_get(v___x_867_, 1);
lean_inc_ref(v_arg_889_);
lean_dec_ref(v___x_867_);
v___x_890_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_arg_889_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_933_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_933_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_933_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_933_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
if (lean_obj_tag(v_a_891_) == 1)
{
lean_object* v_val_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
lean_del_object(v___x_893_);
v_val_895_ = lean_ctor_get(v_a_891_, 0);
lean_inc(v_val_895_);
lean_dec_ref_known(v_a_891_, 1);
v___x_896_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_897_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_873_, v___x_896_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_920_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_920_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_920_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_920_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
if (lean_obj_tag(v_a_898_) == 1)
{
lean_object* v_val_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_915_; 
v_val_902_ = lean_ctor_get(v_a_898_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v_a_898_);
if (v_isSharedCheck_915_ == 0)
{
v___x_904_ = v_a_898_;
v_isShared_905_ = v_isSharedCheck_915_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_val_902_);
lean_dec(v_a_898_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_915_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_fst_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v_fst_906_ = lean_ctor_get(v_val_902_, 0);
lean_inc(v_fst_906_);
lean_dec(v_val_902_);
v___x_907_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f_spec__0(v_fst_906_);
v___x_908_ = l_Rat_div(v_val_895_, v___x_907_);
lean_dec(v_val_895_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_908_);
v___x_910_ = v___x_904_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_912_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_910_);
v___x_912_ = v___x_900_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_918_; 
lean_dec(v_a_898_);
lean_dec(v_val_895_);
v___x_916_ = lean_box(0);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_916_);
v___x_918_ = v___x_900_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v_val_895_);
v_a_921_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_897_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_897_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v___x_929_; lean_object* v___x_931_; 
lean_dec(v_a_891_);
lean_dec_ref(v_arg_873_);
v___x_929_ = lean_box(0);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_929_);
v___x_931_ = v___x_893_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_dec_ref(v_arg_873_);
return v___x_890_;
}
}
}
}
}
}
else
{
lean_object* v___x_934_; 
lean_dec_ref(v___x_874_);
lean_dec_ref(v___x_867_);
lean_dec_ref(v_e_856_);
v___x_934_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_arg_873_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_955_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_955_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_955_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_955_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
if (lean_obj_tag(v_a_935_) == 1)
{
lean_object* v_val_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_950_; 
v_val_939_ = lean_ctor_get(v_a_935_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_950_ == 0)
{
v___x_941_ = v_a_935_;
v_isShared_942_ = v_isSharedCheck_950_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_val_939_);
lean_dec(v_a_935_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_950_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = l_Rat_neg(v_val_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_947_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_945_);
v___x_947_ = v___x_937_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec(v_a_935_);
v___x_951_ = lean_box(0);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_951_);
v___x_953_ = v___x_937_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
return v___x_934_;
}
}
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_e_856_);
v_a_956_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_862_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_862_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getRatValue_x3f___boxed(lean_object* v_e_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Meta_getRatValue_x3f(v_e_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f(lean_object* v_e_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_975_, v_a_977_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = l_Lean_Expr_cleanupAnnotations(v_a_985_);
lean_dec(v_a_985_);
v___x_987_ = l_Lean_Expr_isApp(v___x_986_);
if (v___x_987_ == 0)
{
lean_dec_ref(v___x_986_);
goto v___jp_981_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_988_ = l_Lean_Expr_appFnCleanup___redArg(v___x_986_);
v___x_989_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_990_ = l_Lean_Expr_isConstOf(v___x_988_, v___x_989_);
lean_dec_ref(v___x_988_);
if (v___x_990_ == 0)
{
lean_dec_ref(v___x_986_);
goto v___jp_981_;
}
else
{
lean_object* v_arg_991_; lean_object* v___x_992_; 
v_arg_991_ = lean_ctor_get(v___x_986_, 1);
lean_inc_ref(v_arg_991_);
lean_dec_ref(v___x_986_);
v___x_992_ = l_Lean_Meta_getNatValue_x3f(v_arg_991_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
lean_dec_ref(v_arg_991_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1014_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1014_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1014_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
if (lean_obj_tag(v_a_993_) == 1)
{
lean_object* v_val_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1009_; 
v_val_997_ = lean_ctor_get(v_a_993_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_a_993_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_999_ = v_a_993_;
v_isShared_1000_ = v_isSharedCheck_1009_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_val_997_);
lean_dec(v_a_993_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1009_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
uint32_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1001_ = l_Char_ofNat(v_val_997_);
lean_dec(v_val_997_);
v___x_1002_ = lean_box_uint32(v___x_1001_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1002_);
v___x_1004_ = v___x_999_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1006_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1004_);
v___x_1006_ = v___x_995_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
lean_dec(v_a_993_);
v___x_1010_ = lean_box(0);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1010_);
v___x_1012_ = v___x_995_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_992_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_992_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_984_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_984_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
v___jp_981_:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_box(0);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f___boxed(lean_object* v_e_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Meta_getCharValue_x3f(v_e_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStringValue_x3f(lean_object* v_e_1038_){
_start:
{
if (lean_obj_tag(v_e_1038_) == 9)
{
lean_object* v_a_1039_; 
v_a_1039_ = lean_ctor_get(v_e_1038_, 0);
lean_inc_ref(v_a_1039_);
lean_dec_ref_known(v_e_1038_, 1);
if (lean_obj_tag(v_a_1039_) == 1)
{
lean_object* v_val_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
v_val_1040_ = lean_ctor_get(v_a_1039_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_a_1039_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v_a_1039_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_val_1040_);
lean_dec(v_a_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_val_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
else
{
lean_object* v___x_1048_; 
lean_dec_ref(v_a_1039_);
v___x_1048_ = lean_box(0);
return v___x_1048_;
}
}
else
{
lean_object* v___x_1049_; 
lean_dec_ref(v_e_1038_);
v___x_1049_ = lean_box(0);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f(lean_object* v_e_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_1060_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1053_, v___x_1059_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1129_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1129_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1129_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
if (lean_obj_tag(v_a_1061_) == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = lean_box(0);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
else
{
lean_object* v_val_1069_; lean_object* v_fst_1070_; lean_object* v_snd_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1128_; 
lean_del_object(v___x_1063_);
v_val_1069_ = lean_ctor_get(v_a_1061_, 0);
lean_inc(v_val_1069_);
lean_dec_ref_known(v_a_1061_, 1);
v_fst_1070_ = lean_ctor_get(v_val_1069_, 0);
v_snd_1071_ = lean_ctor_get(v_val_1069_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_val_1069_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1073_ = v_val_1069_;
v_isShared_1074_ = v_isSharedCheck_1128_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_snd_1071_);
lean_inc(v_fst_1070_);
lean_dec(v_val_1069_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1128_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = l_Lean_Expr_appArg_x21(v_snd_1071_);
lean_dec(v_snd_1071_);
v___x_1076_ = l_Lean_Meta_whnfD(v___x_1075_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1078_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = l_Lean_Meta_getNatValue_x3f(v_a_1077_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1111_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1111_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1111_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
if (lean_obj_tag(v_a_1079_) == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
lean_del_object(v___x_1073_);
lean_dec(v_fst_1070_);
v___x_1083_ = lean_box(0);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1083_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
else
{
lean_object* v_val_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1110_; 
v_val_1087_ = lean_ctor_get(v_a_1079_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_a_1079_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1089_ = v_a_1079_;
v_isShared_1090_ = v_isSharedCheck_1110_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_val_1087_);
lean_dec(v_a_1079_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1110_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_zero_1091_; uint8_t v_isZero_1092_; 
v_zero_1091_ = lean_unsigned_to_nat(0u);
v_isZero_1092_ = lean_nat_dec_eq(v_val_1087_, v_zero_1091_);
if (v_isZero_1092_ == 1)
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_del_object(v___x_1089_);
lean_dec(v_val_1087_);
lean_del_object(v___x_1073_);
lean_dec(v_fst_1070_);
v___x_1093_ = lean_box(0);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1093_);
v___x_1095_ = v___x_1081_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
else
{
lean_object* v_one_1097_; lean_object* v_n_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v_one_1097_ = lean_unsigned_to_nat(1u);
v_n_1098_ = lean_nat_sub(v_val_1087_, v_one_1097_);
lean_dec(v_val_1087_);
v___x_1099_ = lean_nat_add(v_n_1098_, v_one_1097_);
lean_dec(v_n_1098_);
v___x_1100_ = lean_nat_mod(v_fst_1070_, v___x_1099_);
lean_dec(v_fst_1070_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v___x_1100_);
lean_ctor_set(v___x_1073_, 0, v___x_1099_);
v___x_1102_ = v___x_1073_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1104_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1102_);
v___x_1104_ = v___x_1089_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1104_);
v___x_1106_ = v___x_1081_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
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
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_del_object(v___x_1073_);
lean_dec(v_fst_1070_);
v_a_1112_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1078_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1078_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_del_object(v___x_1073_);
lean_dec(v_fst_1070_);
v_a_1120_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1076_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1076_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v_a_1130_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1060_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1060_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f___boxed(lean_object* v_e_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Meta_getFinValue_x3f(v_e_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object* v_e_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v_nExpr_1237_; lean_object* v_vExpr_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___x_1293_; 
lean_inc_ref(v_e_1155_);
v___x_1293_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1155_, v_a_1157_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = l_Lean_Expr_cleanupAnnotations(v_a_1294_);
lean_dec(v_a_1294_);
v___x_1296_ = l_Lean_Expr_isApp(v___x_1295_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v___x_1295_);
v___y_1162_ = v_a_1156_;
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1295_);
v___x_1298_ = l_Lean_Expr_isApp(v___x_1297_);
if (v___x_1298_ == 0)
{
lean_dec_ref(v___x_1297_);
lean_dec_ref(v___x_1295_);
v___y_1162_ = v_a_1156_;
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
goto v___jp_1161_;
}
else
{
lean_object* v_arg_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_arg_1299_ = lean_ctor_get(v___x_1297_, 1);
lean_inc_ref(v_arg_1299_);
v___x_1300_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1297_);
lean_dec_ref(v___x_1297_);
v___x_1301_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_1302_ = l_Lean_Expr_isConstOf(v___x_1300_, v___x_1301_);
if (v___x_1302_ == 0)
{
uint8_t v___x_1303_; 
lean_dec_ref(v___x_1295_);
v___x_1303_ = l_Lean_Expr_isApp(v___x_1300_);
if (v___x_1303_ == 0)
{
lean_dec_ref(v___x_1300_);
lean_dec_ref(v_arg_1299_);
v___y_1162_ = v_a_1156_;
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1300_);
v___x_1305_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__4));
v___x_1306_ = l_Lean_Expr_isConstOf(v___x_1304_, v___x_1305_);
lean_dec_ref(v___x_1304_);
if (v___x_1306_ == 0)
{
lean_dec_ref(v___x_1300_);
lean_dec_ref(v_arg_1299_);
v___y_1162_ = v_a_1156_;
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
goto v___jp_1161_;
}
else
{
lean_object* v_arg_1307_; 
lean_dec_ref(v_e_1155_);
v_arg_1307_ = lean_ctor_get(v___x_1300_, 1);
lean_inc_ref(v_arg_1307_);
lean_dec_ref(v___x_1300_);
v_nExpr_1237_ = v_arg_1307_;
v_vExpr_1238_ = v_arg_1299_;
v___y_1239_ = v_a_1156_;
v___y_1240_ = v_a_1157_;
v___y_1241_ = v_a_1158_;
v___y_1242_ = v_a_1159_;
goto v___jp_1236_;
}
}
}
else
{
lean_object* v_arg_1308_; 
lean_dec_ref(v___x_1300_);
lean_dec_ref(v_e_1155_);
v_arg_1308_ = lean_ctor_get(v___x_1295_, 1);
lean_inc_ref(v_arg_1308_);
lean_dec_ref(v___x_1295_);
v_nExpr_1237_ = v_arg_1299_;
v_vExpr_1238_ = v_arg_1308_;
v___y_1239_ = v_a_1156_;
v___y_1240_ = v_a_1157_;
v___y_1241_ = v_a_1158_;
v___y_1242_ = v_a_1159_;
goto v___jp_1236_;
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v_e_1155_);
v_a_1309_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1293_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1293_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
v___jp_1161_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_1167_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1155_, v___x_1166_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1227_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1227_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1227_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
if (lean_obj_tag(v_a_1168_) == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = lean_box(0);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1172_);
v___x_1174_ = v___x_1170_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
else
{
lean_object* v_val_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1226_; 
lean_del_object(v___x_1170_);
v_val_1176_ = lean_ctor_get(v_a_1168_, 0);
lean_inc(v_val_1176_);
lean_dec_ref_known(v_a_1168_, 1);
v_fst_1177_ = lean_ctor_get(v_val_1176_, 0);
v_snd_1178_ = lean_ctor_get(v_val_1176_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_val_1176_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1180_ = v_val_1176_;
v_isShared_1181_ = v_isSharedCheck_1226_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snd_1178_);
lean_inc(v_fst_1177_);
lean_dec(v_val_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1226_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = l_Lean_Expr_appArg_x21(v_snd_1178_);
lean_dec(v_snd_1178_);
v___x_1183_ = l_Lean_Meta_whnfD(v___x_1182_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = l_Lean_Meta_getNatValue_x3f(v_a_1184_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v_a_1184_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1209_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1209_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1209_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
if (lean_obj_tag(v_a_1186_) == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
lean_del_object(v___x_1180_);
lean_dec(v_fst_1177_);
v___x_1190_ = lean_box(0);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
else
{
lean_object* v_val_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1208_; 
v_val_1194_ = lean_ctor_get(v_a_1186_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_a_1186_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1196_ = v_a_1186_;
v_isShared_1197_ = v_isSharedCheck_1208_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_val_1194_);
lean_dec(v_a_1186_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1208_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = l_BitVec_ofNat(v_val_1194_, v_fst_1177_);
lean_dec(v_fst_1177_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1198_);
lean_ctor_set(v___x_1180_, 0, v_val_1194_);
v___x_1200_ = v___x_1180_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_val_1194_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1200_);
v___x_1202_ = v___x_1196_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1202_);
v___x_1204_ = v___x_1188_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_del_object(v___x_1180_);
lean_dec(v_fst_1177_);
v_a_1210_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1185_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1185_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_del_object(v___x_1180_);
lean_dec(v_fst_1177_);
v_a_1218_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1183_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1183_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_a_1228_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1167_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1167_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
v___jp_1236_:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_Meta_getNatValue_x3f(v_nExpr_1237_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec_ref(v_nExpr_1237_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1284_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1284_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1284_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
if (lean_obj_tag(v_a_1244_) == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
lean_dec_ref(v_vExpr_1238_);
v___x_1248_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1248_);
v___x_1250_ = v___x_1246_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
else
{
lean_object* v_val_1252_; lean_object* v___x_1253_; 
lean_del_object(v___x_1246_);
v_val_1252_ = lean_ctor_get(v_a_1244_, 0);
lean_inc(v_val_1252_);
lean_dec_ref_known(v_a_1244_, 1);
v___x_1253_ = l_Lean_Meta_getNatValue_x3f(v_vExpr_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec_ref(v_vExpr_1238_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1275_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1275_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1275_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
if (lean_obj_tag(v_a_1254_) == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
lean_dec(v_val_1252_);
v___x_1258_ = lean_box(0);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1258_);
v___x_1260_ = v___x_1256_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
else
{
lean_object* v_val_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1274_; 
v_val_1262_ = lean_ctor_get(v_a_1254_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_a_1254_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1264_ = v_a_1254_;
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_val_1262_);
lean_dec(v_a_1254_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1266_ = l_BitVec_ofNat(v_val_1252_, v_val_1262_);
lean_dec(v_val_1262_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_val_1252_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1267_);
v___x_1269_ = v___x_1264_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1271_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1269_);
v___x_1271_ = v___x_1256_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_val_1252_);
v_a_1276_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1253_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1253_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_vExpr_1238_);
v_a_1285_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1243_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1243_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f___boxed(lean_object* v_e_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Meta_getBitVecValue_x3f(v_e_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
return v_res_1323_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__0(void){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1324_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__1(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__0, &l_Lean_Meta_getLitValueModulus_x3f___closed__0_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__0);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
return v___x_1326_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__2(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_cstr_to_nat("4294967296");
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLitValueModulus_x3f(lean_object* v_00_u03b1_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03b1_1357_, v_a_1359_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = l_Lean_Expr_cleanupAnnotations(v_a_1379_);
lean_dec(v_a_1379_);
v___x_1381_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_1382_ = l_Lean_Expr_isConstOf(v___x_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_1384_ = l_Lean_Expr_isConstOf(v___x_1380_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_1386_ = l_Lean_Expr_isConstOf(v___x_1380_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_1388_ = l_Lean_Expr_isConstOf(v___x_1380_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_1390_ = l_Lean_Expr_isConstOf(v___x_1380_, v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_1392_ = l_Lean_Expr_isConstOf(v___x_1380_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_1394_ = l_Lean_Expr_isConstOf(v___x_1380_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_1396_ = l_Lean_Expr_isConstOf(v___x_1380_, v___x_1395_);
if (v___x_1396_ == 0)
{
uint8_t v___x_1397_; 
v___x_1397_ = l_Lean_Expr_isApp(v___x_1380_);
if (v___x_1397_ == 0)
{
lean_dec_ref(v___x_1380_);
goto v___jp_1375_;
}
else
{
lean_object* v_arg_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v_arg_1398_ = lean_ctor_get(v___x_1380_, 1);
lean_inc_ref(v_arg_1398_);
v___x_1399_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1380_);
lean_dec_ref(v___x_1380_);
v___x_1400_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_1401_ = l_Lean_Expr_isConstOf(v___x_1399_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_1403_ = l_Lean_Expr_isConstOf(v___x_1399_, v___x_1402_);
lean_dec_ref(v___x_1399_);
if (v___x_1403_ == 0)
{
lean_dec_ref(v_arg_1398_);
goto v___jp_1375_;
}
else
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_Meta_getNatValue_x3f(v_arg_1398_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
lean_dec_ref(v_arg_1398_);
return v___x_1404_;
}
}
else
{
lean_object* v___x_1405_; 
lean_dec_ref(v___x_1399_);
v___x_1405_ = l_Lean_Meta_getNatValue_x3f(v_arg_1398_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
lean_dec_ref(v_arg_1398_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1427_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1427_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1427_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
if (lean_obj_tag(v_a_1406_) == 1)
{
lean_object* v_val_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1422_; 
v_val_1410_ = lean_ctor_get(v_a_1406_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_a_1406_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1412_ = v_a_1406_;
v_isShared_1413_ = v_isSharedCheck_1422_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_val_1410_);
lean_dec(v_a_1406_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1422_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1414_ = lean_unsigned_to_nat(2u);
v___x_1415_ = lean_nat_pow(v___x_1414_, v_val_1410_);
lean_dec(v_val_1410_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1415_);
v___x_1417_ = v___x_1412_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1417_);
v___x_1419_ = v___x_1408_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
lean_dec(v_a_1406_);
v___x_1423_ = lean_box(0);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1423_);
v___x_1425_ = v___x_1408_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
else
{
return v___x_1405_;
}
}
}
}
else
{
lean_dec_ref(v___x_1380_);
goto v___jp_1372_;
}
}
else
{
lean_dec_ref(v___x_1380_);
goto v___jp_1369_;
}
}
else
{
lean_dec_ref(v___x_1380_);
goto v___jp_1366_;
}
}
else
{
lean_dec_ref(v___x_1380_);
goto v___jp_1363_;
}
}
else
{
lean_dec_ref(v___x_1380_);
goto v___jp_1372_;
}
}
else
{
lean_dec_ref(v___x_1380_);
goto v___jp_1369_;
}
}
else
{
lean_dec_ref(v___x_1380_);
goto v___jp_1366_;
}
}
else
{
lean_dec_ref(v___x_1380_);
goto v___jp_1363_;
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
v_a_1428_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1378_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1378_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
v___jp_1363_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__1, &l_Lean_Meta_getLitValueModulus_x3f___closed__1_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__1);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
v___jp_1366_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__2, &l_Lean_Meta_getLitValueModulus_x3f___closed__2_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__2);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
v___jp_1369_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__3));
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
v___jp_1372_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__4));
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
v___jp_1375_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLitValueModulus_x3f___boxed(lean_object* v_00_u03b1_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Meta_getLitValueModulus_x3f(v_00_u03b1_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object* v_e_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_1450_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1443_, v___x_1449_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1473_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1473_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1473_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
if (lean_obj_tag(v_a_1451_) == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_box(0);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
else
{
lean_object* v_val_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1472_; 
v_val_1459_ = lean_ctor_get(v_a_1451_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_a_1451_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1461_ = v_a_1451_;
v_isShared_1462_ = v_isSharedCheck_1472_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_val_1459_);
lean_dec(v_a_1451_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1472_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_fst_1463_; uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
v_fst_1463_ = lean_ctor_get(v_val_1459_, 0);
lean_inc(v_fst_1463_);
lean_dec(v_val_1459_);
v___x_1464_ = lean_uint8_of_nat(v_fst_1463_);
lean_dec(v_fst_1463_);
v___x_1465_ = lean_box(v___x_1464_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1465_);
v___x_1467_ = v___x_1461_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1469_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1467_);
v___x_1469_ = v___x_1453_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_a_1474_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1450_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1450_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f___boxed(lean_object* v_e_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Meta_getUInt8Value_x3f(v_e_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object* v_e_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_1496_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1489_, v___x_1495_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1519_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1519_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1519_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
if (lean_obj_tag(v_a_1497_) == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = lean_box(0);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1501_);
v___x_1503_ = v___x_1499_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
else
{
lean_object* v_val_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1518_; 
v_val_1505_ = lean_ctor_get(v_a_1497_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_a_1497_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1507_ = v_a_1497_;
v_isShared_1508_ = v_isSharedCheck_1518_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_val_1505_);
lean_dec(v_a_1497_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1518_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v_fst_1509_; uint16_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v_fst_1509_ = lean_ctor_get(v_val_1505_, 0);
lean_inc(v_fst_1509_);
lean_dec(v_val_1505_);
v___x_1510_ = lean_uint16_of_nat(v_fst_1509_);
lean_dec(v_fst_1509_);
v___x_1511_ = lean_box(v___x_1510_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1511_);
v___x_1513_ = v___x_1507_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1515_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1513_);
v___x_1515_ = v___x_1499_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
v_a_1520_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1496_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1496_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f___boxed(lean_object* v_e_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Meta_getUInt16Value_x3f(v_e_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object* v_e_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_1542_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1535_, v___x_1541_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1565_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1565_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1565_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
if (lean_obj_tag(v_a_1543_) == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = lean_box(0);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1547_);
v___x_1549_ = v___x_1545_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
else
{
lean_object* v_val_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1564_; 
v_val_1551_ = lean_ctor_get(v_a_1543_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_a_1543_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1553_ = v_a_1543_;
v_isShared_1554_ = v_isSharedCheck_1564_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_val_1551_);
lean_dec(v_a_1543_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1564_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_fst_1555_; uint32_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v_fst_1555_ = lean_ctor_get(v_val_1551_, 0);
lean_inc(v_fst_1555_);
lean_dec(v_val_1551_);
v___x_1556_ = lean_uint32_of_nat(v_fst_1555_);
lean_dec(v_fst_1555_);
v___x_1557_ = lean_box_uint32(v___x_1556_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1557_);
v___x_1559_ = v___x_1553_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1561_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1559_);
v___x_1561_ = v___x_1545_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
v_a_1566_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1542_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1542_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f___boxed(lean_object* v_e_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Meta_getUInt32Value_x3f(v_e_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object* v_e_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_1588_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1581_, v___x_1587_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1611_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1611_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1611_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
if (lean_obj_tag(v_a_1589_) == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1593_ = lean_box(0);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1593_);
v___x_1595_ = v___x_1591_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1610_; 
v_val_1597_ = lean_ctor_get(v_a_1589_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_a_1589_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1599_ = v_a_1589_;
v_isShared_1600_ = v_isSharedCheck_1610_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_val_1597_);
lean_dec(v_a_1589_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1610_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_fst_1601_; uint64_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v_fst_1601_ = lean_ctor_get(v_val_1597_, 0);
lean_inc(v_fst_1601_);
lean_dec(v_val_1597_);
v___x_1602_ = lean_uint64_of_nat(v_fst_1601_);
lean_dec(v_fst_1601_);
v___x_1603_ = lean_box_uint64(v___x_1602_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1603_);
v___x_1605_ = v___x_1599_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1605_);
v___x_1607_ = v___x_1591_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1588_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1588_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f___boxed(lean_object* v_e_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Meta_getUInt64Value_x3f(v_e_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(lean_object* v_e_1627_, lean_object* v_typeDeclName_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___x_1670_; 
lean_inc_ref(v_e_1627_);
v___x_1670_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1627_, v_a_1630_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1672_ = l_Lean_Expr_cleanupAnnotations(v_a_1671_);
lean_dec(v_a_1671_);
v___x_1673_ = l_Lean_Expr_isApp(v___x_1672_);
if (v___x_1673_ == 0)
{
lean_dec_ref(v___x_1672_);
v___y_1635_ = v_a_1629_;
v___y_1636_ = v_a_1630_;
v___y_1637_ = v_a_1631_;
v___y_1638_ = v_a_1632_;
goto v___jp_1634_;
}
else
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1672_);
v___x_1675_ = l_Lean_Expr_isApp(v___x_1674_);
if (v___x_1675_ == 0)
{
lean_dec_ref(v___x_1674_);
lean_dec_ref(v___x_1672_);
v___y_1635_ = v_a_1629_;
v___y_1636_ = v_a_1630_;
v___y_1637_ = v_a_1631_;
v___y_1638_ = v_a_1632_;
goto v___jp_1634_;
}
else
{
lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1676_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1674_);
lean_dec_ref(v___x_1674_);
v___x_1677_ = l_Lean_Expr_isApp(v___x_1676_);
if (v___x_1677_ == 0)
{
lean_dec_ref(v___x_1676_);
lean_dec_ref(v___x_1672_);
v___y_1635_ = v_a_1629_;
v___y_1636_ = v_a_1630_;
v___y_1637_ = v_a_1631_;
v___y_1638_ = v_a_1632_;
goto v___jp_1634_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1678_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1676_);
lean_dec_ref(v___x_1676_);
v___x_1679_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1680_ = l_Lean_Expr_isConstOf(v___x_1678_, v___x_1679_);
lean_dec_ref(v___x_1678_);
if (v___x_1680_ == 0)
{
lean_dec_ref(v___x_1672_);
v___y_1635_ = v_a_1629_;
v___y_1636_ = v_a_1630_;
v___y_1637_ = v_a_1631_;
v___y_1638_ = v_a_1632_;
goto v___jp_1634_;
}
else
{
lean_object* v_arg_1681_; lean_object* v___x_1682_; 
lean_dec_ref(v_e_1627_);
v_arg_1681_ = lean_ctor_get(v___x_1672_, 1);
lean_inc_ref(v_arg_1681_);
lean_dec_ref(v___x_1672_);
v___x_1682_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_1681_, v_typeDeclName_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1705_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1705_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1705_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
if (lean_obj_tag(v_a_1683_) == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_box(0);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1687_);
v___x_1689_ = v___x_1685_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
else
{
lean_object* v_val_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1704_; 
v_val_1691_ = lean_ctor_get(v_a_1683_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_a_1683_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1693_ = v_a_1683_;
v_isShared_1694_ = v_isSharedCheck_1704_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_val_1691_);
lean_dec(v_a_1683_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1704_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_fst_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v_fst_1695_ = lean_ctor_get(v_val_1691_, 0);
lean_inc(v_fst_1695_);
lean_dec(v_val_1691_);
v___x_1696_ = lean_nat_to_int(v_fst_1695_);
v___x_1697_ = lean_int_neg(v___x_1696_);
lean_dec(v___x_1696_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1697_);
v___x_1699_ = v___x_1693_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1701_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1699_);
v___x_1701_ = v___x_1685_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
v_a_1706_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1682_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1682_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
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
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref(v_e_1627_);
v_a_1714_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1670_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1670_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
v___jp_1634_:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1627_, v_typeDeclName_1628_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1661_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1661_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1661_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
if (lean_obj_tag(v_a_1640_) == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_box(0);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1644_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
else
{
lean_object* v_val_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1660_; 
v_val_1648_ = lean_ctor_get(v_a_1640_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_a_1640_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1650_ = v_a_1640_;
v_isShared_1651_ = v_isSharedCheck_1660_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_val_1648_);
lean_dec(v_a_1640_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1660_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v_fst_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
v_fst_1652_ = lean_ctor_get(v_val_1648_, 0);
lean_inc(v_fst_1652_);
lean_dec(v_val_1648_);
v___x_1653_ = lean_nat_to_int(v_fst_1652_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1653_);
v___x_1655_ = v___x_1650_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1657_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1655_);
v___x_1657_ = v___x_1642_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1639_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1639_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f___boxed(lean_object* v_e_1722_, lean_object* v_typeDeclName_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1722_, v_typeDeclName_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_typeDeclName_1723_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt8Value_x3f(lean_object* v_e_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_1737_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1730_, v___x_1736_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1759_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1759_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1759_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
if (lean_obj_tag(v_a_1738_) == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1742_ = lean_box(0);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1742_);
v___x_1744_ = v___x_1740_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
else
{
lean_object* v_val_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1758_; 
v_val_1746_ = lean_ctor_get(v_a_1738_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_a_1738_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1748_ = v_a_1738_;
v_isShared_1749_ = v_isSharedCheck_1758_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_val_1746_);
lean_dec(v_a_1738_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1758_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1750_ = lean_int8_of_int(v_val_1746_);
lean_dec(v_val_1746_);
v___x_1751_ = lean_box(v___x_1750_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1751_);
v___x_1753_ = v___x_1748_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1755_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1753_);
v___x_1755_ = v___x_1740_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
v_a_1760_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1737_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1737_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt8Value_x3f___boxed(lean_object* v_e_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Meta_getInt8Value_x3f(v_e_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt16Value_x3f(lean_object* v_e_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_1782_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1775_, v___x_1781_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1804_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1804_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1804_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
if (lean_obj_tag(v_a_1783_) == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1787_ = lean_box(0);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1787_);
v___x_1789_ = v___x_1785_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
else
{
lean_object* v_val_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1803_; 
v_val_1791_ = lean_ctor_get(v_a_1783_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_a_1783_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1793_ = v_a_1783_;
v_isShared_1794_ = v_isSharedCheck_1803_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_val_1791_);
lean_dec(v_a_1783_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1803_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
uint16_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1795_ = lean_int16_of_int(v_val_1791_);
lean_dec(v_val_1791_);
v___x_1796_ = lean_box(v___x_1795_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1796_);
v___x_1798_ = v___x_1793_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1800_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1798_);
v___x_1800_ = v___x_1785_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
v_a_1805_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1782_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1782_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt16Value_x3f___boxed(lean_object* v_e_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_Meta_getInt16Value_x3f(v_e_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt32Value_x3f(lean_object* v_e_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_1827_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1820_, v___x_1826_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1849_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1849_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1849_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
if (lean_obj_tag(v_a_1828_) == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1832_ = lean_box(0);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1832_);
v___x_1834_ = v___x_1830_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
else
{
lean_object* v_val_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1848_; 
v_val_1836_ = lean_ctor_get(v_a_1828_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_a_1828_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1838_ = v_a_1828_;
v_isShared_1839_ = v_isSharedCheck_1848_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_val_1836_);
lean_dec(v_a_1828_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1848_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
uint32_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1840_ = lean_int32_of_int(v_val_1836_);
lean_dec(v_val_1836_);
v___x_1841_ = lean_box_uint32(v___x_1840_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1843_);
v___x_1845_ = v___x_1830_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1827_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1827_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt32Value_x3f___boxed(lean_object* v_e_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Meta_getInt32Value_x3f(v_e_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt64Value_x3f(lean_object* v_e_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_1872_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1865_, v___x_1871_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1894_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1894_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1894_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
if (lean_obj_tag(v_a_1873_) == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1877_ = lean_box(0);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1877_);
v___x_1879_ = v___x_1875_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
else
{
lean_object* v_val_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1893_; 
v_val_1881_ = lean_ctor_get(v_a_1873_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_a_1873_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1883_ = v_a_1873_;
v_isShared_1884_ = v_isSharedCheck_1893_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_val_1881_);
lean_dec(v_a_1873_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1893_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
uint64_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1885_ = lean_int64_of_int(v_val_1881_);
lean_dec(v_val_1881_);
v___x_1886_ = lean_box_uint64(v___x_1885_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1886_);
v___x_1888_ = v___x_1883_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1888_);
v___x_1890_ = v___x_1875_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_a_1895_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1872_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1872_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt64Value_x3f___boxed(lean_object* v_e_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Meta_getInt64Value_x3f(v_e_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(lean_object* v_e_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___x_1957_; 
lean_inc_ref(v_e_1913_);
v___x_1957_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1913_, v_a_1915_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1959_ = l_Lean_Expr_cleanupAnnotations(v_a_1958_);
lean_dec(v_a_1958_);
v___x_1960_ = l_Lean_Expr_isApp(v___x_1959_);
if (v___x_1960_ == 0)
{
lean_dec_ref(v___x_1959_);
v___y_1920_ = v_a_1914_;
v___y_1921_ = v_a_1915_;
v___y_1922_ = v_a_1916_;
v___y_1923_ = v_a_1917_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1959_);
v___x_1962_ = l_Lean_Expr_isApp(v___x_1961_);
if (v___x_1962_ == 0)
{
lean_dec_ref(v___x_1961_);
lean_dec_ref(v___x_1959_);
v___y_1920_ = v_a_1914_;
v___y_1921_ = v_a_1915_;
v___y_1922_ = v_a_1916_;
v___y_1923_ = v_a_1917_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1961_);
v___x_1964_ = l_Lean_Expr_isApp(v___x_1963_);
if (v___x_1964_ == 0)
{
lean_dec_ref(v___x_1963_);
lean_dec_ref(v___x_1961_);
lean_dec_ref(v___x_1959_);
v___y_1920_ = v_a_1914_;
v___y_1921_ = v_a_1915_;
v___y_1922_ = v_a_1916_;
v___y_1923_ = v_a_1917_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1963_);
v___x_1966_ = l_Lean_Expr_isApp(v___x_1965_);
if (v___x_1966_ == 0)
{
lean_dec_ref(v___x_1965_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v___x_1961_);
lean_dec_ref(v___x_1959_);
v___y_1920_ = v_a_1914_;
v___y_1921_ = v_a_1915_;
v___y_1922_ = v_a_1916_;
v___y_1923_ = v_a_1917_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1965_);
lean_dec_ref(v___x_1965_);
v___x_1968_ = l_Lean_Expr_isApp(v___x_1967_);
if (v___x_1968_ == 0)
{
lean_dec_ref(v___x_1967_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v___x_1961_);
lean_dec_ref(v___x_1959_);
v___y_1920_ = v_a_1914_;
v___y_1921_ = v_a_1915_;
v___y_1922_ = v_a_1916_;
v___y_1923_ = v_a_1917_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1969_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1967_);
v___x_1970_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_1971_ = l_Lean_Expr_isConstOf(v___x_1969_, v___x_1970_);
lean_dec_ref(v___x_1969_);
if (v___x_1971_ == 0)
{
lean_dec_ref(v___x_1967_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v___x_1961_);
lean_dec_ref(v___x_1959_);
v___y_1920_ = v_a_1914_;
v___y_1921_ = v_a_1915_;
v___y_1922_ = v_a_1916_;
v___y_1923_ = v_a_1917_;
goto v___jp_1919_;
}
else
{
lean_object* v_arg_1972_; lean_object* v_arg_1973_; lean_object* v_arg_1974_; lean_object* v_arg_1975_; lean_object* v___x_1976_; 
lean_dec_ref(v_e_1913_);
v_arg_1972_ = lean_ctor_get(v___x_1959_, 1);
lean_inc_ref(v_arg_1972_);
lean_dec_ref(v___x_1959_);
v_arg_1973_ = lean_ctor_get(v___x_1961_, 1);
lean_inc_ref(v_arg_1973_);
lean_dec_ref(v___x_1961_);
v_arg_1974_ = lean_ctor_get(v___x_1963_, 1);
lean_inc_ref(v_arg_1974_);
lean_dec_ref(v___x_1963_);
v_arg_1975_ = lean_ctor_get(v___x_1967_, 1);
lean_inc_ref(v_arg_1975_);
lean_dec_ref(v___x_1967_);
v___x_1976_ = l_Lean_Meta_whnfD(v_arg_1975_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2044_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_2044_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2044_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1982_ = l_Lean_Expr_isConstOf(v_a_1977_, v___x_1981_);
lean_dec(v_a_1977_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_dec_ref(v_arg_1974_);
lean_dec_ref(v_arg_1973_);
lean_dec_ref(v_arg_1972_);
v___x_1983_ = lean_box(0);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1983_);
v___x_1985_ = v___x_1979_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
else
{
lean_object* v___x_1987_; 
v___x_1987_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_1973_);
lean_dec_ref(v_arg_1973_);
if (lean_obj_tag(v___x_1987_) == 1)
{
lean_object* v_val_1988_; lean_object* v___x_1989_; 
lean_del_object(v___x_1979_);
v_val_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_val_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v___x_1989_ = l_Lean_Meta_getNatValue_x3f(v_arg_1974_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
lean_dec_ref(v_arg_1974_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2031_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2031_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2031_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
if (lean_obj_tag(v_a_1990_) == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
lean_dec(v_val_1988_);
lean_dec_ref(v_arg_1972_);
v___x_1994_ = lean_box(0);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1994_);
v___x_1996_ = v___x_1992_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
else
{
lean_object* v_val_1998_; lean_object* v___x_1999_; 
lean_del_object(v___x_1992_);
v_val_1998_ = lean_ctor_get(v_a_1990_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v_a_1990_, 1);
v___x_1999_ = l_Lean_Meta_getNatValue_x3f(v_arg_1972_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
lean_dec_ref(v_arg_1972_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2022_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2022_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2022_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
if (lean_obj_tag(v_a_2000_) == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2006_; 
lean_dec(v_val_1998_);
lean_dec(v_val_1988_);
v___x_2004_ = lean_box(0);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2004_);
v___x_2006_ = v___x_2002_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
else
{
lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2021_; 
v_val_2008_ = lean_ctor_get(v_a_2000_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_a_2000_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2010_ = v_a_2000_;
v_isShared_2011_ = v_isSharedCheck_2021_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_dec(v_a_2000_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2021_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
uint8_t v___x_2012_; double v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2012_ = lean_unbox(v_val_1988_);
lean_dec(v_val_1988_);
v___x_2013_ = l_Float_ofScientific(v_val_1998_, v___x_2012_, v_val_2008_);
v___x_2014_ = lean_box_float(v___x_2013_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2014_);
v___x_2016_ = v___x_2010_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2018_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2016_);
v___x_2018_ = v___x_2002_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec(v_val_1998_);
lean_dec(v_val_1988_);
v_a_2023_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1999_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1999_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_val_1988_);
lean_dec_ref(v_arg_1972_);
v_a_2032_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1989_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1989_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
lean_dec(v___x_1987_);
lean_dec_ref(v_arg_1974_);
lean_dec_ref(v_arg_1972_);
v___x_2040_ = lean_box(0);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_2040_);
v___x_2042_ = v___x_1979_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v_arg_1974_);
lean_dec_ref(v_arg_1973_);
lean_dec_ref(v_arg_1972_);
v_a_2045_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_1976_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_1976_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
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
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v_e_1913_);
v_a_2053_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_1957_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_1957_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
v___jp_1919_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1925_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1913_, v___x_1924_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1948_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1948_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1948_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
if (lean_obj_tag(v_a_1926_) == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = lean_box(0);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1930_);
v___x_1932_ = v___x_1928_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
else
{
lean_object* v_val_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1947_; 
v_val_1934_ = lean_ctor_get(v_a_1926_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_a_1926_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1936_ = v_a_1926_;
v_isShared_1937_ = v_isSharedCheck_1947_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_val_1934_);
lean_dec(v_a_1926_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1947_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v_fst_1938_; double v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v_fst_1938_ = lean_ctor_get(v_val_1934_, 0);
lean_inc(v_fst_1938_);
lean_dec(v_val_1934_);
v___x_1939_ = lean_float_of_nat(v_fst_1938_);
v___x_1940_ = lean_box_float(v___x_1939_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1940_);
v___x_1942_ = v___x_1936_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1944_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1942_);
v___x_1944_ = v___x_1928_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v_a_1949_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1925_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1925_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___boxed(lean_object* v_e_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f(lean_object* v_e_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v___x_2077_; 
lean_inc_ref(v_e_2068_);
v___x_2077_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
if (lean_obj_tag(v_a_2078_) == 1)
{
lean_dec_ref(v_e_2068_);
return v___x_2077_;
}
else
{
lean_object* v___x_2079_; 
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2068_, v_a_2070_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___x_2079_, 1);
v___x_2081_ = l_Lean_Expr_cleanupAnnotations(v_a_2080_);
lean_dec(v_a_2080_);
v___x_2082_ = l_Lean_Expr_isApp(v___x_2081_);
if (v___x_2082_ == 0)
{
lean_dec_ref(v___x_2081_);
goto v___jp_2074_;
}
else
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2081_);
v___x_2084_ = l_Lean_Expr_isApp(v___x_2083_);
if (v___x_2084_ == 0)
{
lean_dec_ref(v___x_2083_);
lean_dec_ref(v___x_2081_);
goto v___jp_2074_;
}
else
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2083_);
lean_dec_ref(v___x_2083_);
v___x_2086_ = l_Lean_Expr_isApp(v___x_2085_);
if (v___x_2086_ == 0)
{
lean_dec_ref(v___x_2085_);
lean_dec_ref(v___x_2081_);
goto v___jp_2074_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2085_);
lean_dec_ref(v___x_2085_);
v___x_2088_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_2089_ = l_Lean_Expr_isConstOf(v___x_2087_, v___x_2088_);
lean_dec_ref(v___x_2087_);
if (v___x_2089_ == 0)
{
lean_dec_ref(v___x_2081_);
goto v___jp_2074_;
}
else
{
lean_object* v_arg_2090_; lean_object* v___x_2091_; 
v_arg_2090_ = lean_ctor_get(v___x_2081_, 1);
lean_inc_ref(v_arg_2090_);
lean_dec_ref(v___x_2081_);
v___x_2091_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_arg_2090_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2114_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2114_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2114_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
if (lean_obj_tag(v_a_2092_) == 1)
{
lean_object* v_val_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2109_; 
v_val_2096_ = lean_ctor_get(v_a_2092_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_a_2092_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2098_ = v_a_2092_;
v_isShared_2099_ = v_isSharedCheck_2109_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_val_2096_);
lean_dec(v_a_2092_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2109_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
double v___x_2100_; double v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2100_ = lean_unbox_float(v_val_2096_);
lean_dec(v_val_2096_);
v___x_2101_ = lean_float_negate(v___x_2100_);
v___x_2102_ = lean_box_float(v___x_2101_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2102_);
v___x_2104_ = v___x_2098_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2104_);
v___x_2106_ = v___x_2094_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
lean_dec(v_a_2092_);
v___x_2110_ = lean_box(0);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2110_);
v___x_2112_ = v___x_2094_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
return v___x_2091_;
}
}
}
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
v_a_2115_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2079_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2079_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2068_);
return v___x_2077_;
}
v___jp_2074_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f___boxed(lean_object* v_e_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Meta_getFloatValue_x3f(v_e_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(lean_object* v_e_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___x_2177_; 
lean_inc_ref(v_e_2133_);
v___x_2177_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2133_, v_a_2135_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = l_Lean_Expr_cleanupAnnotations(v_a_2178_);
lean_dec(v_a_2178_);
v___x_2180_ = l_Lean_Expr_isApp(v___x_2179_);
if (v___x_2180_ == 0)
{
lean_dec_ref(v___x_2179_);
v___y_2140_ = v_a_2134_;
v___y_2141_ = v_a_2135_;
v___y_2142_ = v_a_2136_;
v___y_2143_ = v_a_2137_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2179_);
v___x_2182_ = l_Lean_Expr_isApp(v___x_2181_);
if (v___x_2182_ == 0)
{
lean_dec_ref(v___x_2181_);
lean_dec_ref(v___x_2179_);
v___y_2140_ = v_a_2134_;
v___y_2141_ = v_a_2135_;
v___y_2142_ = v_a_2136_;
v___y_2143_ = v_a_2137_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2183_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2181_);
v___x_2184_ = l_Lean_Expr_isApp(v___x_2183_);
if (v___x_2184_ == 0)
{
lean_dec_ref(v___x_2183_);
lean_dec_ref(v___x_2181_);
lean_dec_ref(v___x_2179_);
v___y_2140_ = v_a_2134_;
v___y_2141_ = v_a_2135_;
v___y_2142_ = v_a_2136_;
v___y_2143_ = v_a_2137_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2185_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2183_);
v___x_2186_ = l_Lean_Expr_isApp(v___x_2185_);
if (v___x_2186_ == 0)
{
lean_dec_ref(v___x_2185_);
lean_dec_ref(v___x_2183_);
lean_dec_ref(v___x_2181_);
lean_dec_ref(v___x_2179_);
v___y_2140_ = v_a_2134_;
v___y_2141_ = v_a_2135_;
v___y_2142_ = v_a_2136_;
v___y_2143_ = v_a_2137_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2187_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2185_);
lean_dec_ref(v___x_2185_);
v___x_2188_ = l_Lean_Expr_isApp(v___x_2187_);
if (v___x_2188_ == 0)
{
lean_dec_ref(v___x_2187_);
lean_dec_ref(v___x_2183_);
lean_dec_ref(v___x_2181_);
lean_dec_ref(v___x_2179_);
v___y_2140_ = v_a_2134_;
v___y_2141_ = v_a_2135_;
v___y_2142_ = v_a_2136_;
v___y_2143_ = v_a_2137_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2189_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2187_);
v___x_2190_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_2191_ = l_Lean_Expr_isConstOf(v___x_2189_, v___x_2190_);
lean_dec_ref(v___x_2189_);
if (v___x_2191_ == 0)
{
lean_dec_ref(v___x_2187_);
lean_dec_ref(v___x_2183_);
lean_dec_ref(v___x_2181_);
lean_dec_ref(v___x_2179_);
v___y_2140_ = v_a_2134_;
v___y_2141_ = v_a_2135_;
v___y_2142_ = v_a_2136_;
v___y_2143_ = v_a_2137_;
goto v___jp_2139_;
}
else
{
lean_object* v_arg_2192_; lean_object* v_arg_2193_; lean_object* v_arg_2194_; lean_object* v_arg_2195_; lean_object* v___x_2196_; 
lean_dec_ref(v_e_2133_);
v_arg_2192_ = lean_ctor_get(v___x_2179_, 1);
lean_inc_ref(v_arg_2192_);
lean_dec_ref(v___x_2179_);
v_arg_2193_ = lean_ctor_get(v___x_2181_, 1);
lean_inc_ref(v_arg_2193_);
lean_dec_ref(v___x_2181_);
v_arg_2194_ = lean_ctor_get(v___x_2183_, 1);
lean_inc_ref(v_arg_2194_);
lean_dec_ref(v___x_2183_);
v_arg_2195_ = lean_ctor_get(v___x_2187_, 1);
lean_inc_ref(v_arg_2195_);
lean_dec_ref(v___x_2187_);
v___x_2196_ = l_Lean_Meta_whnfD(v_arg_2195_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2264_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2264_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2264_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_2202_ = l_Lean_Expr_isConstOf(v_a_2197_, v___x_2201_);
lean_dec(v_a_2197_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
lean_dec_ref(v_arg_2194_);
lean_dec_ref(v_arg_2193_);
lean_dec_ref(v_arg_2192_);
v___x_2203_ = lean_box(0);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2203_);
v___x_2205_ = v___x_2199_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
else
{
lean_object* v___x_2207_; 
v___x_2207_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_2193_);
lean_dec_ref(v_arg_2193_);
if (lean_obj_tag(v___x_2207_) == 1)
{
lean_object* v_val_2208_; lean_object* v___x_2209_; 
lean_del_object(v___x_2199_);
v_val_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_val_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v___x_2209_ = l_Lean_Meta_getNatValue_x3f(v_arg_2194_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec_ref(v_arg_2194_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2251_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2251_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2251_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
if (lean_obj_tag(v_a_2210_) == 0)
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
lean_dec(v_val_2208_);
lean_dec_ref(v_arg_2192_);
v___x_2214_ = lean_box(0);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2214_);
v___x_2216_ = v___x_2212_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
else
{
lean_object* v_val_2218_; lean_object* v___x_2219_; 
lean_del_object(v___x_2212_);
v_val_2218_ = lean_ctor_get(v_a_2210_, 0);
lean_inc(v_val_2218_);
lean_dec_ref_known(v_a_2210_, 1);
v___x_2219_ = l_Lean_Meta_getNatValue_x3f(v_arg_2192_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec_ref(v_arg_2192_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2242_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2242_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2242_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
if (lean_obj_tag(v_a_2220_) == 0)
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
lean_dec(v_val_2218_);
lean_dec(v_val_2208_);
v___x_2224_ = lean_box(0);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
else
{
lean_object* v_val_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2241_; 
v_val_2228_ = lean_ctor_get(v_a_2220_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_a_2220_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2230_ = v_a_2220_;
v_isShared_2231_ = v_isSharedCheck_2241_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_val_2228_);
lean_dec(v_a_2220_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2241_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
uint8_t v___x_2232_; float v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2232_ = lean_unbox(v_val_2208_);
lean_dec(v_val_2208_);
v___x_2233_ = l_Float32_ofScientific(v_val_2218_, v___x_2232_, v_val_2228_);
v___x_2234_ = lean_box_float32(v___x_2233_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2234_);
v___x_2236_ = v___x_2230_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2238_; 
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2236_);
v___x_2238_ = v___x_2222_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_val_2218_);
lean_dec(v_val_2208_);
v_a_2243_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2219_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2219_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec(v_val_2208_);
lean_dec_ref(v_arg_2192_);
v_a_2252_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2209_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2209_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2262_; 
lean_dec(v___x_2207_);
lean_dec_ref(v_arg_2194_);
lean_dec_ref(v_arg_2192_);
v___x_2260_ = lean_box(0);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2260_);
v___x_2262_ = v___x_2199_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec_ref(v_arg_2194_);
lean_dec_ref(v_arg_2193_);
lean_dec_ref(v_arg_2192_);
v_a_2265_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2196_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2196_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
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
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_e_2133_);
v_a_2273_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2177_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2177_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
v___jp_2139_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_2145_ = l_Lean_Meta_getOfNatValue_x3f(v_e_2133_, v___x_2144_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2168_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2168_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2168_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
if (lean_obj_tag(v_a_2146_) == 0)
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_box(0);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2150_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
else
{
lean_object* v_val_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2167_; 
v_val_2154_ = lean_ctor_get(v_a_2146_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_a_2146_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2156_ = v_a_2146_;
v_isShared_2157_ = v_isSharedCheck_2167_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_val_2154_);
lean_dec(v_a_2146_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2167_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v_fst_2158_; float v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v_fst_2158_ = lean_ctor_get(v_val_2154_, 0);
lean_inc(v_fst_2158_);
lean_dec(v_val_2154_);
v___x_2159_ = lean_float32_of_nat(v_fst_2158_);
v___x_2160_ = lean_box_float32(v___x_2159_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2160_);
v___x_2162_ = v___x_2156_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2164_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2162_);
v___x_2164_ = v___x_2148_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_a_2169_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2145_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2145_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___boxed(lean_object* v_e_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f(lean_object* v_e_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v___x_2297_; 
lean_inc_ref(v_e_2288_);
v___x_2297_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
if (lean_obj_tag(v_a_2298_) == 1)
{
lean_dec_ref(v_e_2288_);
return v___x_2297_;
}
else
{
lean_object* v___x_2299_; 
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2288_, v_a_2290_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l_Lean_Expr_cleanupAnnotations(v_a_2300_);
lean_dec(v_a_2300_);
v___x_2302_ = l_Lean_Expr_isApp(v___x_2301_);
if (v___x_2302_ == 0)
{
lean_dec_ref(v___x_2301_);
goto v___jp_2294_;
}
else
{
lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2301_);
v___x_2304_ = l_Lean_Expr_isApp(v___x_2303_);
if (v___x_2304_ == 0)
{
lean_dec_ref(v___x_2303_);
lean_dec_ref(v___x_2301_);
goto v___jp_2294_;
}
else
{
lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2303_);
lean_dec_ref(v___x_2303_);
v___x_2306_ = l_Lean_Expr_isApp(v___x_2305_);
if (v___x_2306_ == 0)
{
lean_dec_ref(v___x_2305_);
lean_dec_ref(v___x_2301_);
goto v___jp_2294_;
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2305_);
lean_dec_ref(v___x_2305_);
v___x_2308_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_2309_ = l_Lean_Expr_isConstOf(v___x_2307_, v___x_2308_);
lean_dec_ref(v___x_2307_);
if (v___x_2309_ == 0)
{
lean_dec_ref(v___x_2301_);
goto v___jp_2294_;
}
else
{
lean_object* v_arg_2310_; lean_object* v___x_2311_; 
v_arg_2310_ = lean_ctor_get(v___x_2301_, 1);
lean_inc_ref(v_arg_2310_);
lean_dec_ref(v___x_2301_);
v___x_2311_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_arg_2310_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2334_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2334_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2334_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
if (lean_obj_tag(v_a_2312_) == 1)
{
lean_object* v_val_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2329_; 
v_val_2316_ = lean_ctor_get(v_a_2312_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_a_2312_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2318_ = v_a_2312_;
v_isShared_2319_ = v_isSharedCheck_2329_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_val_2316_);
lean_dec(v_a_2312_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2329_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
float v___x_2320_; float v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2320_ = lean_unbox_float32(v_val_2316_);
lean_dec(v_val_2316_);
v___x_2321_ = lean_float32_negate(v___x_2320_);
v___x_2322_ = lean_box_float32(v___x_2321_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2322_);
v___x_2324_ = v___x_2318_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v___x_2324_);
v___x_2326_ = v___x_2314_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_dec(v_a_2312_);
v___x_2330_ = lean_box(0);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v___x_2330_);
v___x_2332_ = v___x_2314_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
else
{
return v___x_2311_;
}
}
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
v_a_2335_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2299_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2299_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2288_);
return v___x_2297_;
}
v___jp_2294_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_box(0);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f___boxed(lean_object* v_e_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Meta_getFloat32Value_x3f(v_e_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_floatLitValuesEq_x3f(lean_object* v_a_2350_, lean_object* v_b_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___x_2407_; 
lean_inc_ref(v_a_2350_);
v___x_2407_ = l_Lean_Meta_getFloatValue_x3f(v_a_2350_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
if (lean_obj_tag(v_a_2408_) == 1)
{
lean_object* v_val_2409_; lean_object* v___x_2410_; 
v_val_2409_ = lean_ctor_get(v_a_2408_, 0);
lean_inc(v_val_2409_);
lean_dec_ref_known(v_a_2408_, 1);
lean_inc_ref(v_b_2351_);
v___x_2410_ = l_Lean_Meta_getFloatValue_x3f(v_b_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2432_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2432_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2432_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
if (lean_obj_tag(v_a_2411_) == 1)
{
lean_object* v_val_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2431_; 
lean_dec_ref(v_b_2351_);
lean_dec_ref(v_a_2350_);
v_val_2415_ = lean_ctor_get(v_a_2411_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_a_2411_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2417_ = v_a_2411_;
v_isShared_2418_ = v_isSharedCheck_2431_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_val_2415_);
lean_dec(v_a_2411_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2431_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
double v___x_2419_; uint64_t v___x_2420_; double v___x_2421_; uint64_t v___x_2422_; uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2419_ = lean_unbox_float(v_val_2409_);
lean_dec(v_val_2409_);
v___x_2420_ = lean_float_to_bits(v___x_2419_);
v___x_2421_ = lean_unbox_float(v_val_2415_);
lean_dec(v_val_2415_);
v___x_2422_ = lean_float_to_bits(v___x_2421_);
v___x_2423_ = lean_uint64_dec_eq(v___x_2420_, v___x_2422_);
v___x_2424_ = lean_box(v___x_2423_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2424_);
v___x_2426_ = v___x_2417_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2428_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2426_);
v___x_2428_ = v___x_2413_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
else
{
lean_del_object(v___x_2413_);
lean_dec(v_a_2411_);
lean_dec(v_val_2409_);
v___y_2361_ = v_a_2352_;
v___y_2362_ = v_a_2353_;
v___y_2363_ = v_a_2354_;
v___y_2364_ = v_a_2355_;
goto v___jp_2360_;
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_val_2409_);
lean_dec_ref(v_b_2351_);
lean_dec_ref(v_a_2350_);
v_a_2433_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2410_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2410_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_dec(v_a_2408_);
v___y_2361_ = v_a_2352_;
v___y_2362_ = v_a_2353_;
v___y_2363_ = v_a_2354_;
v___y_2364_ = v_a_2355_;
goto v___jp_2360_;
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec_ref(v_b_2351_);
lean_dec_ref(v_a_2350_);
v_a_2441_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2407_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2407_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
v___jp_2357_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
v___jp_2360_:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_Meta_getFloat32Value_x3f(v_a_2350_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2365_, 1);
if (lean_obj_tag(v_a_2366_) == 1)
{
lean_object* v_val_2367_; lean_object* v___x_2368_; 
v_val_2367_ = lean_ctor_get(v_a_2366_, 0);
lean_inc(v_val_2367_);
lean_dec_ref_known(v_a_2366_, 1);
v___x_2368_ = l_Lean_Meta_getFloat32Value_x3f(v_b_2351_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2390_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2390_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2390_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
if (lean_obj_tag(v_a_2369_) == 1)
{
lean_object* v_val_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2389_; 
v_val_2373_ = lean_ctor_get(v_a_2369_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_a_2369_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2375_ = v_a_2369_;
v_isShared_2376_ = v_isSharedCheck_2389_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_val_2373_);
lean_dec(v_a_2369_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2389_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
float v___x_2377_; uint32_t v___x_2378_; float v___x_2379_; uint32_t v___x_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2377_ = lean_unbox_float32(v_val_2367_);
lean_dec(v_val_2367_);
v___x_2378_ = lean_float32_to_bits(v___x_2377_);
v___x_2379_ = lean_unbox_float32(v_val_2373_);
lean_dec(v_val_2373_);
v___x_2380_ = lean_float32_to_bits(v___x_2379_);
v___x_2381_ = lean_uint32_dec_eq(v___x_2378_, v___x_2380_);
v___x_2382_ = lean_box(v___x_2381_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2382_);
v___x_2384_ = v___x_2375_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2386_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2384_);
v___x_2386_ = v___x_2371_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_del_object(v___x_2371_);
lean_dec(v_a_2369_);
lean_dec(v_val_2367_);
goto v___jp_2357_;
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec(v_val_2367_);
v_a_2391_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2368_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2368_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
else
{
lean_dec(v_a_2366_);
lean_dec_ref(v_b_2351_);
goto v___jp_2357_;
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v_b_2351_);
v_a_2399_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2365_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2365_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_floatLitValuesEq_x3f___boxed(lean_object* v_a_2449_, lean_object* v_b_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Meta_floatLitValuesEq_x3f(v_a_2449_, v_b_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(lean_object* v_e_2457_, lean_object* v___y_2458_){
_start:
{
uint8_t v___x_2460_; 
v___x_2460_ = l_Lean_Expr_hasMVar(v_e_2457_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v_e_2457_);
return v___x_2461_;
}
else
{
lean_object* v___x_2462_; lean_object* v_mctx_2463_; lean_object* v___x_2464_; lean_object* v_fst_2465_; lean_object* v_snd_2466_; lean_object* v___x_2467_; lean_object* v_cache_2468_; lean_object* v_zetaDeltaFVarIds_2469_; lean_object* v_postponed_2470_; lean_object* v_diag_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2480_; 
v___x_2462_ = lean_st_ref_get(v___y_2458_);
v_mctx_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc_ref(v_mctx_2463_);
lean_dec(v___x_2462_);
v___x_2464_ = l_Lean_instantiateMVarsCore(v_mctx_2463_, v_e_2457_);
v_fst_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_fst_2465_);
v_snd_2466_ = lean_ctor_get(v___x_2464_, 1);
lean_inc(v_snd_2466_);
lean_dec_ref(v___x_2464_);
v___x_2467_ = lean_st_ref_take(v___y_2458_);
v_cache_2468_ = lean_ctor_get(v___x_2467_, 1);
v_zetaDeltaFVarIds_2469_ = lean_ctor_get(v___x_2467_, 2);
v_postponed_2470_ = lean_ctor_get(v___x_2467_, 3);
v_diag_2471_ = lean_ctor_get(v___x_2467_, 4);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v___x_2467_, 0);
lean_dec(v_unused_2481_);
v___x_2473_ = v___x_2467_;
v_isShared_2474_ = v_isSharedCheck_2480_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_diag_2471_);
lean_inc(v_postponed_2470_);
lean_inc(v_zetaDeltaFVarIds_2469_);
lean_inc(v_cache_2468_);
lean_dec(v___x_2467_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2480_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v_snd_2466_);
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_snd_2466_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_cache_2468_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_zetaDeltaFVarIds_2469_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_postponed_2470_);
lean_ctor_set(v_reuseFailAlloc_2479_, 4, v_diag_2471_);
v___x_2476_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = lean_st_ref_put(v___y_2458_, v___x_2476_);
v___x_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2478_, 0, v_fst_2465_);
return v___x_2478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg___boxed(lean_object* v_e_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2482_, v___y_2483_);
lean_dec(v___y_2483_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(lean_object* v_e_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2486_, v___y_2488_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___boxed(lean_object* v_e_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(v_e_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
return v_res_2499_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__0(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = lean_unsigned_to_nat(0u);
v___x_2501_ = lean_nat_to_int(v___x_2500_);
return v___x_2501_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__1(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = lean_unsigned_to_nat(0u);
v___x_2503_ = l_Lean_Level_ofNat(v___x_2502_);
return v___x_2503_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__2(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = lean_box(0);
v___x_2505_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__1, &l_Lean_Meta_normLitValue___closed__1_once, _init_l_Lean_Meta_normLitValue___closed__1);
v___x_2506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v___x_2504_);
return v___x_2506_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__3(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_2508_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_2509_ = l_Lean_Expr_const___override(v___x_2508_, v___x_2507_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__4(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_box(0);
v___x_2511_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_2512_ = l_Lean_Expr_const___override(v___x_2511_, v___x_2510_);
return v___x_2512_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__7(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2517_ = lean_box(0);
v___x_2518_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__6));
v___x_2519_ = l_Lean_Expr_const___override(v___x_2518_, v___x_2517_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__8(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_2521_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_2522_ = l_Lean_Expr_const___override(v___x_2521_, v___x_2520_);
return v___x_2522_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__9(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = lean_box(0);
v___x_2524_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_2525_ = l_Lean_mkConst(v___x_2524_, v___x_2523_);
return v___x_2525_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__12(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_box(0);
v___x_2531_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__11));
v___x_2532_ = l_Lean_Expr_const___override(v___x_2531_, v___x_2530_);
return v___x_2532_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__15(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = lean_box(0);
v___x_2538_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__14));
v___x_2539_ = l_Lean_Expr_const___override(v___x_2538_, v___x_2537_);
return v___x_2539_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__16(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = lean_box(0);
v___x_2541_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_2542_ = l_Lean_Expr_const___override(v___x_2541_, v___x_2540_);
return v___x_2542_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__17(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = lean_box(0);
v___x_2544_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_2545_ = l_Lean_mkConst(v___x_2544_, v___x_2543_);
return v___x_2545_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__18(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = lean_box(0);
v___x_2547_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_2548_ = l_Lean_mkConst(v___x_2547_, v___x_2546_);
return v___x_2548_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__20(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = lean_box(0);
v___x_2553_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__19));
v___x_2554_ = l_Lean_Expr_const___override(v___x_2553_, v___x_2552_);
return v___x_2554_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__21(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = lean_box(0);
v___x_2556_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_2557_ = l_Lean_mkConst(v___x_2556_, v___x_2555_);
return v___x_2557_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__23(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = lean_box(0);
v___x_2562_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__22));
v___x_2563_ = l_Lean_Expr_const___override(v___x_2562_, v___x_2561_);
return v___x_2563_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__24(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2564_ = lean_box(0);
v___x_2565_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_2566_ = l_Lean_mkConst(v___x_2565_, v___x_2564_);
return v___x_2566_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__26(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_box(0);
v___x_2571_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__25));
v___x_2572_ = l_Lean_Expr_const___override(v___x_2571_, v___x_2570_);
return v___x_2572_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__27(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_box(0);
v___x_2574_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_2575_ = l_Lean_mkConst(v___x_2574_, v___x_2573_);
return v___x_2575_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__29(void){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = lean_box(0);
v___x_2580_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__28));
v___x_2581_ = l_Lean_Expr_const___override(v___x_2580_, v___x_2579_);
return v___x_2581_;
}
}
static uint8_t _init_l_Lean_Meta_normLitValue___closed__30(void){
_start:
{
lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = lean_unsigned_to_nat(0u);
v___x_2583_ = lean_int8_of_nat(v___x_2582_);
return v___x_2583_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__31(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_box(0);
v___x_2585_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_2586_ = l_Lean_Expr_const___override(v___x_2585_, v___x_2584_);
return v___x_2586_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__34(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = lean_box(0);
v___x_2592_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__33));
v___x_2593_ = l_Lean_Expr_const___override(v___x_2592_, v___x_2591_);
return v___x_2593_;
}
}
static uint16_t _init_l_Lean_Meta_normLitValue___closed__35(void){
_start:
{
lean_object* v___x_2594_; uint16_t v___x_2595_; 
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = lean_int16_of_nat(v___x_2594_);
return v___x_2595_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__36(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_box(0);
v___x_2597_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_2598_ = l_Lean_Expr_const___override(v___x_2597_, v___x_2596_);
return v___x_2598_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__38(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_box(0);
v___x_2603_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__37));
v___x_2604_ = l_Lean_Expr_const___override(v___x_2603_, v___x_2602_);
return v___x_2604_;
}
}
static uint32_t _init_l_Lean_Meta_normLitValue___closed__39(void){
_start:
{
lean_object* v___x_2605_; uint32_t v___x_2606_; 
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_int32_of_nat(v___x_2605_);
return v___x_2606_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__40(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_box(0);
v___x_2608_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_2609_ = l_Lean_Expr_const___override(v___x_2608_, v___x_2607_);
return v___x_2609_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__42(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = lean_box(0);
v___x_2614_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__41));
v___x_2615_ = l_Lean_Expr_const___override(v___x_2614_, v___x_2613_);
return v___x_2615_;
}
}
static uint64_t _init_l_Lean_Meta_normLitValue___closed__43(void){
_start:
{
lean_object* v___x_2616_; uint64_t v___x_2617_; 
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = lean_int64_of_nat(v___x_2616_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__44(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_box(0);
v___x_2619_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_2620_ = l_Lean_Expr_const___override(v___x_2619_, v___x_2618_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__46(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = lean_box(0);
v___x_2625_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__45));
v___x_2626_ = l_Lean_Expr_const___override(v___x_2625_, v___x_2624_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue(lean_object* v_e_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v___x_2633_; lean_object* v_a_2634_; lean_object* v___x_2635_; 
v___x_2633_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2627_, v_a_2629_);
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref(v___x_2633_);
v___x_2635_ = l_Lean_Meta_getNatValue_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_3018_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_3018_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_3018_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
if (lean_obj_tag(v_a_2636_) == 1)
{
lean_object* v_val_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_dec(v_a_2634_);
v_val_2640_ = lean_ctor_get(v_a_2636_, 0);
lean_inc(v_val_2640_);
lean_dec_ref_known(v_a_2636_, 1);
v___x_2641_ = l_Lean_mkNatLit(v_val_2640_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2641_);
v___x_2643_ = v___x_2638_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
else
{
lean_object* v___x_2645_; 
lean_del_object(v___x_2638_);
lean_dec(v_a_2636_);
lean_inc(v_a_2634_);
v___x_2645_ = l_Lean_Meta_getIntValue_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_3009_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_3009_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_3009_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
if (lean_obj_tag(v_a_2646_) == 1)
{
lean_object* v_val_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
lean_dec(v_a_2634_);
v_val_2650_ = lean_ctor_get(v_a_2646_, 0);
lean_inc(v_val_2650_);
lean_dec_ref_known(v_a_2646_, 1);
v___x_2651_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_2652_ = lean_int_dec_le(v___x_2651_, v_val_2650_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2653_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2654_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__4, &l_Lean_Meta_normLitValue___closed__4_once, _init_l_Lean_Meta_normLitValue___closed__4);
v___x_2655_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__7, &l_Lean_Meta_normLitValue___closed__7_once, _init_l_Lean_Meta_normLitValue___closed__7);
v___x_2656_ = lean_int_neg(v_val_2650_);
lean_dec(v_val_2650_);
v___x_2657_ = l_Int_toNat(v___x_2656_);
lean_dec(v___x_2656_);
v___x_2658_ = l_Lean_instToExprInt_mkNat(v___x_2657_);
v___x_2659_ = l_Lean_mkApp3(v___x_2653_, v___x_2654_, v___x_2655_, v___x_2658_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2659_);
v___x_2661_ = v___x_2648_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2663_ = l_Int_toNat(v_val_2650_);
lean_dec(v_val_2650_);
v___x_2664_ = l_Lean_instToExprInt_mkNat(v___x_2663_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2664_);
v___x_2666_ = v___x_2648_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
else
{
lean_object* v___x_2668_; 
lean_del_object(v___x_2648_);
lean_dec(v_a_2646_);
lean_inc(v_a_2634_);
v___x_2668_ = l_Lean_Meta_getFinValue_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_3000_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_3000_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_3000_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
if (lean_obj_tag(v_a_2669_) == 1)
{
lean_object* v_val_2673_; lean_object* v_fst_2674_; lean_object* v_snd_2675_; lean_object* v_r_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
lean_dec(v_a_2634_);
v_val_2673_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_val_2673_);
lean_dec_ref_known(v_a_2669_, 1);
v_fst_2674_ = lean_ctor_get(v_val_2673_, 0);
lean_inc_n(v_fst_2674_, 2);
v_snd_2675_ = lean_ctor_get(v_val_2673_, 1);
lean_inc(v_snd_2675_);
lean_dec(v_val_2673_);
v_r_2676_ = l_Lean_mkRawNatLit(v_snd_2675_);
v___x_2677_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2678_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__9, &l_Lean_Meta_normLitValue___closed__9_once, _init_l_Lean_Meta_normLitValue___closed__9);
v___x_2679_ = l_Lean_mkNatLit(v_fst_2674_);
lean_inc_ref(v___x_2679_);
v___x_2680_ = l_Lean_Expr_app___override(v___x_2678_, v___x_2679_);
v___x_2681_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__12, &l_Lean_Meta_normLitValue___closed__12_once, _init_l_Lean_Meta_normLitValue___closed__12);
v___x_2682_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__15, &l_Lean_Meta_normLitValue___closed__15_once, _init_l_Lean_Meta_normLitValue___closed__15);
v___x_2683_ = lean_unsigned_to_nat(1u);
v___x_2684_ = lean_nat_sub(v_fst_2674_, v___x_2683_);
lean_dec(v_fst_2674_);
v___x_2685_ = l_Lean_mkNatLit(v___x_2684_);
v___x_2686_ = l_Lean_Expr_app___override(v___x_2682_, v___x_2685_);
lean_inc_ref(v_r_2676_);
v___x_2687_ = l_Lean_mkApp3(v___x_2681_, v___x_2679_, v___x_2686_, v_r_2676_);
v___x_2688_ = l_Lean_mkApp3(v___x_2677_, v___x_2680_, v_r_2676_, v___x_2687_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2688_);
v___x_2690_ = v___x_2671_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
else
{
lean_object* v___x_2692_; 
lean_del_object(v___x_2671_);
lean_dec(v_a_2669_);
lean_inc(v_a_2634_);
v___x_2692_ = l_Lean_Meta_getBitVecValue_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2991_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2991_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2991_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
if (lean_obj_tag(v_a_2693_) == 1)
{
lean_object* v_val_2697_; lean_object* v_fst_2698_; lean_object* v_snd_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
lean_dec(v_a_2634_);
v_val_2697_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_val_2697_);
lean_dec_ref_known(v_a_2693_, 1);
v_fst_2698_ = lean_ctor_get(v_val_2697_, 0);
lean_inc(v_fst_2698_);
v_snd_2699_ = lean_ctor_get(v_val_2697_, 1);
lean_inc(v_snd_2699_);
lean_dec(v_val_2697_);
v___x_2700_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__16, &l_Lean_Meta_normLitValue___closed__16_once, _init_l_Lean_Meta_normLitValue___closed__16);
v___x_2701_ = l_Lean_mkNatLit(v_fst_2698_);
v___x_2702_ = l_Lean_mkNatLit(v_snd_2699_);
v___x_2703_ = l_Lean_mkAppB(v___x_2700_, v___x_2701_, v___x_2702_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2703_);
v___x_2705_ = v___x_2695_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
else
{
lean_object* v___x_2707_; 
lean_dec(v_a_2693_);
lean_inc(v_a_2634_);
v___x_2707_ = l_Lean_Meta_getStringValue_x3f(v_a_2634_);
if (lean_obj_tag(v___x_2707_) == 1)
{
lean_object* v_val_2708_; lean_object* v___x_2709_; lean_object* v___x_2711_; 
lean_dec(v_a_2634_);
v_val_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v___x_2707_, 1);
v___x_2709_ = l_Lean_mkStrLit(v_val_2708_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2709_);
v___x_2711_ = v___x_2695_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
else
{
lean_object* v___x_2713_; 
lean_dec(v___x_2707_);
lean_del_object(v___x_2695_);
lean_inc(v_a_2634_);
v___x_2713_ = l_Lean_Meta_getCharValue_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2982_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2982_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2982_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
if (lean_obj_tag(v_a_2714_) == 1)
{
lean_object* v_val_2718_; lean_object* v___x_2719_; uint32_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
lean_dec(v_a_2634_);
v_val_2718_ = lean_ctor_get(v_a_2714_, 0);
lean_inc(v_val_2718_);
lean_dec_ref_known(v_a_2714_, 1);
v___x_2719_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__17, &l_Lean_Meta_normLitValue___closed__17_once, _init_l_Lean_Meta_normLitValue___closed__17);
v___x_2720_ = lean_unbox_uint32(v_val_2718_);
lean_dec(v_val_2718_);
v___x_2721_ = lean_uint32_to_nat(v___x_2720_);
v___x_2722_ = l_Lean_mkRawNatLit(v___x_2721_);
v___x_2723_ = l_Lean_Expr_app___override(v___x_2719_, v___x_2722_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v___x_2723_);
v___x_2725_ = v___x_2716_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
else
{
lean_object* v___x_2727_; 
lean_del_object(v___x_2716_);
lean_dec(v_a_2714_);
lean_inc(v_a_2634_);
v___x_2727_ = l_Lean_Meta_getUInt8Value_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2973_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2973_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2973_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
if (lean_obj_tag(v_a_2728_) == 1)
{
lean_object* v_val_2732_; uint8_t v___x_2733_; lean_object* v___x_2734_; lean_object* v_r_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
lean_dec(v_a_2634_);
v_val_2732_ = lean_ctor_get(v_a_2728_, 0);
lean_inc(v_val_2732_);
lean_dec_ref_known(v_a_2728_, 1);
v___x_2733_ = lean_unbox(v_val_2732_);
lean_dec(v_val_2732_);
v___x_2734_ = lean_uint8_to_nat(v___x_2733_);
v_r_2735_ = l_Lean_mkRawNatLit(v___x_2734_);
v___x_2736_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2737_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__18, &l_Lean_Meta_normLitValue___closed__18_once, _init_l_Lean_Meta_normLitValue___closed__18);
v___x_2738_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__20, &l_Lean_Meta_normLitValue___closed__20_once, _init_l_Lean_Meta_normLitValue___closed__20);
lean_inc_ref(v_r_2735_);
v___x_2739_ = l_Lean_Expr_app___override(v___x_2738_, v_r_2735_);
v___x_2740_ = l_Lean_mkApp3(v___x_2736_, v___x_2737_, v_r_2735_, v___x_2739_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2740_);
v___x_2742_ = v___x_2730_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
else
{
lean_object* v___x_2744_; 
lean_del_object(v___x_2730_);
lean_dec(v_a_2728_);
lean_inc(v_a_2634_);
v___x_2744_ = l_Lean_Meta_getUInt16Value_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2964_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2964_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2964_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
if (lean_obj_tag(v_a_2745_) == 1)
{
lean_object* v_val_2749_; uint16_t v___x_2750_; lean_object* v___x_2751_; lean_object* v_r_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
lean_dec(v_a_2634_);
v_val_2749_ = lean_ctor_get(v_a_2745_, 0);
lean_inc(v_val_2749_);
lean_dec_ref_known(v_a_2745_, 1);
v___x_2750_ = lean_unbox(v_val_2749_);
lean_dec(v_val_2749_);
v___x_2751_ = lean_uint16_to_nat(v___x_2750_);
v_r_2752_ = l_Lean_mkRawNatLit(v___x_2751_);
v___x_2753_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2754_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__21, &l_Lean_Meta_normLitValue___closed__21_once, _init_l_Lean_Meta_normLitValue___closed__21);
v___x_2755_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__23, &l_Lean_Meta_normLitValue___closed__23_once, _init_l_Lean_Meta_normLitValue___closed__23);
lean_inc_ref(v_r_2752_);
v___x_2756_ = l_Lean_Expr_app___override(v___x_2755_, v_r_2752_);
v___x_2757_ = l_Lean_mkApp3(v___x_2753_, v___x_2754_, v_r_2752_, v___x_2756_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___x_2757_);
v___x_2759_ = v___x_2747_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
else
{
lean_object* v___x_2761_; 
lean_del_object(v___x_2747_);
lean_dec(v_a_2745_);
lean_inc(v_a_2634_);
v___x_2761_ = l_Lean_Meta_getUInt32Value_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2955_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2955_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2955_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
if (lean_obj_tag(v_a_2762_) == 1)
{
lean_object* v_val_2766_; uint32_t v___x_2767_; lean_object* v___x_2768_; lean_object* v_r_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
lean_dec(v_a_2634_);
v_val_2766_ = lean_ctor_get(v_a_2762_, 0);
lean_inc(v_val_2766_);
lean_dec_ref_known(v_a_2762_, 1);
v___x_2767_ = lean_unbox_uint32(v_val_2766_);
lean_dec(v_val_2766_);
v___x_2768_ = lean_uint32_to_nat(v___x_2767_);
v_r_2769_ = l_Lean_mkRawNatLit(v___x_2768_);
v___x_2770_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2771_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__24, &l_Lean_Meta_normLitValue___closed__24_once, _init_l_Lean_Meta_normLitValue___closed__24);
v___x_2772_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__26, &l_Lean_Meta_normLitValue___closed__26_once, _init_l_Lean_Meta_normLitValue___closed__26);
lean_inc_ref(v_r_2769_);
v___x_2773_ = l_Lean_Expr_app___override(v___x_2772_, v_r_2769_);
v___x_2774_ = l_Lean_mkApp3(v___x_2770_, v___x_2771_, v_r_2769_, v___x_2773_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2774_);
v___x_2776_ = v___x_2764_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
else
{
lean_object* v___x_2778_; 
lean_del_object(v___x_2764_);
lean_dec(v_a_2762_);
lean_inc(v_a_2634_);
v___x_2778_ = l_Lean_Meta_getUInt64Value_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2946_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2946_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2946_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
if (lean_obj_tag(v_a_2779_) == 1)
{
lean_object* v_val_2783_; uint64_t v___x_2784_; lean_object* v___x_2785_; lean_object* v_r_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
lean_dec(v_a_2634_);
v_val_2783_ = lean_ctor_get(v_a_2779_, 0);
lean_inc(v_val_2783_);
lean_dec_ref_known(v_a_2779_, 1);
v___x_2784_ = lean_unbox_uint64(v_val_2783_);
lean_dec(v_val_2783_);
v___x_2785_ = lean_uint64_to_nat(v___x_2784_);
v_r_2786_ = l_Lean_mkRawNatLit(v___x_2785_);
v___x_2787_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2788_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__27, &l_Lean_Meta_normLitValue___closed__27_once, _init_l_Lean_Meta_normLitValue___closed__27);
v___x_2789_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__29, &l_Lean_Meta_normLitValue___closed__29_once, _init_l_Lean_Meta_normLitValue___closed__29);
lean_inc_ref(v_r_2786_);
v___x_2790_ = l_Lean_Expr_app___override(v___x_2789_, v_r_2786_);
v___x_2791_ = l_Lean_mkApp3(v___x_2787_, v___x_2788_, v_r_2786_, v___x_2790_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2791_);
v___x_2793_ = v___x_2781_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
else
{
lean_object* v___x_2795_; 
lean_del_object(v___x_2781_);
lean_dec(v_a_2779_);
lean_inc(v_a_2634_);
v___x_2795_ = l_Lean_Meta_getInt8Value_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2937_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2937_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2937_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
if (lean_obj_tag(v_a_2796_) == 1)
{
lean_object* v_val_2800_; uint8_t v___x_2801_; uint8_t v___x_2802_; uint8_t v___x_2803_; 
lean_dec(v_a_2634_);
v_val_2800_ = lean_ctor_get(v_a_2796_, 0);
lean_inc(v_val_2800_);
lean_dec_ref_known(v_a_2796_, 1);
v___x_2801_ = lean_uint8_once(&l_Lean_Meta_normLitValue___closed__30, &l_Lean_Meta_normLitValue___closed__30_once, _init_l_Lean_Meta_normLitValue___closed__30);
v___x_2802_ = lean_unbox(v_val_2800_);
v___x_2803_ = lean_int8_dec_le(v___x_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2804_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2805_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__31, &l_Lean_Meta_normLitValue___closed__31_once, _init_l_Lean_Meta_normLitValue___closed__31);
v___x_2806_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__34, &l_Lean_Meta_normLitValue___closed__34_once, _init_l_Lean_Meta_normLitValue___closed__34);
v___x_2807_ = lean_unbox(v_val_2800_);
lean_dec(v_val_2800_);
v___x_2808_ = lean_int8_to_int(v___x_2807_);
v___x_2809_ = lean_int_neg(v___x_2808_);
v___x_2810_ = l_Int_toNat(v___x_2809_);
lean_dec(v___x_2809_);
v___x_2811_ = l_Lean_instToExprInt8_mkNat(v___x_2810_);
v___x_2812_ = l_Lean_mkApp3(v___x_2804_, v___x_2805_, v___x_2806_, v___x_2811_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2812_);
v___x_2814_ = v___x_2798_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
else
{
uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2816_ = lean_unbox(v_val_2800_);
lean_dec(v_val_2800_);
v___x_2817_ = lean_int8_to_int(v___x_2816_);
v___x_2818_ = l_Int_toNat(v___x_2817_);
v___x_2819_ = l_Lean_instToExprInt8_mkNat(v___x_2818_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2819_);
v___x_2821_ = v___x_2798_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
else
{
lean_object* v___x_2823_; 
lean_del_object(v___x_2798_);
lean_dec(v_a_2796_);
lean_inc(v_a_2634_);
v___x_2823_ = l_Lean_Meta_getInt16Value_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2928_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2928_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2928_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
if (lean_obj_tag(v_a_2824_) == 1)
{
lean_object* v_val_2828_; uint16_t v___x_2829_; uint16_t v___x_2830_; uint8_t v___x_2831_; 
lean_dec(v_a_2634_);
v_val_2828_ = lean_ctor_get(v_a_2824_, 0);
lean_inc(v_val_2828_);
lean_dec_ref_known(v_a_2824_, 1);
v___x_2829_ = lean_uint16_once(&l_Lean_Meta_normLitValue___closed__35, &l_Lean_Meta_normLitValue___closed__35_once, _init_l_Lean_Meta_normLitValue___closed__35);
v___x_2830_ = lean_unbox(v_val_2828_);
v___x_2831_ = lean_int16_dec_le(v___x_2829_, v___x_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint16_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
v___x_2832_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2833_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__36, &l_Lean_Meta_normLitValue___closed__36_once, _init_l_Lean_Meta_normLitValue___closed__36);
v___x_2834_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__38, &l_Lean_Meta_normLitValue___closed__38_once, _init_l_Lean_Meta_normLitValue___closed__38);
v___x_2835_ = lean_unbox(v_val_2828_);
lean_dec(v_val_2828_);
v___x_2836_ = lean_int16_to_int(v___x_2835_);
v___x_2837_ = lean_int_neg(v___x_2836_);
v___x_2838_ = l_Int_toNat(v___x_2837_);
lean_dec(v___x_2837_);
v___x_2839_ = l_Lean_instToExprInt16_mkNat(v___x_2838_);
v___x_2840_ = l_Lean_mkApp3(v___x_2832_, v___x_2833_, v___x_2834_, v___x_2839_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2840_);
v___x_2842_ = v___x_2826_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
else
{
uint16_t v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2844_ = lean_unbox(v_val_2828_);
lean_dec(v_val_2828_);
v___x_2845_ = lean_int16_to_int(v___x_2844_);
v___x_2846_ = l_Int_toNat(v___x_2845_);
v___x_2847_ = l_Lean_instToExprInt16_mkNat(v___x_2846_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2847_);
v___x_2849_ = v___x_2826_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2847_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
else
{
lean_object* v___x_2851_; 
lean_del_object(v___x_2826_);
lean_dec(v_a_2824_);
lean_inc(v_a_2634_);
v___x_2851_ = l_Lean_Meta_getInt32Value_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2919_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2854_ = v___x_2851_;
v_isShared_2855_ = v_isSharedCheck_2919_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2919_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
if (lean_obj_tag(v_a_2852_) == 1)
{
lean_object* v_val_2856_; uint32_t v___x_2857_; uint32_t v___x_2858_; uint8_t v___x_2859_; 
lean_dec(v_a_2634_);
v_val_2856_ = lean_ctor_get(v_a_2852_, 0);
lean_inc(v_val_2856_);
lean_dec_ref_known(v_a_2852_, 1);
v___x_2857_ = lean_uint32_once(&l_Lean_Meta_normLitValue___closed__39, &l_Lean_Meta_normLitValue___closed__39_once, _init_l_Lean_Meta_normLitValue___closed__39);
v___x_2858_ = lean_unbox_uint32(v_val_2856_);
v___x_2859_ = lean_int32_dec_le(v___x_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; uint32_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2860_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2861_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__40, &l_Lean_Meta_normLitValue___closed__40_once, _init_l_Lean_Meta_normLitValue___closed__40);
v___x_2862_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__42, &l_Lean_Meta_normLitValue___closed__42_once, _init_l_Lean_Meta_normLitValue___closed__42);
v___x_2863_ = lean_unbox_uint32(v_val_2856_);
lean_dec(v_val_2856_);
v___x_2864_ = lean_int32_to_int(v___x_2863_);
v___x_2865_ = lean_int_neg(v___x_2864_);
lean_dec(v___x_2864_);
v___x_2866_ = l_Int_toNat(v___x_2865_);
lean_dec(v___x_2865_);
v___x_2867_ = l_Lean_instToExprInt32_mkNat(v___x_2866_);
v___x_2868_ = l_Lean_mkApp3(v___x_2860_, v___x_2861_, v___x_2862_, v___x_2867_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2868_);
v___x_2870_ = v___x_2854_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
else
{
uint32_t v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2872_ = lean_unbox_uint32(v_val_2856_);
lean_dec(v_val_2856_);
v___x_2873_ = lean_int32_to_int(v___x_2872_);
v___x_2874_ = l_Int_toNat(v___x_2873_);
lean_dec(v___x_2873_);
v___x_2875_ = l_Lean_instToExprInt32_mkNat(v___x_2874_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2875_);
v___x_2877_ = v___x_2854_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
else
{
lean_object* v___x_2879_; 
lean_del_object(v___x_2854_);
lean_dec(v_a_2852_);
lean_inc(v_a_2634_);
v___x_2879_ = l_Lean_Meta_getInt64Value_x3f(v_a_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2910_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2882_ = v___x_2879_;
v_isShared_2883_ = v_isSharedCheck_2910_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2910_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
if (lean_obj_tag(v_a_2880_) == 1)
{
lean_object* v_val_2884_; uint64_t v___x_2885_; uint64_t v___x_2886_; uint8_t v___x_2887_; 
lean_dec(v_a_2634_);
v_val_2884_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_val_2884_);
lean_dec_ref_known(v_a_2880_, 1);
v___x_2885_ = lean_uint64_once(&l_Lean_Meta_normLitValue___closed__43, &l_Lean_Meta_normLitValue___closed__43_once, _init_l_Lean_Meta_normLitValue___closed__43);
v___x_2886_ = lean_unbox_uint64(v_val_2884_);
v___x_2887_ = lean_int64_dec_le(v___x_2885_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; uint64_t v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2888_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2889_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__44, &l_Lean_Meta_normLitValue___closed__44_once, _init_l_Lean_Meta_normLitValue___closed__44);
v___x_2890_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__46, &l_Lean_Meta_normLitValue___closed__46_once, _init_l_Lean_Meta_normLitValue___closed__46);
v___x_2891_ = lean_unbox_uint64(v_val_2884_);
lean_dec(v_val_2884_);
v___x_2892_ = lean_int64_to_int_sint(v___x_2891_);
v___x_2893_ = lean_int_neg(v___x_2892_);
lean_dec(v___x_2892_);
v___x_2894_ = l_Int_toNat(v___x_2893_);
lean_dec(v___x_2893_);
v___x_2895_ = l_Lean_instToExprInt64_mkNat(v___x_2894_);
v___x_2896_ = l_Lean_mkApp3(v___x_2888_, v___x_2889_, v___x_2890_, v___x_2895_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2896_);
v___x_2898_ = v___x_2882_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
else
{
uint64_t v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2900_ = lean_unbox_uint64(v_val_2884_);
lean_dec(v_val_2884_);
v___x_2901_ = lean_int64_to_int_sint(v___x_2900_);
v___x_2902_ = l_Int_toNat(v___x_2901_);
lean_dec(v___x_2901_);
v___x_2903_ = l_Lean_instToExprInt64_mkNat(v___x_2902_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2903_);
v___x_2905_ = v___x_2882_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
else
{
lean_object* v___x_2908_; 
lean_dec(v_a_2880_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v_a_2634_);
v___x_2908_ = v___x_2882_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2634_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v_a_2634_);
v_a_2911_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2879_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2879_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_a_2634_);
v_a_2920_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2851_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2851_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v_a_2634_);
v_a_2929_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2823_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2823_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v_a_2634_);
v_a_2938_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2795_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2795_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v_a_2634_);
v_a_2947_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2778_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2778_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec(v_a_2634_);
v_a_2956_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2761_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2761_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v_a_2634_);
v_a_2965_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2744_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2744_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec(v_a_2634_);
v_a_2974_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2727_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2727_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec(v_a_2634_);
v_a_2983_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2713_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2713_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec(v_a_2634_);
v_a_2992_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2692_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2692_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec(v_a_2634_);
v_a_3001_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2668_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2668_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec(v_a_2634_);
v_a_3010_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2645_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2645_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_a_2634_);
v_a_3019_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2635_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2635_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue___boxed(lean_object* v_e_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_Meta_normLitValue(v_e_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(lean_object* v_m_3040_, lean_object* v_s_3041_, lean_object* v_exp_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v_s_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v_s_3053_ = l_Lean_Expr_consumeMData(v_s_3041_);
v___x_3054_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__0));
v___x_3055_ = l_Lean_Expr_isConstOf(v_s_3053_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3056_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__1));
v___x_3057_ = l_Lean_Expr_isConstOf(v_s_3053_, v___x_3056_);
lean_dec_ref(v_s_3053_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_box(v___x_3057_);
v___x_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
return v___x_3059_;
}
else
{
goto v___jp_3048_;
}
}
else
{
lean_dec_ref(v_s_3053_);
goto v___jp_3048_;
}
v___jp_3048_:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_Meta_isNatValue(v_m_3040_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; uint8_t v___x_3051_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v___x_3051_ = lean_unbox(v_a_3050_);
if (v___x_3051_ == 0)
{
return v___x_3049_;
}
else
{
lean_object* v___x_3052_; 
lean_dec_ref_known(v___x_3049_, 1);
v___x_3052_ = l_Lean_Meta_isNatValue(v_exp_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
return v___x_3052_;
}
}
else
{
return v___x_3049_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___boxed(lean_object* v_m_3060_, lean_object* v_s_3061_, lean_object* v_exp_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_3060_, v_s_3061_, v_exp_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec_ref(v_exp_3062_);
lean_dec_ref(v_s_3061_);
lean_dec_ref(v_m_3060_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(lean_object* v_type_3069_, lean_object* v_m_3070_, lean_object* v_s_3071_, lean_object* v_exp_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Lean_Meta_whnfD(v_type_3069_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3096_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3096_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3096_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_3084_ = l_Lean_Expr_isConstOf(v_a_3079_, v___x_3083_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_3086_ = l_Lean_Expr_isConstOf(v_a_3079_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; uint8_t v___x_3088_; 
v___x_3087_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_3088_ = l_Lean_Expr_isConstOf(v_a_3079_, v___x_3087_);
lean_dec(v_a_3079_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = lean_box(v___x_3088_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 0, v___x_3089_);
v___x_3091_ = v___x_3081_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
else
{
lean_object* v___x_3093_; 
lean_del_object(v___x_3081_);
v___x_3093_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_3070_, v_s_3071_, v_exp_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
return v___x_3093_;
}
}
else
{
lean_object* v___x_3094_; 
lean_del_object(v___x_3081_);
lean_dec(v_a_3079_);
v___x_3094_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_3070_, v_s_3071_, v_exp_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
return v___x_3094_;
}
}
else
{
lean_object* v___x_3095_; 
lean_del_object(v___x_3081_);
lean_dec(v_a_3079_);
v___x_3095_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_3070_, v_s_3071_, v_exp_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
return v___x_3095_;
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
v_a_3097_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3078_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3078_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue___boxed(lean_object* v_type_3105_, lean_object* v_m_3106_, lean_object* v_s_3107_, lean_object* v_exp_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(v_type_3105_, v_m_3106_, v_s_3107_, v_exp_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
lean_dec_ref(v_exp_3108_);
lean_dec_ref(v_s_3107_);
lean_dec_ref(v_m_3106_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue(lean_object* v_type_3115_, lean_object* v_n_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3122_ = l_Lean_Expr_consumeMData(v_n_3116_);
v___x_3123_ = l_Lean_Expr_isRawNatLit(v___x_3122_);
lean_dec_ref(v___x_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
lean_dec_ref(v_type_3115_);
v___x_3124_ = lean_box(v___x_3123_);
v___x_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3124_);
return v___x_3125_;
}
else
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Lean_Meta_whnfD(v_type_3115_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3248_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3248_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3248_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Expr_getAppFn(v_a_3127_);
if (lean_obj_tag(v___x_3131_) == 4)
{
lean_object* v_declName_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v_declName_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_declName_3132_);
lean_dec_ref_known(v___x_3131_, 2);
v___x_3133_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_3134_ = lean_name_eq(v_declName_3132_, v___x_3133_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; uint8_t v___x_3136_; 
v___x_3135_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_3136_ = lean_name_eq(v_declName_3132_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3137_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_3138_ = lean_name_eq(v_declName_3132_, v___x_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; uint8_t v___x_3140_; 
v___x_3139_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_3140_ = lean_name_eq(v_declName_3132_, v___x_3139_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3141_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_3142_ = lean_name_eq(v_declName_3132_, v___x_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; uint8_t v___x_3144_; 
v___x_3143_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_3144_ = lean_name_eq(v_declName_3132_, v___x_3143_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_3146_ = lean_name_eq(v_declName_3132_, v___x_3145_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; uint8_t v___x_3148_; 
v___x_3147_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_3148_ = lean_name_eq(v_declName_3132_, v___x_3147_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3149_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_3150_ = lean_name_eq(v_declName_3132_, v___x_3149_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; uint8_t v___x_3152_; 
v___x_3151_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_3152_ = lean_name_eq(v_declName_3132_, v___x_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3153_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_3154_ = lean_name_eq(v_declName_3132_, v___x_3153_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; uint8_t v___x_3156_; 
v___x_3155_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_3156_ = lean_name_eq(v_declName_3132_, v___x_3155_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3157_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_3158_ = lean_name_eq(v_declName_3132_, v___x_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_3159_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_3160_ = lean_name_eq(v_declName_3132_, v___x_3159_);
if (v___x_3160_ == 0)
{
lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_3162_ = lean_name_eq(v_declName_3132_, v___x_3161_);
lean_dec(v_declName_3132_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3165_; 
lean_dec(v_a_3127_);
v___x_3163_ = lean_box(v___x_3162_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3163_);
v___x_3165_ = v___x_3129_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
else
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_del_object(v___x_3129_);
v___x_3167_ = l_Lean_Expr_appArg_x21(v_a_3127_);
lean_dec(v_a_3127_);
v___x_3168_ = l_Lean_Meta_whnfD(v___x_3167_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3170_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___x_3168_, 1);
v___x_3170_ = l_Lean_Meta_isNatValue(v_a_3169_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
lean_dec(v_a_3169_);
return v___x_3170_;
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
v_a_3171_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3168_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3168_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_dec(v_declName_3132_);
lean_del_object(v___x_3129_);
v___x_3179_ = l_Lean_Expr_appArg_x21(v_a_3127_);
lean_dec(v_a_3127_);
v___x_3180_ = l_Lean_Meta_whnfD(v___x_3179_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3182_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3181_);
lean_dec_ref_known(v___x_3180_, 1);
v___x_3182_ = l_Lean_Meta_isNonZeroNatValue(v_a_3181_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
lean_dec(v_a_3181_);
return v___x_3182_;
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
v_a_3183_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3180_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3180_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
}
else
{
lean_object* v___x_3191_; lean_object* v___x_3193_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3191_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3191_);
v___x_3193_ = v___x_3129_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3197_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3195_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3195_);
v___x_3197_ = v___x_3129_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
else
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3199_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3199_);
v___x_3201_ = v___x_3129_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3203_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3203_);
v___x_3205_ = v___x_3129_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3209_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3207_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3207_);
v___x_3209_ = v___x_3129_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3213_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3211_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3211_);
v___x_3213_ = v___x_3129_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
else
{
lean_object* v___x_3215_; lean_object* v___x_3217_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3215_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3215_);
v___x_3217_ = v___x_3129_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
else
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3219_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3219_);
v___x_3221_ = v___x_3129_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
else
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3223_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3223_);
v___x_3225_ = v___x_3129_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3229_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3227_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3227_);
v___x_3229_ = v___x_3129_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3231_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3231_);
v___x_3233_ = v___x_3129_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3237_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3235_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3235_);
v___x_3237_ = v___x_3129_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
else
{
lean_object* v___x_3239_; lean_object* v___x_3241_; 
lean_dec(v_declName_3132_);
lean_dec(v_a_3127_);
v___x_3239_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3239_);
v___x_3241_ = v___x_3129_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
else
{
uint8_t v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
lean_dec_ref(v___x_3131_);
lean_dec(v_a_3127_);
v___x_3243_ = 0;
v___x_3244_ = lean_box(v___x_3243_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3244_);
v___x_3246_ = v___x_3129_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
v_a_3249_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3126_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3126_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue___boxed(lean_object* v_type_3257_, lean_object* v_n_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue(v_type_3257_, v_n_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec_ref(v_n_3258_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue(lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_3265_, v_a_3267_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3375_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3375_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3375_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; uint8_t v___x_3281_; 
v___x_3280_ = l_Lean_Expr_cleanupAnnotations(v_a_3276_);
lean_dec(v_a_3276_);
v___x_3281_ = l_Lean_Expr_isApp(v___x_3280_);
if (v___x_3281_ == 0)
{
lean_dec_ref(v___x_3280_);
lean_del_object(v___x_3278_);
goto v___jp_3271_;
}
else
{
lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3282_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3280_);
v___x_3283_ = l_Lean_Expr_isApp(v___x_3282_);
if (v___x_3283_ == 0)
{
lean_dec_ref(v___x_3282_);
lean_dec_ref(v___x_3280_);
lean_del_object(v___x_3278_);
goto v___jp_3271_;
}
else
{
lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3284_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3282_);
v___x_3285_ = l_Lean_Expr_isApp(v___x_3284_);
if (v___x_3285_ == 0)
{
lean_dec_ref(v___x_3284_);
lean_dec_ref(v___x_3282_);
lean_dec_ref(v___x_3280_);
lean_del_object(v___x_3278_);
goto v___jp_3271_;
}
else
{
lean_object* v_arg_3286_; lean_object* v_arg_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
v_arg_3286_ = lean_ctor_get(v___x_3282_, 1);
lean_inc_ref(v_arg_3286_);
lean_dec_ref(v___x_3282_);
v_arg_3287_ = lean_ctor_get(v___x_3284_, 1);
lean_inc_ref(v_arg_3287_);
v___x_3288_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3284_);
lean_dec_ref(v___x_3284_);
v___x_3289_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_3290_ = l_Lean_Expr_isConstOf(v___x_3288_, v___x_3289_);
if (v___x_3290_ == 0)
{
uint8_t v___x_3291_; 
lean_del_object(v___x_3278_);
v___x_3291_ = l_Lean_Expr_isApp(v___x_3288_);
if (v___x_3291_ == 0)
{
lean_dec_ref(v___x_3288_);
lean_dec_ref(v_arg_3287_);
lean_dec_ref(v_arg_3286_);
lean_dec_ref(v___x_3280_);
goto v___jp_3271_;
}
else
{
lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___x_3292_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3288_);
lean_dec_ref(v___x_3288_);
v___x_3293_ = l_Lean_Expr_isApp(v___x_3292_);
if (v___x_3293_ == 0)
{
lean_dec_ref(v___x_3292_);
lean_dec_ref(v_arg_3287_);
lean_dec_ref(v_arg_3286_);
lean_dec_ref(v___x_3280_);
goto v___jp_3271_;
}
else
{
lean_object* v___x_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3294_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3292_);
v___x_3295_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_3296_ = l_Lean_Expr_isConstOf(v___x_3294_, v___x_3295_);
lean_dec_ref(v___x_3294_);
if (v___x_3296_ == 0)
{
lean_dec_ref(v___x_3292_);
lean_dec_ref(v_arg_3287_);
lean_dec_ref(v_arg_3286_);
lean_dec_ref(v___x_3280_);
goto v___jp_3271_;
}
else
{
lean_object* v_arg_3297_; lean_object* v_arg_3298_; lean_object* v___x_3299_; 
v_arg_3297_ = lean_ctor_get(v___x_3280_, 1);
lean_inc_ref(v_arg_3297_);
lean_dec_ref(v___x_3280_);
v_arg_3298_ = lean_ctor_get(v___x_3292_, 1);
lean_inc_ref(v_arg_3298_);
lean_dec_ref(v___x_3292_);
v___x_3299_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(v_arg_3298_, v_arg_3287_, v_arg_3286_, v_arg_3297_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
lean_dec_ref(v_arg_3297_);
lean_dec_ref(v_arg_3286_);
lean_dec_ref(v_arg_3287_);
return v___x_3299_;
}
}
}
}
else
{
lean_object* v___x_3300_; uint8_t v___x_3301_; 
lean_dec_ref(v___x_3288_);
lean_dec_ref(v___x_3280_);
v___x_3300_ = l_Lean_Expr_consumeMData(v_arg_3286_);
lean_dec_ref(v_arg_3286_);
v___x_3301_ = l_Lean_Expr_isRawNatLit(v___x_3300_);
lean_dec_ref(v___x_3300_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; lean_object* v___x_3304_; 
lean_dec_ref(v_arg_3287_);
v___x_3302_ = lean_box(v___x_3301_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3302_);
v___x_3304_ = v___x_3278_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
else
{
lean_object* v___x_3306_; 
lean_del_object(v___x_3278_);
v___x_3306_ = l_Lean_Meta_whnfD(v_arg_3287_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3366_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3366_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3366_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_Expr_getAppFn(v_a_3307_);
lean_dec(v_a_3307_);
if (lean_obj_tag(v___x_3311_) == 4)
{
lean_object* v_declName_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v_declName_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_declName_3312_);
lean_dec_ref_known(v___x_3311_, 2);
v___x_3313_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_3314_ = lean_name_eq(v_declName_3312_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3315_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_3316_ = lean_name_eq(v_declName_3312_, v___x_3315_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; uint8_t v___x_3318_; 
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_3318_ = lean_name_eq(v_declName_3312_, v___x_3317_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_3320_ = lean_name_eq(v_declName_3312_, v___x_3319_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3321_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_3322_ = lean_name_eq(v_declName_3312_, v___x_3321_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3323_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_3324_ = lean_name_eq(v_declName_3312_, v___x_3323_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; uint8_t v___x_3326_; 
v___x_3325_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_3326_ = lean_name_eq(v_declName_3312_, v___x_3325_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; uint8_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3331_; 
v___x_3327_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_3328_ = lean_name_eq(v_declName_3312_, v___x_3327_);
lean_dec(v_declName_3312_);
v___x_3329_ = lean_box(v___x_3328_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3329_);
v___x_3331_ = v___x_3309_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
else
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
lean_dec(v_declName_3312_);
v___x_3333_ = lean_box(v___x_3290_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3333_);
v___x_3335_ = v___x_3309_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
else
{
lean_object* v___x_3337_; lean_object* v___x_3339_; 
lean_dec(v_declName_3312_);
v___x_3337_ = lean_box(v___x_3290_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3337_);
v___x_3339_ = v___x_3309_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
else
{
lean_object* v___x_3341_; lean_object* v___x_3343_; 
lean_dec(v_declName_3312_);
v___x_3341_ = lean_box(v___x_3290_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3341_);
v___x_3343_ = v___x_3309_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
else
{
lean_object* v___x_3345_; lean_object* v___x_3347_; 
lean_dec(v_declName_3312_);
v___x_3345_ = lean_box(v___x_3290_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3345_);
v___x_3347_ = v___x_3309_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3351_; 
lean_dec(v_declName_3312_);
v___x_3349_ = lean_box(v___x_3290_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3349_);
v___x_3351_ = v___x_3309_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
else
{
lean_object* v___x_3353_; lean_object* v___x_3355_; 
lean_dec(v_declName_3312_);
v___x_3353_ = lean_box(v___x_3290_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3353_);
v___x_3355_ = v___x_3309_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
lean_dec(v_declName_3312_);
v___x_3357_ = lean_box(v___x_3290_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3357_);
v___x_3359_ = v___x_3309_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
else
{
uint8_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3364_; 
lean_dec_ref(v___x_3311_);
v___x_3361_ = 0;
v___x_3362_ = lean_box(v___x_3361_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3362_);
v___x_3364_ = v___x_3309_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
v_a_3367_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3306_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3306_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
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
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
v_a_3376_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3275_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3275_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
v___jp_3271_:
{
uint8_t v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3272_ = 0;
v___x_3273_ = lean_box(v___x_3272_);
v___x_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
return v___x_3274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue___boxed(lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue(v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(lean_object* v_e_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3401_ = l_Lean_Expr_cleanupAnnotations(v_e_3391_);
v___x_3402_ = l_Lean_Expr_isApp(v___x_3401_);
if (v___x_3402_ == 0)
{
lean_dec_ref(v___x_3401_);
goto v___jp_3397_;
}
else
{
lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3403_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3401_);
lean_dec_ref(v___x_3401_);
v___x_3404_ = l_Lean_Expr_isApp(v___x_3403_);
if (v___x_3404_ == 0)
{
lean_dec_ref(v___x_3403_);
goto v___jp_3397_;
}
else
{
lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3405_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3403_);
v___x_3406_ = l_Lean_Expr_isApp(v___x_3405_);
if (v___x_3406_ == 0)
{
lean_dec_ref(v___x_3405_);
lean_dec_ref(v___x_3403_);
goto v___jp_3397_;
}
else
{
lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3407_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3405_);
v___x_3408_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_3409_ = l_Lean_Expr_isConstOf(v___x_3407_, v___x_3408_);
lean_dec_ref(v___x_3407_);
if (v___x_3409_ == 0)
{
lean_dec_ref(v___x_3405_);
lean_dec_ref(v___x_3403_);
goto v___jp_3397_;
}
else
{
lean_object* v_arg_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v_arg_3410_ = lean_ctor_get(v___x_3403_, 1);
lean_inc_ref(v_arg_3410_);
lean_dec_ref(v___x_3403_);
v___x_3411_ = l_Lean_Expr_consumeMData(v_arg_3410_);
lean_dec_ref(v_arg_3410_);
v___x_3412_ = l_Lean_Expr_isRawNatLit(v___x_3411_);
lean_dec_ref(v___x_3411_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec_ref(v___x_3405_);
v___x_3413_ = lean_box(v___x_3412_);
v___x_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
else
{
lean_object* v_arg_3415_; lean_object* v___x_3416_; 
v_arg_3415_ = lean_ctor_get(v___x_3405_, 1);
lean_inc_ref(v_arg_3415_);
lean_dec_ref(v___x_3405_);
v___x_3416_ = l_Lean_Meta_whnfD(v_arg_3415_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3428_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3428_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3428_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; uint8_t v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
v___x_3421_ = l_Lean_Expr_getAppFn(v_a_3417_);
lean_dec(v_a_3417_);
v___x_3422_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_3423_ = l_Lean_Expr_isConstOf(v___x_3421_, v___x_3422_);
lean_dec_ref(v___x_3421_);
v___x_3424_ = lean_box(v___x_3423_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3424_);
v___x_3426_ = v___x_3419_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
v_a_3429_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3416_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3416_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
}
}
}
}
v___jp_3397_:
{
uint8_t v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3398_ = 0;
v___x_3399_ = lean_box(v___x_3398_);
v___x_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
return v___x_3400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat___boxed(lean_object* v_e_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(v_e_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
lean_dec(v_a_3441_);
lean_dec_ref(v_a_3440_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3438_);
lean_dec_ref(v_e_3437_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue(lean_object* v_a_3444_, lean_object* v_b_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v___y_3452_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3457_ = l_Lean_Expr_cleanupAnnotations(v_a_3444_);
v___x_3458_ = l_Lean_Expr_isApp(v___x_3457_);
if (v___x_3458_ == 0)
{
lean_dec_ref(v___x_3457_);
v___y_3452_ = v_a_3444_;
goto v___jp_3451_;
}
else
{
lean_object* v___x_3459_; uint8_t v___x_3460_; 
v___x_3459_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3457_);
v___x_3460_ = l_Lean_Expr_isApp(v___x_3459_);
if (v___x_3460_ == 0)
{
lean_dec_ref(v___x_3459_);
lean_dec_ref(v___x_3457_);
v___y_3452_ = v_a_3444_;
goto v___jp_3451_;
}
else
{
lean_object* v___x_3461_; uint8_t v___x_3462_; 
v___x_3461_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3459_);
lean_dec_ref(v___x_3459_);
v___x_3462_ = l_Lean_Expr_isApp(v___x_3461_);
if (v___x_3462_ == 0)
{
lean_dec_ref(v___x_3461_);
lean_dec_ref(v___x_3457_);
v___y_3452_ = v_a_3444_;
goto v___jp_3451_;
}
else
{
lean_object* v___x_3463_; lean_object* v___x_3464_; uint8_t v___x_3465_; 
v___x_3463_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3461_);
lean_dec_ref(v___x_3461_);
v___x_3464_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_3465_ = l_Lean_Expr_isConstOf(v___x_3463_, v___x_3464_);
lean_dec_ref(v___x_3463_);
if (v___x_3465_ == 0)
{
lean_dec_ref(v___x_3457_);
v___y_3452_ = v_a_3444_;
goto v___jp_3451_;
}
else
{
lean_object* v_arg_3466_; 
lean_dec_ref(v_a_3444_);
v_arg_3466_ = lean_ctor_get(v___x_3457_, 1);
lean_inc_ref(v_arg_3466_);
lean_dec_ref(v___x_3457_);
v___y_3452_ = v_arg_3466_;
goto v___jp_3451_;
}
}
}
}
v___jp_3451_:
{
lean_object* v___x_3453_; 
v___x_3453_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(v___y_3452_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
lean_dec_ref(v___y_3452_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; uint8_t v___x_3455_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
v___x_3455_ = lean_unbox(v_a_3454_);
if (v___x_3455_ == 0)
{
return v___x_3453_;
}
else
{
lean_object* v___x_3456_; 
lean_dec_ref_known(v___x_3453_, 1);
v___x_3456_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(v_b_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3456_;
}
}
else
{
return v___x_3453_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue___boxed(lean_object* v_a_3467_, lean_object* v_b_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue(v_a_3467_, v_b_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_a_3470_);
lean_dec_ref(v_a_3469_);
lean_dec_ref(v_b_3468_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue(lean_object* v_e_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v_w_3482_; lean_object* v_v_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___x_3492_; lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3597_; 
v___x_3492_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_3475_, v_a_3477_);
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3597_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3597_;
goto v_resetjp_3494_;
}
v___jp_3481_:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_Meta_isNatValue(v_w_3482_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec_ref(v_w_3482_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; uint8_t v___x_3490_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v___x_3490_ = lean_unbox(v_a_3489_);
if (v___x_3490_ == 0)
{
lean_dec_ref(v_v_3483_);
return v___x_3488_;
}
else
{
lean_object* v___x_3491_; 
lean_dec_ref_known(v___x_3488_, 1);
v___x_3491_ = l_Lean_Meta_isNatValue(v_v_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec_ref(v_v_3483_);
return v___x_3491_;
}
}
else
{
lean_dec_ref(v_v_3483_);
return v___x_3488_;
}
}
v_resetjp_3494_:
{
lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; 
if (lean_obj_tag(v_a_3493_) == 9)
{
lean_object* v_a_3586_; 
v_a_3586_ = lean_ctor_get(v_a_3493_, 0);
lean_inc_ref(v_a_3586_);
if (lean_obj_tag(v_a_3586_) == 1)
{
lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref_known(v_a_3493_, 1);
lean_del_object(v___x_3495_);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_a_3586_);
if (v_isSharedCheck_3595_ == 0)
{
lean_object* v_unused_3596_; 
v_unused_3596_ = lean_ctor_get(v_a_3586_, 0);
lean_dec(v_unused_3596_);
v___x_3588_ = v_a_3586_;
v_isShared_3589_ = v_isSharedCheck_3595_;
goto v_resetjp_3587_;
}
else
{
lean_dec(v_a_3586_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3595_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
uint8_t v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3590_ = 1;
v___x_3591_ = lean_box(v___x_3590_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set_tag(v___x_3588_, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3591_);
v___x_3593_ = v___x_3588_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
else
{
lean_dec_ref(v_a_3586_);
v___y_3498_ = v_a_3476_;
v___y_3499_ = v_a_3477_;
v___y_3500_ = v_a_3478_;
v___y_3501_ = v_a_3479_;
goto v___jp_3497_;
}
}
else
{
v___y_3498_ = v_a_3476_;
v___y_3499_ = v_a_3477_;
v___y_3500_ = v_a_3478_;
v___y_3501_ = v_a_3479_;
goto v___jp_3497_;
}
v___jp_3497_:
{
lean_object* v___x_3502_; uint8_t v___x_3503_; 
v___x_3502_ = l_Lean_Expr_consumeMData(v_a_3493_);
v___x_3503_ = l_Lean_Expr_isRawNatLit(v___x_3502_);
lean_dec_ref(v___x_3502_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; 
lean_del_object(v___x_3495_);
v___x_3504_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_3493_, v___y_3499_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3573_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3507_ = v___x_3504_;
v_isShared_3508_ = v_isSharedCheck_3573_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3504_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3573_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3509_; uint8_t v___x_3510_; 
v___x_3509_ = l_Lean_Expr_cleanupAnnotations(v_a_3505_);
lean_dec(v_a_3505_);
v___x_3510_ = l_Lean_Expr_isApp(v___x_3509_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
lean_dec_ref(v___x_3509_);
v___x_3511_ = lean_box(v___x_3503_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3511_);
v___x_3513_ = v___x_3507_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
else
{
lean_object* v_arg_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; 
v_arg_3515_ = lean_ctor_get(v___x_3509_, 1);
lean_inc_ref(v_arg_3515_);
v___x_3516_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3509_);
lean_dec_ref(v___x_3509_);
v___x_3517_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_3518_ = l_Lean_Expr_isConstOf(v___x_3516_, v___x_3517_);
if (v___x_3518_ == 0)
{
uint8_t v___x_3519_; 
v___x_3519_ = l_Lean_Expr_isApp(v___x_3516_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3520_; lean_object* v___x_3522_; 
lean_dec_ref(v___x_3516_);
lean_dec_ref(v_arg_3515_);
v___x_3520_ = lean_box(v___x_3503_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3520_);
v___x_3522_ = v___x_3507_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
else
{
lean_object* v_arg_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
v_arg_3524_ = lean_ctor_get(v___x_3516_, 1);
lean_inc_ref(v_arg_3524_);
v___x_3525_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3516_);
lean_dec_ref(v___x_3516_);
v___x_3526_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_3527_ = l_Lean_Expr_isConstOf(v___x_3525_, v___x_3526_);
if (v___x_3527_ == 0)
{
uint8_t v___x_3528_; 
v___x_3528_ = l_Lean_Expr_isApp(v___x_3525_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
lean_dec_ref(v___x_3525_);
lean_dec_ref(v_arg_3524_);
lean_dec_ref(v_arg_3515_);
v___x_3529_ = lean_box(v___x_3503_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3529_);
v___x_3531_ = v___x_3507_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
else
{
lean_object* v_arg_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v_arg_3533_ = lean_ctor_get(v___x_3525_, 1);
lean_inc_ref(v_arg_3533_);
v___x_3534_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3525_);
lean_dec_ref(v___x_3525_);
v___x_3535_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__4));
v___x_3536_ = l_Lean_Expr_isConstOf(v___x_3534_, v___x_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; uint8_t v___x_3538_; 
v___x_3537_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_3538_ = l_Lean_Expr_isConstOf(v___x_3534_, v___x_3537_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; uint8_t v___x_3540_; 
v___x_3539_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_3540_ = l_Lean_Expr_isConstOf(v___x_3534_, v___x_3539_);
if (v___x_3540_ == 0)
{
uint8_t v___x_3541_; 
v___x_3541_ = l_Lean_Expr_isApp(v___x_3534_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3544_; 
lean_dec_ref(v___x_3534_);
lean_dec_ref(v_arg_3533_);
lean_dec_ref(v_arg_3524_);
lean_dec_ref(v_arg_3515_);
v___x_3542_ = lean_box(v___x_3503_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3542_);
v___x_3544_ = v___x_3507_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
else
{
lean_object* v___x_3546_; uint8_t v___x_3547_; 
v___x_3546_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3534_);
lean_dec_ref(v___x_3534_);
v___x_3547_ = l_Lean_Expr_isApp(v___x_3546_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3550_; 
lean_dec_ref(v___x_3546_);
lean_dec_ref(v_arg_3533_);
lean_dec_ref(v_arg_3524_);
lean_dec_ref(v_arg_3515_);
v___x_3548_ = lean_box(v___x_3503_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3548_);
v___x_3550_ = v___x_3507_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
else
{
lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v___x_3552_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3546_);
v___x_3553_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_3554_ = l_Lean_Expr_isConstOf(v___x_3552_, v___x_3553_);
if (v___x_3554_ == 0)
{
uint8_t v___x_3555_; 
lean_dec_ref(v___x_3546_);
lean_dec_ref(v_arg_3533_);
v___x_3555_ = l_Lean_Expr_isApp(v___x_3552_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; lean_object* v___x_3558_; 
lean_dec_ref(v___x_3552_);
lean_dec_ref(v_arg_3524_);
lean_dec_ref(v_arg_3515_);
v___x_3556_ = lean_box(v___x_3503_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3556_);
v___x_3558_ = v___x_3507_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
else
{
lean_object* v___x_3560_; lean_object* v___x_3561_; uint8_t v___x_3562_; 
v___x_3560_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3552_);
lean_dec_ref(v___x_3552_);
v___x_3561_ = ((lean_object*)(l_Lean_Meta_getRatValue_x3f___closed__2));
v___x_3562_ = l_Lean_Expr_isConstOf(v___x_3560_, v___x_3561_);
lean_dec_ref(v___x_3560_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; lean_object* v___x_3565_; 
lean_dec_ref(v_arg_3524_);
lean_dec_ref(v_arg_3515_);
v___x_3563_ = lean_box(v___x_3503_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3563_);
v___x_3565_ = v___x_3507_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
else
{
lean_object* v___x_3567_; 
lean_del_object(v___x_3507_);
v___x_3567_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue(v_arg_3524_, v_arg_3515_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec_ref(v_arg_3515_);
return v___x_3567_;
}
}
}
else
{
lean_object* v_arg_3568_; lean_object* v___x_3569_; 
lean_dec_ref(v___x_3552_);
lean_del_object(v___x_3507_);
v_arg_3568_ = lean_ctor_get(v___x_3546_, 1);
lean_inc_ref(v_arg_3568_);
lean_dec_ref(v___x_3546_);
v___x_3569_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(v_arg_3568_, v_arg_3533_, v_arg_3524_, v_arg_3515_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec_ref(v_arg_3515_);
lean_dec_ref(v_arg_3524_);
lean_dec_ref(v_arg_3533_);
return v___x_3569_;
}
}
}
}
else
{
lean_object* v___x_3570_; 
lean_dec_ref(v___x_3534_);
lean_dec_ref(v_arg_3515_);
lean_del_object(v___x_3507_);
v___x_3570_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue(v_arg_3533_, v_arg_3524_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec_ref(v_arg_3524_);
return v___x_3570_;
}
}
else
{
lean_object* v___x_3571_; 
lean_dec_ref(v___x_3534_);
lean_dec_ref(v_arg_3533_);
lean_dec_ref(v_arg_3524_);
lean_del_object(v___x_3507_);
v___x_3571_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue(v_arg_3515_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
return v___x_3571_;
}
}
else
{
lean_dec_ref(v___x_3534_);
lean_dec_ref(v_arg_3515_);
lean_del_object(v___x_3507_);
v_w_3482_ = v_arg_3533_;
v_v_3483_ = v_arg_3524_;
v___y_3484_ = v___y_3498_;
v___y_3485_ = v___y_3499_;
v___y_3486_ = v___y_3500_;
v___y_3487_ = v___y_3501_;
goto v___jp_3481_;
}
}
}
else
{
lean_dec_ref(v___x_3525_);
lean_del_object(v___x_3507_);
v_w_3482_ = v_arg_3524_;
v_v_3483_ = v_arg_3515_;
v___y_3484_ = v___y_3498_;
v___y_3485_ = v___y_3499_;
v___y_3486_ = v___y_3500_;
v___y_3487_ = v___y_3501_;
goto v___jp_3481_;
}
}
}
else
{
lean_object* v___x_3572_; 
lean_dec_ref(v___x_3516_);
lean_del_object(v___x_3507_);
v___x_3572_ = l_Lean_Meta_isNatValue(v_arg_3515_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec_ref(v_arg_3515_);
return v___x_3572_;
}
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
v_a_3574_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3504_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3504_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_object* v___x_3582_; lean_object* v___x_3584_; 
lean_dec(v_a_3493_);
v___x_3582_ = lean_box(v___x_3503_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3582_);
v___x_3584_ = v___x_3495_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue___boxed(lean_object* v_e_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Meta_isLitValue(v_e_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
return v_res_3604_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__2(void){
_start:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3609_ = lean_box(0);
v___x_3610_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__1));
v___x_3611_ = l_Lean_mkConst(v___x_3610_, v___x_3609_);
return v___x_3611_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__5(void){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3616_ = lean_box(0);
v___x_3617_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__4));
v___x_3618_ = l_Lean_mkConst(v___x_3617_, v___x_3616_);
return v___x_3618_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__7(void){
_start:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3622_ = lean_box(0);
v___x_3623_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__6));
v___x_3624_ = l_Lean_mkConst(v___x_3623_, v___x_3622_);
return v___x_3624_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__10(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = lean_box(0);
v___x_3630_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__9));
v___x_3631_ = l_Lean_mkConst(v___x_3630_, v___x_3629_);
return v___x_3631_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__11(void){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = lean_unsigned_to_nat(1u);
v___x_3633_ = lean_nat_to_int(v___x_3632_);
return v___x_3633_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__15(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_3640_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__14));
v___x_3641_ = l_Lean_mkConst(v___x_3640_, v___x_3639_);
return v___x_3641_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__16(void){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3642_ = lean_box(0);
v___x_3643_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_3644_ = l_Lean_mkConst(v___x_3643_, v___x_3642_);
return v___x_3644_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__19(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = lean_box(0);
v___x_3649_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__18));
v___x_3650_ = l_Lean_mkConst(v___x_3649_, v___x_3648_);
return v___x_3650_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__22(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3654_ = lean_box(0);
v___x_3655_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__21));
v___x_3656_ = l_Lean_mkConst(v___x_3655_, v___x_3654_);
return v___x_3656_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__25(void){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = lean_box(0);
v___x_3662_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__24));
v___x_3663_ = l_Lean_mkConst(v___x_3662_, v___x_3661_);
return v___x_3663_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__28(void){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3668_ = lean_box(0);
v___x_3669_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__27));
v___x_3670_ = l_Lean_mkConst(v___x_3669_, v___x_3668_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor(lean_object* v_e_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v___x_3677_; lean_object* v_a_3678_; lean_object* v___x_3679_; 
v___x_3677_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_3671_, v_a_3673_);
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref(v___x_3677_);
v___x_3679_ = l_Lean_Meta_getNatValue_x3f(v_a_3678_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3769_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3682_ = v___x_3679_;
v_isShared_3683_ = v_isSharedCheck_3769_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3679_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3769_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
if (lean_obj_tag(v_a_3680_) == 1)
{
lean_object* v_val_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
lean_dec(v_a_3678_);
v_val_3684_ = lean_ctor_get(v_a_3680_, 0);
lean_inc(v_val_3684_);
lean_dec_ref_known(v_a_3680_, 1);
v___x_3685_ = lean_unsigned_to_nat(0u);
v___x_3686_ = lean_nat_dec_eq(v_val_3684_, v___x_3685_);
if (v___x_3686_ == 0)
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3687_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__2, &l_Lean_Meta_litToCtor___closed__2_once, _init_l_Lean_Meta_litToCtor___closed__2);
v___x_3688_ = lean_unsigned_to_nat(1u);
v___x_3689_ = lean_nat_sub(v_val_3684_, v___x_3688_);
lean_dec(v_val_3684_);
v___x_3690_ = l_Lean_mkNatLit(v___x_3689_);
v___x_3691_ = l_Lean_Expr_app___override(v___x_3687_, v___x_3690_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 0, v___x_3691_);
v___x_3693_ = v___x_3682_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
else
{
lean_object* v___x_3695_; lean_object* v___x_3697_; 
lean_dec(v_val_3684_);
v___x_3695_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__5, &l_Lean_Meta_litToCtor___closed__5_once, _init_l_Lean_Meta_litToCtor___closed__5);
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 0, v___x_3695_);
v___x_3697_ = v___x_3682_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3695_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
else
{
lean_object* v___x_3699_; 
lean_del_object(v___x_3682_);
lean_dec(v_a_3680_);
lean_inc(v_a_3678_);
v___x_3699_ = l_Lean_Meta_getIntValue_x3f(v_a_3678_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3760_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3702_ = v___x_3699_;
v_isShared_3703_ = v_isSharedCheck_3760_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3699_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3760_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
if (lean_obj_tag(v_a_3700_) == 1)
{
lean_object* v_val_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
lean_dec(v_a_3678_);
v_val_3704_ = lean_ctor_get(v_a_3700_, 0);
lean_inc(v_val_3704_);
lean_dec_ref_known(v_a_3700_, 1);
v___x_3705_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_3706_ = lean_int_dec_lt(v_val_3704_, v___x_3705_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3712_; 
v___x_3707_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__7, &l_Lean_Meta_litToCtor___closed__7_once, _init_l_Lean_Meta_litToCtor___closed__7);
v___x_3708_ = l_Int_toNat(v_val_3704_);
lean_dec(v_val_3704_);
v___x_3709_ = l_Lean_mkNatLit(v___x_3708_);
v___x_3710_ = l_Lean_Expr_app___override(v___x_3707_, v___x_3709_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v___x_3710_);
v___x_3712_ = v___x_3702_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3710_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
else
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3722_; 
v___x_3714_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__10, &l_Lean_Meta_litToCtor___closed__10_once, _init_l_Lean_Meta_litToCtor___closed__10);
v___x_3715_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__11, &l_Lean_Meta_litToCtor___closed__11_once, _init_l_Lean_Meta_litToCtor___closed__11);
v___x_3716_ = lean_int_add(v_val_3704_, v___x_3715_);
lean_dec(v_val_3704_);
v___x_3717_ = lean_int_neg(v___x_3716_);
lean_dec(v___x_3716_);
v___x_3718_ = l_Int_toNat(v___x_3717_);
lean_dec(v___x_3717_);
v___x_3719_ = l_Lean_mkNatLit(v___x_3718_);
v___x_3720_ = l_Lean_Expr_app___override(v___x_3714_, v___x_3719_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v___x_3720_);
v___x_3722_ = v___x_3702_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
else
{
lean_object* v___x_3724_; 
lean_del_object(v___x_3702_);
lean_dec(v_a_3700_);
lean_inc(v_a_3678_);
v___x_3724_ = l_Lean_Meta_getFinValue_x3f(v_a_3678_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3751_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3727_ = v___x_3724_;
v_isShared_3728_ = v_isSharedCheck_3751_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3724_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3751_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
if (lean_obj_tag(v_a_3725_) == 1)
{
lean_object* v_val_3729_; lean_object* v_fst_3730_; lean_object* v_snd_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
lean_dec(v_a_3678_);
v_val_3729_ = lean_ctor_get(v_a_3725_, 0);
lean_inc(v_val_3729_);
lean_dec_ref_known(v_a_3725_, 1);
v_fst_3730_ = lean_ctor_get(v_val_3729_, 0);
lean_inc(v_fst_3730_);
v_snd_3731_ = lean_ctor_get(v_val_3729_, 1);
lean_inc(v_snd_3731_);
lean_dec(v_val_3729_);
v___x_3732_ = l_Lean_mkNatLit(v_snd_3731_);
v___x_3733_ = l_Lean_mkNatLit(v_fst_3730_);
v___x_3734_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__15, &l_Lean_Meta_litToCtor___closed__15_once, _init_l_Lean_Meta_litToCtor___closed__15);
v___x_3735_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__16, &l_Lean_Meta_litToCtor___closed__16_once, _init_l_Lean_Meta_litToCtor___closed__16);
v___x_3736_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__19, &l_Lean_Meta_litToCtor___closed__19_once, _init_l_Lean_Meta_litToCtor___closed__19);
lean_inc_ref_n(v___x_3733_, 2);
lean_inc_ref_n(v___x_3732_, 2);
v___x_3737_ = l_Lean_mkApp4(v___x_3734_, v___x_3735_, v___x_3736_, v___x_3732_, v___x_3733_);
v___x_3738_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__22, &l_Lean_Meta_litToCtor___closed__22_once, _init_l_Lean_Meta_litToCtor___closed__22);
v___x_3739_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__25, &l_Lean_Meta_litToCtor___closed__25_once, _init_l_Lean_Meta_litToCtor___closed__25);
v___x_3740_ = l_Lean_mkAppB(v___x_3739_, v___x_3732_, v___x_3733_);
v___x_3741_ = l_Lean_eagerReflBoolTrue;
v___x_3742_ = l_Lean_mkApp3(v___x_3738_, v___x_3737_, v___x_3740_, v___x_3741_);
v___x_3743_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__28, &l_Lean_Meta_litToCtor___closed__28_once, _init_l_Lean_Meta_litToCtor___closed__28);
v___x_3744_ = l_Lean_mkApp3(v___x_3743_, v___x_3733_, v___x_3732_, v___x_3742_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3744_);
v___x_3746_ = v___x_3727_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
else
{
lean_object* v___x_3749_; 
lean_dec(v_a_3725_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v_a_3678_);
v___x_3749_ = v___x_3727_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3678_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec(v_a_3678_);
v_a_3752_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3724_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3724_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_a_3678_);
v_a_3761_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3699_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3699_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec(v_a_3678_);
v_a_3770_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3679_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3679_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor___boxed(lean_object* v_e_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Lean_Meta_litToCtor(v_e_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(lean_object* v_fst_3787_, lean_object* v_snd_3788_, lean_object* v_x_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3795_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0));
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v_fst_3787_);
lean_ctor_set(v___x_3796_, 1, v_snd_3788_);
v___x_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3795_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
v___x_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_fst_3800_, lean_object* v_snd_3801_, lean_object* v_x_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3800_, v_snd_3801_, v_x_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(lean_object* v_f_3820_, lean_object* v_a_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v___y_3828_; lean_object* v_snd_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3936_; 
v_snd_3848_ = lean_ctor_get(v_a_3821_, 1);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_a_3821_);
if (v_isSharedCheck_3936_ == 0)
{
lean_object* v_unused_3937_; 
v_unused_3937_ = lean_ctor_get(v_a_3821_, 0);
lean_dec(v_unused_3937_);
v___x_3850_ = v_a_3821_;
v_isShared_3851_ = v_isSharedCheck_3936_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_snd_3848_);
lean_dec(v_a_3821_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3936_;
goto v_resetjp_3849_;
}
v___jp_3827_:
{
if (lean_obj_tag(v___y_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3839_; 
v_a_3829_ = lean_ctor_get(v___y_3828_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___y_3828_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3831_ = v___y_3828_;
v_isShared_3832_ = v_isSharedCheck_3839_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___y_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3839_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
if (lean_obj_tag(v_a_3829_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; 
lean_dec_ref(v_f_3820_);
v_a_3833_ = lean_ctor_get(v_a_3829_, 0);
lean_inc(v_a_3833_);
lean_dec_ref_known(v_a_3829_, 1);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v_a_3833_);
v___x_3835_ = v___x_3831_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3833_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
else
{
lean_object* v_a_3837_; 
lean_del_object(v___x_3831_);
v_a_3837_ = lean_ctor_get(v_a_3829_, 0);
lean_inc(v_a_3837_);
lean_dec_ref_known(v_a_3829_, 1);
v_a_3821_ = v_a_3837_;
goto _start;
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_dec_ref(v_f_3820_);
v_a_3840_ = lean_ctor_get(v___y_3828_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___y_3828_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___y_3828_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___y_3828_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
v_resetjp_3849_:
{
lean_object* v_fst_3852_; lean_object* v_snd_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3935_; 
v_fst_3852_ = lean_ctor_get(v_snd_3848_, 0);
v_snd_3853_ = lean_ctor_get(v_snd_3848_, 1);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_snd_3848_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3855_ = v_snd_3848_;
v_isShared_3856_ = v_isSharedCheck_3935_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_snd_3853_);
lean_inc(v_fst_3852_);
lean_dec(v_snd_3848_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3935_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = lean_box(0);
lean_inc(v_fst_3852_);
v___x_3858_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_fst_3852_, v___y_3823_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3926_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3861_ = v___x_3858_;
v_isShared_3862_ = v_isSharedCheck_3926_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3858_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3926_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3863_; uint8_t v___x_3864_; 
v___x_3863_ = l_Lean_Expr_cleanupAnnotations(v_a_3859_);
lean_dec(v_a_3859_);
v___x_3864_ = l_Lean_Expr_isApp(v___x_3863_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_dec_ref(v___x_3863_);
lean_del_object(v___x_3861_);
lean_del_object(v___x_3855_);
lean_del_object(v___x_3850_);
v___x_3865_ = lean_box(0);
v___x_3866_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3852_, v_snd_3853_, v___x_3865_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
v___y_3828_ = v___x_3866_;
goto v___jp_3827_;
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; 
v___x_3867_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3863_);
v___x_3868_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2));
v___x_3869_ = l_Lean_Expr_isConstOf(v___x_3867_, v___x_3868_);
if (v___x_3869_ == 0)
{
uint8_t v___x_3870_; 
lean_del_object(v___x_3861_);
v___x_3870_ = l_Lean_Expr_isApp(v___x_3867_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; lean_object* v___x_3872_; 
lean_dec_ref(v___x_3867_);
lean_dec_ref(v___x_3863_);
lean_del_object(v___x_3855_);
lean_del_object(v___x_3850_);
v___x_3871_ = lean_box(0);
v___x_3872_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3852_, v_snd_3853_, v___x_3871_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
v___y_3828_ = v___x_3872_;
goto v___jp_3827_;
}
else
{
lean_object* v___x_3873_; uint8_t v___x_3874_; 
v___x_3873_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3867_);
v___x_3874_ = l_Lean_Expr_isApp(v___x_3873_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
lean_dec_ref(v___x_3873_);
lean_dec_ref(v___x_3867_);
lean_dec_ref(v___x_3863_);
lean_del_object(v___x_3855_);
lean_del_object(v___x_3850_);
v___x_3875_ = lean_box(0);
v___x_3876_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3852_, v_snd_3853_, v___x_3875_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
v___y_3828_ = v___x_3876_;
goto v___jp_3827_;
}
else
{
lean_object* v___x_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; 
v___x_3877_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3873_);
lean_dec_ref(v___x_3873_);
v___x_3878_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4));
v___x_3879_ = l_Lean_Expr_isConstOf(v___x_3877_, v___x_3878_);
lean_dec_ref(v___x_3877_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
lean_dec_ref(v___x_3867_);
lean_dec_ref(v___x_3863_);
lean_del_object(v___x_3855_);
lean_del_object(v___x_3850_);
v___x_3880_ = lean_box(0);
v___x_3881_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3852_, v_snd_3853_, v___x_3880_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
v___y_3828_ = v___x_3881_;
goto v___jp_3827_;
}
else
{
lean_object* v_arg_3882_; lean_object* v_arg_3883_; lean_object* v___x_3884_; 
v_arg_3882_ = lean_ctor_get(v___x_3863_, 1);
lean_inc_ref(v_arg_3882_);
lean_dec_ref(v___x_3863_);
v_arg_3883_ = lean_ctor_get(v___x_3867_, 1);
lean_inc_ref(v_arg_3883_);
lean_dec_ref(v___x_3867_);
lean_inc_ref(v_f_3820_);
lean_inc(v___y_3825_);
lean_inc_ref(v___y_3824_);
lean_inc(v___y_3823_);
lean_inc_ref(v___y_3822_);
v___x_3884_ = lean_apply_6(v_f_3820_, v_arg_3883_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, lean_box(0));
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3908_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3887_ = v___x_3884_;
v_isShared_3888_ = v_isSharedCheck_3908_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3908_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
if (lean_obj_tag(v_a_3885_) == 1)
{
lean_object* v_val_3889_; lean_object* v___x_3890_; lean_object* v___x_3892_; 
lean_del_object(v___x_3887_);
lean_dec(v_fst_3852_);
v_val_3889_ = lean_ctor_get(v_a_3885_, 0);
lean_inc(v_val_3889_);
lean_dec_ref_known(v_a_3885_, 1);
v___x_3890_ = lean_array_push(v_snd_3853_, v_val_3889_);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 1, v___x_3890_);
lean_ctor_set(v___x_3855_, 0, v_arg_3882_);
v___x_3892_ = v___x_3855_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_arg_3882_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v___x_3890_);
v___x_3892_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3894_; 
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v___x_3892_);
lean_ctor_set(v___x_3850_, 0, v___x_3857_);
v___x_3894_ = v___x_3850_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v___x_3892_);
v___x_3894_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
v_a_3821_ = v___x_3894_;
goto _start;
}
}
}
else
{
lean_object* v___x_3898_; lean_object* v___x_3900_; 
lean_dec(v_a_3885_);
lean_dec_ref(v_arg_3882_);
lean_dec_ref(v_f_3820_);
v___x_3898_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5));
if (v_isShared_3856_ == 0)
{
v___x_3900_ = v___x_3855_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_fst_3852_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_snd_3853_);
v___x_3900_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
lean_object* v___x_3902_; 
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v___x_3900_);
lean_ctor_set(v___x_3850_, 0, v___x_3898_);
v___x_3902_ = v___x_3850_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3898_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v___x_3900_);
v___x_3902_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3904_; 
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v___x_3902_);
v___x_3904_ = v___x_3887_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
}
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
lean_dec_ref(v_arg_3882_);
lean_del_object(v___x_3855_);
lean_dec(v_snd_3853_);
lean_dec(v_fst_3852_);
lean_del_object(v___x_3850_);
lean_dec_ref(v_f_3820_);
v_a_3909_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3884_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3884_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3918_; 
lean_dec_ref(v___x_3867_);
lean_dec_ref(v___x_3863_);
lean_dec_ref(v_f_3820_);
if (v_isShared_3856_ == 0)
{
v___x_3918_ = v___x_3855_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_fst_3852_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_snd_3853_);
v___x_3918_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3920_; 
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v___x_3918_);
lean_ctor_set(v___x_3850_, 0, v___x_3857_);
v___x_3920_ = v___x_3850_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v___x_3918_);
v___x_3920_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3922_; 
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v___x_3920_);
v___x_3922_ = v___x_3861_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_del_object(v___x_3855_);
lean_dec(v_snd_3853_);
lean_dec(v_fst_3852_);
lean_del_object(v___x_3850_);
lean_dec_ref(v_f_3820_);
v_a_3927_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3858_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3858_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___boxed(lean_object* v_f_3938_, lean_object* v_a_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_3938_, v_a_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg(lean_object* v_e_3948_, lean_object* v_f_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3992_; 
v___x_3955_ = l_Lean_Expr_consumeMData(v_e_3948_);
v___x_3956_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_3955_, v_a_3951_);
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3992_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3992_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3961_ = ((lean_object*)(l_Lean_Meta_getListLitOf_x3f___redArg___closed__0));
v___x_3962_ = lean_box(0);
v___x_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3963_, 0, v_a_3957_);
lean_ctor_set(v___x_3963_, 1, v___x_3961_);
v___x_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3962_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
v___x_3965_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_3949_, v___x_3964_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3983_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_3983_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3983_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v_fst_3970_; 
v_fst_3970_ = lean_ctor_get(v_a_3966_, 0);
if (lean_obj_tag(v_fst_3970_) == 0)
{
lean_object* v_snd_3971_; lean_object* v_snd_3972_; lean_object* v___x_3974_; 
v_snd_3971_ = lean_ctor_get(v_a_3966_, 1);
lean_inc(v_snd_3971_);
lean_dec(v_a_3966_);
v_snd_3972_ = lean_ctor_get(v_snd_3971_, 1);
lean_inc(v_snd_3972_);
lean_dec(v_snd_3971_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set_tag(v___x_3959_, 1);
lean_ctor_set(v___x_3959_, 0, v_snd_3972_);
v___x_3974_ = v___x_3959_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_snd_3972_);
v___x_3974_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3976_; 
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3974_);
v___x_3976_ = v___x_3968_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
else
{
lean_object* v_val_3979_; lean_object* v___x_3981_; 
lean_inc_ref(v_fst_3970_);
lean_dec(v_a_3966_);
lean_del_object(v___x_3959_);
v_val_3979_ = lean_ctor_get(v_fst_3970_, 0);
lean_inc(v_val_3979_);
lean_dec_ref_known(v_fst_3970_, 1);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v_val_3979_);
v___x_3981_ = v___x_3968_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_val_3979_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_del_object(v___x_3959_);
v_a_3984_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3965_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3965_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___boxed(lean_object* v_e_3993_, lean_object* v_f_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_3993_, v_f_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
lean_dec_ref(v_a_3995_);
lean_dec_ref(v_e_3993_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f(lean_object* v_00_u03b1_4001_, lean_object* v_e_4002_, lean_object* v_f_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_4002_, v_f_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___boxed(lean_object* v_00_u03b1_4010_, lean_object* v_e_4011_, lean_object* v_f_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_Meta_getListLitOf_x3f(v_00_u03b1_4010_, v_e_4011_, v_f_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
lean_dec_ref(v_e_4011_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(lean_object* v_00_u03b1_4019_, lean_object* v_f_4020_, lean_object* v_inst_4021_, lean_object* v_a_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_4020_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___boxed(lean_object* v_00_u03b1_4029_, lean_object* v_f_4030_, lean_object* v_inst_4031_, lean_object* v_a_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(v_00_u03b1_4029_, v_f_4030_, v_inst_4031_, v_a_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0(lean_object* v_s_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4045_, 0, v_s_4039_);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0___boxed(lean_object* v_s_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_Meta_getListLit_x3f___lam__0(v_s_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f(lean_object* v_e_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_){
_start:
{
lean_object* v___f_4061_; lean_object* v___x_4062_; 
v___f_4061_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_4062_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_4055_, v___f_4061_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___boxed(lean_object* v_e_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_Lean_Meta_getListLit_x3f(v_e_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
lean_dec(v_a_4067_);
lean_dec_ref(v_a_4066_);
lean_dec(v_a_4065_);
lean_dec_ref(v_a_4064_);
lean_dec_ref(v_e_4063_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg(lean_object* v_e_4074_, lean_object* v_f_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v_a_4086_; lean_object* v___x_4087_; 
v___x_4084_ = l_Lean_Expr_consumeMData(v_e_4074_);
v___x_4085_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_4084_, v_a_4077_);
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref(v___x_4085_);
v___x_4087_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_4086_, v_a_4077_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4089_; uint8_t v___x_4090_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
lean_inc(v_a_4088_);
lean_dec_ref_known(v___x_4087_, 1);
v___x_4089_ = l_Lean_Expr_cleanupAnnotations(v_a_4088_);
lean_dec(v_a_4088_);
v___x_4090_ = l_Lean_Expr_isApp(v___x_4089_);
if (v___x_4090_ == 0)
{
lean_dec_ref(v___x_4089_);
lean_dec_ref(v_f_4075_);
goto v___jp_4081_;
}
else
{
lean_object* v___x_4091_; uint8_t v___x_4092_; 
v___x_4091_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4089_);
v___x_4092_ = l_Lean_Expr_isApp(v___x_4091_);
if (v___x_4092_ == 0)
{
lean_dec_ref(v___x_4091_);
lean_dec_ref(v___x_4089_);
lean_dec_ref(v_f_4075_);
goto v___jp_4081_;
}
else
{
lean_object* v___x_4093_; lean_object* v___x_4094_; uint8_t v___x_4095_; 
v___x_4093_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4091_);
lean_dec_ref(v___x_4091_);
v___x_4094_ = ((lean_object*)(l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1));
v___x_4095_ = l_Lean_Expr_isConstOf(v___x_4093_, v___x_4094_);
lean_dec_ref(v___x_4093_);
if (v___x_4095_ == 0)
{
lean_dec_ref(v___x_4089_);
lean_dec_ref(v_f_4075_);
goto v___jp_4081_;
}
else
{
lean_object* v_arg_4096_; lean_object* v___x_4097_; 
v_arg_4096_ = lean_ctor_get(v___x_4089_, 1);
lean_inc_ref(v_arg_4096_);
lean_dec_ref(v___x_4089_);
v___x_4097_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_arg_4096_, v_f_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
lean_dec_ref(v_arg_4096_);
return v___x_4097_;
}
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec_ref(v_f_4075_);
v_a_4098_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4087_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4087_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
v___jp_4081_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = lean_box(0);
v___x_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
return v___x_4083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___boxed(lean_object* v_e_4106_, lean_object* v_f_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_4106_, v_f_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_);
lean_dec(v_a_4111_);
lean_dec_ref(v_a_4110_);
lean_dec(v_a_4109_);
lean_dec_ref(v_a_4108_);
lean_dec_ref(v_e_4106_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f(lean_object* v_00_u03b1_4114_, lean_object* v_e_4115_, lean_object* v_f_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_4115_, v_f_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___boxed(lean_object* v_00_u03b1_4123_, lean_object* v_e_4124_, lean_object* v_f_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Lean_Meta_getArrayLitOf_x3f(v_00_u03b1_4123_, v_e_4124_, v_f_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_);
lean_dec(v_a_4129_);
lean_dec_ref(v_a_4128_);
lean_dec(v_a_4127_);
lean_dec_ref(v_a_4126_);
lean_dec_ref(v_e_4124_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object* v_e_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_){
_start:
{
lean_object* v___f_4138_; lean_object* v___x_4139_; 
v___f_4138_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_4139_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_4132_, v___f_4138_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f___boxed(lean_object* v_e_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Meta_getArrayLit_x3f(v_e_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec_ref(v_e_4140_);
return v_res_4146_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_LitValues(builtin);
}
#ifdef __cplusplus
}
#endif
