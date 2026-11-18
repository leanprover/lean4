// Lean compiler output
// Module: Lean.Meta.LitValues
// Imports: public import Lean.Meta.Basic import Init.While import Lean.Util.SafeExponentiation
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
uint8_t l_Lean_isSafeBitVecWidth(lean_object*);
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
lean_dec_ref_known(v_declName_568_, 2);
lean_dec(v_pre_569_);
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
lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v_nExpr_1242_; lean_object* v_vExpr_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___x_1303_; 
lean_inc_ref(v_e_1155_);
v___x_1303_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1155_, v_a_1157_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = l_Lean_Expr_cleanupAnnotations(v_a_1304_);
lean_dec(v_a_1304_);
v___x_1306_ = l_Lean_Expr_isApp(v___x_1305_);
if (v___x_1306_ == 0)
{
lean_dec_ref(v___x_1305_);
v___y_1162_ = v_a_1156_;
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1305_);
v___x_1308_ = l_Lean_Expr_isApp(v___x_1307_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v___x_1307_);
lean_dec_ref(v___x_1305_);
v___y_1162_ = v_a_1156_;
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
goto v___jp_1161_;
}
else
{
lean_object* v_arg_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_arg_1309_ = lean_ctor_get(v___x_1307_, 1);
lean_inc_ref(v_arg_1309_);
v___x_1310_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1307_);
lean_dec_ref(v___x_1307_);
v___x_1311_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_1312_ = l_Lean_Expr_isConstOf(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
uint8_t v___x_1313_; 
lean_dec_ref(v___x_1305_);
v___x_1313_ = l_Lean_Expr_isApp(v___x_1310_);
if (v___x_1313_ == 0)
{
lean_dec_ref(v___x_1310_);
lean_dec_ref(v_arg_1309_);
v___y_1162_ = v_a_1156_;
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1310_);
v___x_1315_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__4));
v___x_1316_ = l_Lean_Expr_isConstOf(v___x_1314_, v___x_1315_);
lean_dec_ref(v___x_1314_);
if (v___x_1316_ == 0)
{
lean_dec_ref(v___x_1310_);
lean_dec_ref(v_arg_1309_);
v___y_1162_ = v_a_1156_;
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
goto v___jp_1161_;
}
else
{
lean_object* v_arg_1317_; 
lean_dec_ref(v_e_1155_);
v_arg_1317_ = lean_ctor_get(v___x_1310_, 1);
lean_inc_ref(v_arg_1317_);
lean_dec_ref(v___x_1310_);
v_nExpr_1242_ = v_arg_1317_;
v_vExpr_1243_ = v_arg_1309_;
v___y_1244_ = v_a_1156_;
v___y_1245_ = v_a_1157_;
v___y_1246_ = v_a_1158_;
v___y_1247_ = v_a_1159_;
goto v___jp_1241_;
}
}
}
else
{
lean_object* v_arg_1318_; 
lean_dec_ref(v___x_1310_);
lean_dec_ref(v_e_1155_);
v_arg_1318_ = lean_ctor_get(v___x_1305_, 1);
lean_inc_ref(v_arg_1318_);
lean_dec_ref(v___x_1305_);
v_nExpr_1242_ = v_arg_1309_;
v_vExpr_1243_ = v_arg_1318_;
v___y_1244_ = v_a_1156_;
v___y_1245_ = v_a_1157_;
v___y_1246_ = v_a_1158_;
v___y_1247_ = v_a_1159_;
goto v___jp_1241_;
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v_e_1155_);
v_a_1319_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1303_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1303_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
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
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1232_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1232_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1232_;
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
lean_object* v_val_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1231_; 
lean_del_object(v___x_1170_);
v_val_1176_ = lean_ctor_get(v_a_1168_, 0);
lean_inc(v_val_1176_);
lean_dec_ref_known(v_a_1168_, 1);
v_fst_1177_ = lean_ctor_get(v_val_1176_, 0);
v_snd_1178_ = lean_ctor_get(v_val_1176_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_val_1176_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1180_ = v_val_1176_;
v_isShared_1181_ = v_isSharedCheck_1231_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snd_1178_);
lean_inc(v_fst_1177_);
lean_dec(v_val_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1231_;
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
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1214_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1214_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1214_;
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
lean_object* v_val_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1213_; 
v_val_1194_ = lean_ctor_get(v_a_1186_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_a_1186_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1196_ = v_a_1186_;
v_isShared_1197_ = v_isSharedCheck_1213_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_val_1194_);
lean_dec(v_a_1186_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1213_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
uint8_t v___x_1198_; 
v___x_1198_ = l_Lean_isSafeBitVecWidth(v_val_1194_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
lean_del_object(v___x_1196_);
lean_dec(v_val_1194_);
lean_del_object(v___x_1180_);
lean_dec(v_fst_1177_);
v___x_1199_ = lean_box(0);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1199_);
v___x_1201_ = v___x_1188_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = l_BitVec_ofNat(v_val_1194_, v_fst_1177_);
lean_dec(v_fst_1177_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1203_);
lean_ctor_set(v___x_1180_, 0, v_val_1194_);
v___x_1205_ = v___x_1180_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_val_1194_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1205_);
v___x_1207_ = v___x_1196_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1207_);
v___x_1209_ = v___x_1188_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
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
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_del_object(v___x_1180_);
lean_dec(v_fst_1177_);
v_a_1215_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1185_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1185_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_del_object(v___x_1180_);
lean_dec(v_fst_1177_);
v_a_1223_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1183_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1183_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
v_a_1233_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1167_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1167_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
v___jp_1241_:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Meta_getNatValue_x3f(v_nExpr_1242_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec_ref(v_nExpr_1242_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1294_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1294_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1294_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
if (lean_obj_tag(v_a_1249_) == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_dec_ref(v_vExpr_1243_);
v___x_1253_ = lean_box(0);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1253_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_object* v_val_1257_; uint8_t v___x_1258_; 
v_val_1257_ = lean_ctor_get(v_a_1249_, 0);
lean_inc(v_val_1257_);
lean_dec_ref_known(v_a_1249_, 1);
v___x_1258_ = l_Lean_isSafeBitVecWidth(v_val_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
lean_dec(v_val_1257_);
lean_dec_ref(v_vExpr_1243_);
v___x_1259_ = lean_box(0);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1259_);
v___x_1261_ = v___x_1251_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
else
{
lean_object* v___x_1263_; 
lean_del_object(v___x_1251_);
v___x_1263_ = l_Lean_Meta_getNatValue_x3f(v_vExpr_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec_ref(v_vExpr_1243_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1285_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1285_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1285_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
if (lean_obj_tag(v_a_1264_) == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
lean_dec(v_val_1257_);
v___x_1268_ = lean_box(0);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1268_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
else
{
lean_object* v_val_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1284_; 
v_val_1272_ = lean_ctor_get(v_a_1264_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_a_1264_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1274_ = v_a_1264_;
v_isShared_1275_ = v_isSharedCheck_1284_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_val_1272_);
lean_dec(v_a_1264_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1284_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1276_ = l_BitVec_ofNat(v_val_1257_, v_val_1272_);
lean_dec(v_val_1272_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v_val_1257_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1277_);
v___x_1279_ = v___x_1274_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1281_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1279_);
v___x_1281_ = v___x_1266_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
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
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_val_1257_);
v_a_1286_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1263_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1263_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v_vExpr_1243_);
v_a_1295_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1248_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1248_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f___boxed(lean_object* v_e_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Meta_getBitVecValue_x3f(v_e_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
return v_res_1333_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__0(void){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__1(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__0, &l_Lean_Meta_getLitValueModulus_x3f___closed__0_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__0);
v___x_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__2(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_cstr_to_nat("4294967296");
v___x_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLitValueModulus_x3f(lean_object* v_00_u03b1_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03b1_1367_, v_a_1369_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = l_Lean_Expr_cleanupAnnotations(v_a_1389_);
lean_dec(v_a_1389_);
v___x_1391_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_1392_ = l_Lean_Expr_isConstOf(v___x_1390_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_1394_ = l_Lean_Expr_isConstOf(v___x_1390_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_1396_ = l_Lean_Expr_isConstOf(v___x_1390_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_1398_ = l_Lean_Expr_isConstOf(v___x_1390_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_1400_ = l_Lean_Expr_isConstOf(v___x_1390_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1401_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_1402_ = l_Lean_Expr_isConstOf(v___x_1390_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_1404_ = l_Lean_Expr_isConstOf(v___x_1390_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_1406_ = l_Lean_Expr_isConstOf(v___x_1390_, v___x_1405_);
if (v___x_1406_ == 0)
{
uint8_t v___x_1407_; 
v___x_1407_ = l_Lean_Expr_isApp(v___x_1390_);
if (v___x_1407_ == 0)
{
lean_dec_ref(v___x_1390_);
goto v___jp_1385_;
}
else
{
lean_object* v_arg_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v_arg_1408_ = lean_ctor_get(v___x_1390_, 1);
lean_inc_ref(v_arg_1408_);
v___x_1409_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1390_);
lean_dec_ref(v___x_1390_);
v___x_1410_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_1411_ = l_Lean_Expr_isConstOf(v___x_1409_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_1413_ = l_Lean_Expr_isConstOf(v___x_1409_, v___x_1412_);
lean_dec_ref(v___x_1409_);
if (v___x_1413_ == 0)
{
lean_dec_ref(v_arg_1408_);
goto v___jp_1385_;
}
else
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_Meta_getNatValue_x3f(v_arg_1408_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
lean_dec_ref(v_arg_1408_);
return v___x_1414_;
}
}
else
{
lean_object* v___x_1415_; 
lean_dec_ref(v___x_1409_);
v___x_1415_ = l_Lean_Meta_getNatValue_x3f(v_arg_1408_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
lean_dec_ref(v_arg_1408_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1442_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1442_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1442_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
if (lean_obj_tag(v_a_1416_) == 1)
{
lean_object* v_val_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1437_; 
v_val_1420_ = lean_ctor_get(v_a_1416_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_a_1416_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1422_ = v_a_1416_;
v_isShared_1423_ = v_isSharedCheck_1437_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_val_1420_);
lean_dec(v_a_1416_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1437_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
uint8_t v___x_1424_; 
v___x_1424_ = l_Lean_isSafeBitVecWidth(v_val_1420_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
lean_del_object(v___x_1422_);
lean_dec(v_val_1420_);
v___x_1425_ = lean_box(0);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1425_);
v___x_1427_ = v___x_1418_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1429_ = lean_unsigned_to_nat(2u);
v___x_1430_ = lean_nat_pow(v___x_1429_, v_val_1420_);
lean_dec(v_val_1420_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1430_);
v___x_1432_ = v___x_1422_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1432_);
v___x_1434_ = v___x_1418_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_dec(v_a_1416_);
v___x_1438_ = lean_box(0);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1438_);
v___x_1440_ = v___x_1418_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
return v___x_1415_;
}
}
}
}
else
{
lean_dec_ref(v___x_1390_);
goto v___jp_1382_;
}
}
else
{
lean_dec_ref(v___x_1390_);
goto v___jp_1379_;
}
}
else
{
lean_dec_ref(v___x_1390_);
goto v___jp_1376_;
}
}
else
{
lean_dec_ref(v___x_1390_);
goto v___jp_1373_;
}
}
else
{
lean_dec_ref(v___x_1390_);
goto v___jp_1382_;
}
}
else
{
lean_dec_ref(v___x_1390_);
goto v___jp_1379_;
}
}
else
{
lean_dec_ref(v___x_1390_);
goto v___jp_1376_;
}
}
else
{
lean_dec_ref(v___x_1390_);
goto v___jp_1373_;
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
v_a_1443_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1388_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1388_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
v___jp_1373_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__1, &l_Lean_Meta_getLitValueModulus_x3f___closed__1_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__1);
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
return v___x_1375_;
}
v___jp_1376_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__2, &l_Lean_Meta_getLitValueModulus_x3f___closed__2_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__2);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
return v___x_1378_;
}
v___jp_1379_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__3));
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
return v___x_1381_;
}
v___jp_1382_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__4));
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
v___jp_1385_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLitValueModulus_x3f___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_Meta_getLitValueModulus_x3f(v_00_u03b1_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object* v_e_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_1465_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1458_, v___x_1464_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1488_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1488_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1488_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
if (lean_obj_tag(v_a_1466_) == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_box(0);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
else
{
lean_object* v_val_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1487_; 
v_val_1474_ = lean_ctor_get(v_a_1466_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_a_1466_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1476_ = v_a_1466_;
v_isShared_1477_ = v_isSharedCheck_1487_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_val_1474_);
lean_dec(v_a_1466_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1487_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v_fst_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v_fst_1478_ = lean_ctor_get(v_val_1474_, 0);
lean_inc(v_fst_1478_);
lean_dec(v_val_1474_);
v___x_1479_ = lean_uint8_of_nat(v_fst_1478_);
lean_dec(v_fst_1478_);
v___x_1480_ = lean_box(v___x_1479_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1480_);
v___x_1482_ = v___x_1476_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1482_);
v___x_1484_ = v___x_1468_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_a_1489_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1465_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1465_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f___boxed(lean_object* v_e_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Meta_getUInt8Value_x3f(v_e_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object* v_e_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_1511_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1504_, v___x_1510_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1534_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1534_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1534_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
if (lean_obj_tag(v_a_1512_) == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1516_ = lean_box(0);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1516_);
v___x_1518_ = v___x_1514_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
else
{
lean_object* v_val_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1533_; 
v_val_1520_ = lean_ctor_get(v_a_1512_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_a_1512_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1522_ = v_a_1512_;
v_isShared_1523_ = v_isSharedCheck_1533_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_val_1520_);
lean_dec(v_a_1512_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1533_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_fst_1524_; uint16_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
v_fst_1524_ = lean_ctor_get(v_val_1520_, 0);
lean_inc(v_fst_1524_);
lean_dec(v_val_1520_);
v___x_1525_ = lean_uint16_of_nat(v_fst_1524_);
lean_dec(v_fst_1524_);
v___x_1526_ = lean_box(v___x_1525_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1526_);
v___x_1528_ = v___x_1522_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1530_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1528_);
v___x_1530_ = v___x_1514_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_a_1535_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1511_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1511_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f___boxed(lean_object* v_e_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Meta_getUInt16Value_x3f(v_e_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object* v_e_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_1557_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1550_, v___x_1556_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1580_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1580_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1580_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
if (lean_obj_tag(v_a_1558_) == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = lean_box(0);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1562_);
v___x_1564_ = v___x_1560_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
else
{
lean_object* v_val_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1579_; 
v_val_1566_ = lean_ctor_get(v_a_1558_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_a_1558_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1568_ = v_a_1558_;
v_isShared_1569_ = v_isSharedCheck_1579_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_val_1566_);
lean_dec(v_a_1558_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1579_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_fst_1570_; uint32_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v_fst_1570_ = lean_ctor_get(v_val_1566_, 0);
lean_inc(v_fst_1570_);
lean_dec(v_val_1566_);
v___x_1571_ = lean_uint32_of_nat(v_fst_1570_);
lean_dec(v_fst_1570_);
v___x_1572_ = lean_box_uint32(v___x_1571_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1572_);
v___x_1574_ = v___x_1568_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1574_);
v___x_1576_ = v___x_1560_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
v_a_1581_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1557_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1557_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f___boxed(lean_object* v_e_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Meta_getUInt32Value_x3f(v_e_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object* v_e_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_1603_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1596_, v___x_1602_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1626_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1626_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1626_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
if (lean_obj_tag(v_a_1604_) == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1608_ = lean_box(0);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1608_);
v___x_1610_ = v___x_1606_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
else
{
lean_object* v_val_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1625_; 
v_val_1612_ = lean_ctor_get(v_a_1604_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_a_1604_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1614_ = v_a_1604_;
v_isShared_1615_ = v_isSharedCheck_1625_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_val_1612_);
lean_dec(v_a_1604_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1625_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_fst_1616_; uint64_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v_fst_1616_ = lean_ctor_get(v_val_1612_, 0);
lean_inc(v_fst_1616_);
lean_dec(v_val_1612_);
v___x_1617_ = lean_uint64_of_nat(v_fst_1616_);
lean_dec(v_fst_1616_);
v___x_1618_ = lean_box_uint64(v___x_1617_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1618_);
v___x_1620_ = v___x_1614_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1622_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1620_);
v___x_1622_ = v___x_1606_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_a_1627_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1603_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1603_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f___boxed(lean_object* v_e_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Meta_getUInt64Value_x3f(v_e_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(lean_object* v_e_1642_, lean_object* v_typeDeclName_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___x_1685_; 
lean_inc_ref(v_e_1642_);
v___x_1685_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1642_, v_a_1645_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1685_, 1);
v___x_1687_ = l_Lean_Expr_cleanupAnnotations(v_a_1686_);
lean_dec(v_a_1686_);
v___x_1688_ = l_Lean_Expr_isApp(v___x_1687_);
if (v___x_1688_ == 0)
{
lean_dec_ref(v___x_1687_);
v___y_1650_ = v_a_1644_;
v___y_1651_ = v_a_1645_;
v___y_1652_ = v_a_1646_;
v___y_1653_ = v_a_1647_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1687_);
v___x_1690_ = l_Lean_Expr_isApp(v___x_1689_);
if (v___x_1690_ == 0)
{
lean_dec_ref(v___x_1689_);
lean_dec_ref(v___x_1687_);
v___y_1650_ = v_a_1644_;
v___y_1651_ = v_a_1645_;
v___y_1652_ = v_a_1646_;
v___y_1653_ = v_a_1647_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1689_);
lean_dec_ref(v___x_1689_);
v___x_1692_ = l_Lean_Expr_isApp(v___x_1691_);
if (v___x_1692_ == 0)
{
lean_dec_ref(v___x_1691_);
lean_dec_ref(v___x_1687_);
v___y_1650_ = v_a_1644_;
v___y_1651_ = v_a_1645_;
v___y_1652_ = v_a_1646_;
v___y_1653_ = v_a_1647_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1691_);
lean_dec_ref(v___x_1691_);
v___x_1694_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1695_ = l_Lean_Expr_isConstOf(v___x_1693_, v___x_1694_);
lean_dec_ref(v___x_1693_);
if (v___x_1695_ == 0)
{
lean_dec_ref(v___x_1687_);
v___y_1650_ = v_a_1644_;
v___y_1651_ = v_a_1645_;
v___y_1652_ = v_a_1646_;
v___y_1653_ = v_a_1647_;
goto v___jp_1649_;
}
else
{
lean_object* v_arg_1696_; lean_object* v___x_1697_; 
lean_dec_ref(v_e_1642_);
v_arg_1696_ = lean_ctor_get(v___x_1687_, 1);
lean_inc_ref(v_arg_1696_);
lean_dec_ref(v___x_1687_);
v___x_1697_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_1696_, v_typeDeclName_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1720_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1720_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1720_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
if (lean_obj_tag(v_a_1698_) == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = lean_box(0);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
else
{
lean_object* v_val_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1719_; 
v_val_1706_ = lean_ctor_get(v_a_1698_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_a_1698_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1708_ = v_a_1698_;
v_isShared_1709_ = v_isSharedCheck_1719_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_val_1706_);
lean_dec(v_a_1698_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1719_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v_fst_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v_fst_1710_ = lean_ctor_get(v_val_1706_, 0);
lean_inc(v_fst_1710_);
lean_dec(v_val_1706_);
v___x_1711_ = lean_nat_to_int(v_fst_1710_);
v___x_1712_ = lean_int_neg(v___x_1711_);
lean_dec(v___x_1711_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1712_);
v___x_1714_ = v___x_1708_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1714_);
v___x_1716_ = v___x_1700_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
v_a_1721_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1697_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1697_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
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
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v_e_1642_);
v_a_1729_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1685_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1685_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
v___jp_1649_:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1642_, v_typeDeclName_1643_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1676_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1676_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1676_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
if (lean_obj_tag(v_a_1655_) == 0)
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = lean_box(0);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
else
{
lean_object* v_val_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1675_; 
v_val_1663_ = lean_ctor_get(v_a_1655_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_a_1655_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1665_ = v_a_1655_;
v_isShared_1666_ = v_isSharedCheck_1675_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_val_1663_);
lean_dec(v_a_1655_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1675_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v_fst_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v_fst_1667_ = lean_ctor_get(v_val_1663_, 0);
lean_inc(v_fst_1667_);
lean_dec(v_val_1663_);
v___x_1668_ = lean_nat_to_int(v_fst_1667_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1668_);
v___x_1670_ = v___x_1665_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1670_);
v___x_1672_ = v___x_1657_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_a_1677_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1654_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1654_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f___boxed(lean_object* v_e_1737_, lean_object* v_typeDeclName_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1737_, v_typeDeclName_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_typeDeclName_1738_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt8Value_x3f(lean_object* v_e_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_1752_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1745_, v___x_1751_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1774_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1774_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1774_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
if (lean_obj_tag(v_a_1753_) == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = lean_box(0);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1757_);
v___x_1759_ = v___x_1755_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
else
{
lean_object* v_val_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1773_; 
v_val_1761_ = lean_ctor_get(v_a_1753_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_a_1753_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1763_ = v_a_1753_;
v_isShared_1764_ = v_isSharedCheck_1773_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_val_1761_);
lean_dec(v_a_1753_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1773_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
uint8_t v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1765_ = lean_int8_of_int(v_val_1761_);
lean_dec(v_val_1761_);
v___x_1766_ = lean_box(v___x_1765_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1766_);
v___x_1768_ = v___x_1763_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1770_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1768_);
v___x_1770_ = v___x_1755_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
v_a_1775_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1752_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1752_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt8Value_x3f___boxed(lean_object* v_e_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_Meta_getInt8Value_x3f(v_e_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt16Value_x3f(lean_object* v_e_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_1797_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1790_, v___x_1796_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1819_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1819_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1819_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
if (lean_obj_tag(v_a_1798_) == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = lean_box(0);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
else
{
lean_object* v_val_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1818_; 
v_val_1806_ = lean_ctor_get(v_a_1798_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_a_1798_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1808_ = v_a_1798_;
v_isShared_1809_ = v_isSharedCheck_1818_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_val_1806_);
lean_dec(v_a_1798_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1818_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
uint16_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1810_ = lean_int16_of_int(v_val_1806_);
lean_dec(v_val_1806_);
v___x_1811_ = lean_box(v___x_1810_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1811_);
v___x_1813_ = v___x_1808_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1815_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1813_);
v___x_1815_ = v___x_1800_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_a_1820_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1797_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1797_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt16Value_x3f___boxed(lean_object* v_e_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_Meta_getInt16Value_x3f(v_e_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt32Value_x3f(lean_object* v_e_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_1842_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1835_, v___x_1841_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1864_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1864_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1864_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
if (lean_obj_tag(v_a_1843_) == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_box(0);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
else
{
lean_object* v_val_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1863_; 
v_val_1851_ = lean_ctor_get(v_a_1843_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_a_1843_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1853_ = v_a_1843_;
v_isShared_1854_ = v_isSharedCheck_1863_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_val_1851_);
lean_dec(v_a_1843_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1863_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
uint32_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1855_ = lean_int32_of_int(v_val_1851_);
lean_dec(v_val_1851_);
v___x_1856_ = lean_box_uint32(v___x_1855_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1856_);
v___x_1858_ = v___x_1853_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1860_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1858_);
v___x_1860_ = v___x_1845_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
v_a_1865_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1842_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1842_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt32Value_x3f___boxed(lean_object* v_e_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_Meta_getInt32Value_x3f(v_e_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt64Value_x3f(lean_object* v_e_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_1887_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1880_, v___x_1886_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1909_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1909_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1909_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
if (lean_obj_tag(v_a_1888_) == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1892_ = lean_box(0);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1892_);
v___x_1894_ = v___x_1890_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
else
{
lean_object* v_val_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1908_; 
v_val_1896_ = lean_ctor_get(v_a_1888_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_a_1888_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1898_ = v_a_1888_;
v_isShared_1899_ = v_isSharedCheck_1908_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_val_1896_);
lean_dec(v_a_1888_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1908_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
uint64_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1900_ = lean_int64_of_int(v_val_1896_);
lean_dec(v_val_1896_);
v___x_1901_ = lean_box_uint64(v___x_1900_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1901_);
v___x_1903_ = v___x_1898_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1903_);
v___x_1905_ = v___x_1890_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_a_1910_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1887_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1887_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt64Value_x3f___boxed(lean_object* v_e_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_Meta_getInt64Value_x3f(v_e_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(lean_object* v_e_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___x_1972_; 
lean_inc_ref(v_e_1928_);
v___x_1972_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1928_, v_a_1930_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
v___x_1974_ = l_Lean_Expr_cleanupAnnotations(v_a_1973_);
lean_dec(v_a_1973_);
v___x_1975_ = l_Lean_Expr_isApp(v___x_1974_);
if (v___x_1975_ == 0)
{
lean_dec_ref(v___x_1974_);
v___y_1935_ = v_a_1929_;
v___y_1936_ = v_a_1930_;
v___y_1937_ = v_a_1931_;
v___y_1938_ = v_a_1932_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1974_);
v___x_1977_ = l_Lean_Expr_isApp(v___x_1976_);
if (v___x_1977_ == 0)
{
lean_dec_ref(v___x_1976_);
lean_dec_ref(v___x_1974_);
v___y_1935_ = v_a_1929_;
v___y_1936_ = v_a_1930_;
v___y_1937_ = v_a_1931_;
v___y_1938_ = v_a_1932_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1976_);
v___x_1979_ = l_Lean_Expr_isApp(v___x_1978_);
if (v___x_1979_ == 0)
{
lean_dec_ref(v___x_1978_);
lean_dec_ref(v___x_1976_);
lean_dec_ref(v___x_1974_);
v___y_1935_ = v_a_1929_;
v___y_1936_ = v_a_1930_;
v___y_1937_ = v_a_1931_;
v___y_1938_ = v_a_1932_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1980_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1978_);
v___x_1981_ = l_Lean_Expr_isApp(v___x_1980_);
if (v___x_1981_ == 0)
{
lean_dec_ref(v___x_1980_);
lean_dec_ref(v___x_1978_);
lean_dec_ref(v___x_1976_);
lean_dec_ref(v___x_1974_);
v___y_1935_ = v_a_1929_;
v___y_1936_ = v_a_1930_;
v___y_1937_ = v_a_1931_;
v___y_1938_ = v_a_1932_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1980_);
lean_dec_ref(v___x_1980_);
v___x_1983_ = l_Lean_Expr_isApp(v___x_1982_);
if (v___x_1983_ == 0)
{
lean_dec_ref(v___x_1982_);
lean_dec_ref(v___x_1978_);
lean_dec_ref(v___x_1976_);
lean_dec_ref(v___x_1974_);
v___y_1935_ = v_a_1929_;
v___y_1936_ = v_a_1930_;
v___y_1937_ = v_a_1931_;
v___y_1938_ = v_a_1932_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1984_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1982_);
v___x_1985_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_1986_ = l_Lean_Expr_isConstOf(v___x_1984_, v___x_1985_);
lean_dec_ref(v___x_1984_);
if (v___x_1986_ == 0)
{
lean_dec_ref(v___x_1982_);
lean_dec_ref(v___x_1978_);
lean_dec_ref(v___x_1976_);
lean_dec_ref(v___x_1974_);
v___y_1935_ = v_a_1929_;
v___y_1936_ = v_a_1930_;
v___y_1937_ = v_a_1931_;
v___y_1938_ = v_a_1932_;
goto v___jp_1934_;
}
else
{
lean_object* v_arg_1987_; lean_object* v_arg_1988_; lean_object* v_arg_1989_; lean_object* v_arg_1990_; lean_object* v___x_1991_; 
lean_dec_ref(v_e_1928_);
v_arg_1987_ = lean_ctor_get(v___x_1974_, 1);
lean_inc_ref(v_arg_1987_);
lean_dec_ref(v___x_1974_);
v_arg_1988_ = lean_ctor_get(v___x_1976_, 1);
lean_inc_ref(v_arg_1988_);
lean_dec_ref(v___x_1976_);
v_arg_1989_ = lean_ctor_get(v___x_1978_, 1);
lean_inc_ref(v_arg_1989_);
lean_dec_ref(v___x_1978_);
v_arg_1990_ = lean_ctor_get(v___x_1982_, 1);
lean_inc_ref(v_arg_1990_);
lean_dec_ref(v___x_1982_);
v___x_1991_ = l_Lean_Meta_whnfD(v_arg_1990_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2059_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2059_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2059_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1997_ = l_Lean_Expr_isConstOf(v_a_1992_, v___x_1996_);
lean_dec(v_a_1992_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1987_);
v___x_1998_ = lean_box(0);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_1998_);
v___x_2000_ = v___x_1994_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
else
{
lean_object* v___x_2002_; 
v___x_2002_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_1988_);
lean_dec_ref(v_arg_1988_);
if (lean_obj_tag(v___x_2002_) == 1)
{
lean_object* v_val_2003_; lean_object* v___x_2004_; 
lean_del_object(v___x_1994_);
v_val_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_val_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = l_Lean_Meta_getNatValue_x3f(v_arg_1989_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec_ref(v_arg_1989_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2046_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2046_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2046_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
if (lean_obj_tag(v_a_2005_) == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
lean_dec(v_val_2003_);
lean_dec_ref(v_arg_1987_);
v___x_2009_ = lean_box(0);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2009_);
v___x_2011_ = v___x_2007_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
else
{
lean_object* v_val_2013_; lean_object* v___x_2014_; 
lean_del_object(v___x_2007_);
v_val_2013_ = lean_ctor_get(v_a_2005_, 0);
lean_inc(v_val_2013_);
lean_dec_ref_known(v_a_2005_, 1);
v___x_2014_ = l_Lean_Meta_getNatValue_x3f(v_arg_1987_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec_ref(v_arg_1987_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2037_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2037_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2037_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
if (lean_obj_tag(v_a_2015_) == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
lean_dec(v_val_2013_);
lean_dec(v_val_2003_);
v___x_2019_ = lean_box(0);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
else
{
lean_object* v_val_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2036_; 
v_val_2023_ = lean_ctor_get(v_a_2015_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2025_ = v_a_2015_;
v_isShared_2026_ = v_isSharedCheck_2036_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_val_2023_);
lean_dec(v_a_2015_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2036_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
uint8_t v___x_2027_; double v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2027_ = lean_unbox(v_val_2003_);
lean_dec(v_val_2003_);
v___x_2028_ = l_Float_ofScientific(v_val_2013_, v___x_2027_, v_val_2023_);
v___x_2029_ = lean_box_float(v___x_2028_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2029_);
v___x_2031_ = v___x_2025_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2031_);
v___x_2033_ = v___x_2017_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_val_2013_);
lean_dec(v_val_2003_);
v_a_2038_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2014_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2014_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_val_2003_);
lean_dec_ref(v_arg_1987_);
v_a_2047_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2004_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2004_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
lean_dec(v___x_2002_);
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_arg_1987_);
v___x_2055_ = lean_box(0);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_2055_);
v___x_2057_ = v___x_1994_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1987_);
v_a_2060_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_1991_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_1991_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
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
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v_e_1928_);
v_a_2068_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_1972_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_1972_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
v___jp_1934_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1940_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1928_, v___x_1939_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1963_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1963_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1963_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
if (lean_obj_tag(v_a_1941_) == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1945_ = lean_box(0);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1945_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
else
{
lean_object* v_val_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1962_; 
v_val_1949_ = lean_ctor_get(v_a_1941_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_a_1941_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1951_ = v_a_1941_;
v_isShared_1952_ = v_isSharedCheck_1962_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_val_1949_);
lean_dec(v_a_1941_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1962_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_fst_1953_; double v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v_fst_1953_ = lean_ctor_get(v_val_1949_, 0);
lean_inc(v_fst_1953_);
lean_dec(v_val_1949_);
v___x_1954_ = lean_float_of_nat(v_fst_1953_);
v___x_1955_ = lean_box_float(v___x_1954_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1955_);
v___x_1957_ = v___x_1951_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1959_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1957_);
v___x_1959_ = v___x_1943_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
v_a_1964_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1940_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1940_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___boxed(lean_object* v_e_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f(lean_object* v_e_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v___x_2092_; 
lean_inc_ref(v_e_2083_);
v___x_2092_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
if (lean_obj_tag(v_a_2093_) == 1)
{
lean_dec_ref(v_e_2083_);
return v___x_2092_;
}
else
{
lean_object* v___x_2094_; 
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2083_, v_a_2085_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = l_Lean_Expr_cleanupAnnotations(v_a_2095_);
lean_dec(v_a_2095_);
v___x_2097_ = l_Lean_Expr_isApp(v___x_2096_);
if (v___x_2097_ == 0)
{
lean_dec_ref(v___x_2096_);
goto v___jp_2089_;
}
else
{
lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2098_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2096_);
v___x_2099_ = l_Lean_Expr_isApp(v___x_2098_);
if (v___x_2099_ == 0)
{
lean_dec_ref(v___x_2098_);
lean_dec_ref(v___x_2096_);
goto v___jp_2089_;
}
else
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2098_);
lean_dec_ref(v___x_2098_);
v___x_2101_ = l_Lean_Expr_isApp(v___x_2100_);
if (v___x_2101_ == 0)
{
lean_dec_ref(v___x_2100_);
lean_dec_ref(v___x_2096_);
goto v___jp_2089_;
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2100_);
lean_dec_ref(v___x_2100_);
v___x_2103_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_2104_ = l_Lean_Expr_isConstOf(v___x_2102_, v___x_2103_);
lean_dec_ref(v___x_2102_);
if (v___x_2104_ == 0)
{
lean_dec_ref(v___x_2096_);
goto v___jp_2089_;
}
else
{
lean_object* v_arg_2105_; lean_object* v___x_2106_; 
v_arg_2105_ = lean_ctor_get(v___x_2096_, 1);
lean_inc_ref(v_arg_2105_);
lean_dec_ref(v___x_2096_);
v___x_2106_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_arg_2105_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2129_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2129_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2129_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
if (lean_obj_tag(v_a_2107_) == 1)
{
lean_object* v_val_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2124_; 
v_val_2111_ = lean_ctor_get(v_a_2107_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_a_2107_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2113_ = v_a_2107_;
v_isShared_2114_ = v_isSharedCheck_2124_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_val_2111_);
lean_dec(v_a_2107_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2124_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
double v___x_2115_; double v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2115_ = lean_unbox_float(v_val_2111_);
lean_dec(v_val_2111_);
v___x_2116_ = lean_float_negate(v___x_2115_);
v___x_2117_ = lean_box_float(v___x_2116_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2117_);
v___x_2119_ = v___x_2113_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2121_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2119_);
v___x_2121_ = v___x_2109_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
lean_dec(v_a_2107_);
v___x_2125_ = lean_box(0);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2125_);
v___x_2127_ = v___x_2109_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
return v___x_2106_;
}
}
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_a_2130_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2094_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2094_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2083_);
return v___x_2092_;
}
v___jp_2089_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = lean_box(0);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f___boxed(lean_object* v_e_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Meta_getFloatValue_x3f(v_e_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(lean_object* v_e_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___x_2192_; 
lean_inc_ref(v_e_2148_);
v___x_2192_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2148_, v_a_2150_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v___x_2194_ = l_Lean_Expr_cleanupAnnotations(v_a_2193_);
lean_dec(v_a_2193_);
v___x_2195_ = l_Lean_Expr_isApp(v___x_2194_);
if (v___x_2195_ == 0)
{
lean_dec_ref(v___x_2194_);
v___y_2155_ = v_a_2149_;
v___y_2156_ = v_a_2150_;
v___y_2157_ = v_a_2151_;
v___y_2158_ = v_a_2152_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2196_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2194_);
v___x_2197_ = l_Lean_Expr_isApp(v___x_2196_);
if (v___x_2197_ == 0)
{
lean_dec_ref(v___x_2196_);
lean_dec_ref(v___x_2194_);
v___y_2155_ = v_a_2149_;
v___y_2156_ = v_a_2150_;
v___y_2157_ = v_a_2151_;
v___y_2158_ = v_a_2152_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2196_);
v___x_2199_ = l_Lean_Expr_isApp(v___x_2198_);
if (v___x_2199_ == 0)
{
lean_dec_ref(v___x_2198_);
lean_dec_ref(v___x_2196_);
lean_dec_ref(v___x_2194_);
v___y_2155_ = v_a_2149_;
v___y_2156_ = v_a_2150_;
v___y_2157_ = v_a_2151_;
v___y_2158_ = v_a_2152_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2198_);
v___x_2201_ = l_Lean_Expr_isApp(v___x_2200_);
if (v___x_2201_ == 0)
{
lean_dec_ref(v___x_2200_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v___x_2196_);
lean_dec_ref(v___x_2194_);
v___y_2155_ = v_a_2149_;
v___y_2156_ = v_a_2150_;
v___y_2157_ = v_a_2151_;
v___y_2158_ = v_a_2152_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2200_);
lean_dec_ref(v___x_2200_);
v___x_2203_ = l_Lean_Expr_isApp(v___x_2202_);
if (v___x_2203_ == 0)
{
lean_dec_ref(v___x_2202_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v___x_2196_);
lean_dec_ref(v___x_2194_);
v___y_2155_ = v_a_2149_;
v___y_2156_ = v_a_2150_;
v___y_2157_ = v_a_2151_;
v___y_2158_ = v_a_2152_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2202_);
v___x_2205_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_2206_ = l_Lean_Expr_isConstOf(v___x_2204_, v___x_2205_);
lean_dec_ref(v___x_2204_);
if (v___x_2206_ == 0)
{
lean_dec_ref(v___x_2202_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v___x_2196_);
lean_dec_ref(v___x_2194_);
v___y_2155_ = v_a_2149_;
v___y_2156_ = v_a_2150_;
v___y_2157_ = v_a_2151_;
v___y_2158_ = v_a_2152_;
goto v___jp_2154_;
}
else
{
lean_object* v_arg_2207_; lean_object* v_arg_2208_; lean_object* v_arg_2209_; lean_object* v_arg_2210_; lean_object* v___x_2211_; 
lean_dec_ref(v_e_2148_);
v_arg_2207_ = lean_ctor_get(v___x_2194_, 1);
lean_inc_ref(v_arg_2207_);
lean_dec_ref(v___x_2194_);
v_arg_2208_ = lean_ctor_get(v___x_2196_, 1);
lean_inc_ref(v_arg_2208_);
lean_dec_ref(v___x_2196_);
v_arg_2209_ = lean_ctor_get(v___x_2198_, 1);
lean_inc_ref(v_arg_2209_);
lean_dec_ref(v___x_2198_);
v_arg_2210_ = lean_ctor_get(v___x_2202_, 1);
lean_inc_ref(v_arg_2210_);
lean_dec_ref(v___x_2202_);
v___x_2211_ = l_Lean_Meta_whnfD(v_arg_2210_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2279_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2279_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2279_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_2217_ = l_Lean_Expr_isConstOf(v_a_2212_, v___x_2216_);
lean_dec(v_a_2212_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
lean_dec_ref(v_arg_2209_);
lean_dec_ref(v_arg_2208_);
lean_dec_ref(v_arg_2207_);
v___x_2218_ = lean_box(0);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2218_);
v___x_2220_ = v___x_2214_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
else
{
lean_object* v___x_2222_; 
v___x_2222_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_2208_);
lean_dec_ref(v_arg_2208_);
if (lean_obj_tag(v___x_2222_) == 1)
{
lean_object* v_val_2223_; lean_object* v___x_2224_; 
lean_del_object(v___x_2214_);
v_val_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_val_2223_);
lean_dec_ref_known(v___x_2222_, 1);
v___x_2224_ = l_Lean_Meta_getNatValue_x3f(v_arg_2209_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec_ref(v_arg_2209_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2266_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2266_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2266_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
if (lean_obj_tag(v_a_2225_) == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
lean_dec(v_val_2223_);
lean_dec_ref(v_arg_2207_);
v___x_2229_ = lean_box(0);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
else
{
lean_object* v_val_2233_; lean_object* v___x_2234_; 
lean_del_object(v___x_2227_);
v_val_2233_ = lean_ctor_get(v_a_2225_, 0);
lean_inc(v_val_2233_);
lean_dec_ref_known(v_a_2225_, 1);
v___x_2234_ = l_Lean_Meta_getNatValue_x3f(v_arg_2207_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec_ref(v_arg_2207_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2257_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2257_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2257_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
if (lean_obj_tag(v_a_2235_) == 0)
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_dec(v_val_2233_);
lean_dec(v_val_2223_);
v___x_2239_ = lean_box(0);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
else
{
lean_object* v_val_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2256_; 
v_val_2243_ = lean_ctor_get(v_a_2235_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_a_2235_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2245_ = v_a_2235_;
v_isShared_2246_ = v_isSharedCheck_2256_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_val_2243_);
lean_dec(v_a_2235_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2256_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
uint8_t v___x_2247_; float v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2247_ = lean_unbox(v_val_2223_);
lean_dec(v_val_2223_);
v___x_2248_ = l_Float32_ofScientific(v_val_2233_, v___x_2247_, v_val_2243_);
v___x_2249_ = lean_box_float32(v___x_2248_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2249_);
v___x_2251_ = v___x_2245_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2251_);
v___x_2253_ = v___x_2237_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_val_2233_);
lean_dec(v_val_2223_);
v_a_2258_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2234_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2234_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v_val_2223_);
lean_dec_ref(v_arg_2207_);
v_a_2267_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2224_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2224_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
lean_dec(v___x_2222_);
lean_dec_ref(v_arg_2209_);
lean_dec_ref(v_arg_2207_);
v___x_2275_ = lean_box(0);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2275_);
v___x_2277_ = v___x_2214_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v_arg_2209_);
lean_dec_ref(v_arg_2208_);
lean_dec_ref(v_arg_2207_);
v_a_2280_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2211_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2211_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
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
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec_ref(v_e_2148_);
v_a_2288_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2192_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2192_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
v___jp_2154_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_2160_ = l_Lean_Meta_getOfNatValue_x3f(v_e_2148_, v___x_2159_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2183_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2183_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2183_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
if (lean_obj_tag(v_a_2161_) == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = lean_box(0);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2165_);
v___x_2167_ = v___x_2163_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
else
{
lean_object* v_val_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2182_; 
v_val_2169_ = lean_ctor_get(v_a_2161_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_a_2161_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2171_ = v_a_2161_;
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_val_2169_);
lean_dec(v_a_2161_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v_fst_2173_; float v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
v_fst_2173_ = lean_ctor_get(v_val_2169_, 0);
lean_inc(v_fst_2173_);
lean_dec(v_val_2169_);
v___x_2174_ = lean_float32_of_nat(v_fst_2173_);
v___x_2175_ = lean_box_float32(v___x_2174_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2175_);
v___x_2177_ = v___x_2171_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2179_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2177_);
v___x_2179_ = v___x_2163_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
v_a_2184_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2160_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2160_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___boxed(lean_object* v_e_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f(lean_object* v_e_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___x_2312_; 
lean_inc_ref(v_e_2303_);
v___x_2312_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
if (lean_obj_tag(v_a_2313_) == 1)
{
lean_dec_ref(v_e_2303_);
return v___x_2312_;
}
else
{
lean_object* v___x_2314_; 
lean_dec_ref_known(v___x_2312_, 1);
v___x_2314_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2303_, v_a_2305_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = l_Lean_Expr_cleanupAnnotations(v_a_2315_);
lean_dec(v_a_2315_);
v___x_2317_ = l_Lean_Expr_isApp(v___x_2316_);
if (v___x_2317_ == 0)
{
lean_dec_ref(v___x_2316_);
goto v___jp_2309_;
}
else
{
lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2316_);
v___x_2319_ = l_Lean_Expr_isApp(v___x_2318_);
if (v___x_2319_ == 0)
{
lean_dec_ref(v___x_2318_);
lean_dec_ref(v___x_2316_);
goto v___jp_2309_;
}
else
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2318_);
lean_dec_ref(v___x_2318_);
v___x_2321_ = l_Lean_Expr_isApp(v___x_2320_);
if (v___x_2321_ == 0)
{
lean_dec_ref(v___x_2320_);
lean_dec_ref(v___x_2316_);
goto v___jp_2309_;
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2320_);
lean_dec_ref(v___x_2320_);
v___x_2323_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_2324_ = l_Lean_Expr_isConstOf(v___x_2322_, v___x_2323_);
lean_dec_ref(v___x_2322_);
if (v___x_2324_ == 0)
{
lean_dec_ref(v___x_2316_);
goto v___jp_2309_;
}
else
{
lean_object* v_arg_2325_; lean_object* v___x_2326_; 
v_arg_2325_ = lean_ctor_get(v___x_2316_, 1);
lean_inc_ref(v_arg_2325_);
lean_dec_ref(v___x_2316_);
v___x_2326_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_arg_2325_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2349_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2349_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2349_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
if (lean_obj_tag(v_a_2327_) == 1)
{
lean_object* v_val_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2344_; 
v_val_2331_ = lean_ctor_get(v_a_2327_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_a_2327_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2333_ = v_a_2327_;
v_isShared_2334_ = v_isSharedCheck_2344_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_val_2331_);
lean_dec(v_a_2327_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2344_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
float v___x_2335_; float v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2335_ = lean_unbox_float32(v_val_2331_);
lean_dec(v_val_2331_);
v___x_2336_ = lean_float32_negate(v___x_2335_);
v___x_2337_ = lean_box_float32(v___x_2336_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2337_);
v___x_2339_ = v___x_2333_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2341_; 
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2339_);
v___x_2341_ = v___x_2329_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
lean_dec(v_a_2327_);
v___x_2345_ = lean_box(0);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2345_);
v___x_2347_ = v___x_2329_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
return v___x_2326_;
}
}
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
v_a_2350_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2314_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2314_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2303_);
return v___x_2312_;
}
v___jp_2309_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_box(0);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
return v___x_2311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f___boxed(lean_object* v_e_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_Meta_getFloat32Value_x3f(v_e_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_floatLitValuesEq_x3f(lean_object* v_a_2365_, lean_object* v_b_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___x_2422_; 
lean_inc_ref(v_a_2365_);
v___x_2422_ = l_Lean_Meta_getFloatValue_x3f(v_a_2365_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
if (lean_obj_tag(v_a_2423_) == 1)
{
lean_object* v_val_2424_; lean_object* v___x_2425_; 
v_val_2424_ = lean_ctor_get(v_a_2423_, 0);
lean_inc(v_val_2424_);
lean_dec_ref_known(v_a_2423_, 1);
lean_inc_ref(v_b_2366_);
v___x_2425_ = l_Lean_Meta_getFloatValue_x3f(v_b_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2447_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2447_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2447_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
if (lean_obj_tag(v_a_2426_) == 1)
{
lean_object* v_val_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2446_; 
lean_dec_ref(v_b_2366_);
lean_dec_ref(v_a_2365_);
v_val_2430_ = lean_ctor_get(v_a_2426_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_a_2426_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2432_ = v_a_2426_;
v_isShared_2433_ = v_isSharedCheck_2446_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_val_2430_);
lean_dec(v_a_2426_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2446_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
double v___x_2434_; uint64_t v___x_2435_; double v___x_2436_; uint64_t v___x_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
v___x_2434_ = lean_unbox_float(v_val_2424_);
lean_dec(v_val_2424_);
v___x_2435_ = lean_float_to_bits(v___x_2434_);
v___x_2436_ = lean_unbox_float(v_val_2430_);
lean_dec(v_val_2430_);
v___x_2437_ = lean_float_to_bits(v___x_2436_);
v___x_2438_ = lean_uint64_dec_eq(v___x_2435_, v___x_2437_);
v___x_2439_ = lean_box(v___x_2438_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2439_);
v___x_2441_ = v___x_2432_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2443_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2441_);
v___x_2443_ = v___x_2428_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
else
{
lean_del_object(v___x_2428_);
lean_dec(v_a_2426_);
lean_dec(v_val_2424_);
v___y_2376_ = v_a_2367_;
v___y_2377_ = v_a_2368_;
v___y_2378_ = v_a_2369_;
v___y_2379_ = v_a_2370_;
goto v___jp_2375_;
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v_val_2424_);
lean_dec_ref(v_b_2366_);
lean_dec_ref(v_a_2365_);
v_a_2448_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2425_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2425_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
lean_dec(v_a_2423_);
v___y_2376_ = v_a_2367_;
v___y_2377_ = v_a_2368_;
v___y_2378_ = v_a_2369_;
v___y_2379_ = v_a_2370_;
goto v___jp_2375_;
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v_b_2366_);
lean_dec_ref(v_a_2365_);
v_a_2456_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2422_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2422_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
v___jp_2372_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
v___jp_2375_:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_Meta_getFloat32Value_x3f(v_a_2365_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
if (lean_obj_tag(v_a_2381_) == 1)
{
lean_object* v_val_2382_; lean_object* v___x_2383_; 
v_val_2382_ = lean_ctor_get(v_a_2381_, 0);
lean_inc(v_val_2382_);
lean_dec_ref_known(v_a_2381_, 1);
v___x_2383_ = l_Lean_Meta_getFloat32Value_x3f(v_b_2366_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2405_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2405_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2405_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
if (lean_obj_tag(v_a_2384_) == 1)
{
lean_object* v_val_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2404_; 
v_val_2388_ = lean_ctor_get(v_a_2384_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_a_2384_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2390_ = v_a_2384_;
v_isShared_2391_ = v_isSharedCheck_2404_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_val_2388_);
lean_dec(v_a_2384_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2404_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
float v___x_2392_; uint32_t v___x_2393_; float v___x_2394_; uint32_t v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2392_ = lean_unbox_float32(v_val_2382_);
lean_dec(v_val_2382_);
v___x_2393_ = lean_float32_to_bits(v___x_2392_);
v___x_2394_ = lean_unbox_float32(v_val_2388_);
lean_dec(v_val_2388_);
v___x_2395_ = lean_float32_to_bits(v___x_2394_);
v___x_2396_ = lean_uint32_dec_eq(v___x_2393_, v___x_2395_);
v___x_2397_ = lean_box(v___x_2396_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2397_);
v___x_2399_ = v___x_2390_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2401_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2399_);
v___x_2401_ = v___x_2386_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_del_object(v___x_2386_);
lean_dec(v_a_2384_);
lean_dec(v_val_2382_);
goto v___jp_2372_;
}
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec(v_val_2382_);
v_a_2406_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2383_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2383_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_dec(v_a_2381_);
lean_dec_ref(v_b_2366_);
goto v___jp_2372_;
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec_ref(v_b_2366_);
v_a_2414_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2380_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2380_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_floatLitValuesEq_x3f___boxed(lean_object* v_a_2464_, lean_object* v_b_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_Meta_floatLitValuesEq_x3f(v_a_2464_, v_b_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(lean_object* v_e_2472_, lean_object* v___y_2473_){
_start:
{
uint8_t v___x_2475_; 
v___x_2475_ = l_Lean_Expr_hasMVar(v_e_2472_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v_e_2472_);
return v___x_2476_;
}
else
{
lean_object* v___x_2477_; lean_object* v_mctx_2478_; lean_object* v___x_2479_; lean_object* v_fst_2480_; lean_object* v_snd_2481_; lean_object* v___x_2482_; lean_object* v_cache_2483_; lean_object* v_zetaDeltaFVarIds_2484_; lean_object* v_postponed_2485_; lean_object* v_diag_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2495_; 
v___x_2477_ = lean_st_ref_get(v___y_2473_);
v_mctx_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc_ref(v_mctx_2478_);
lean_dec(v___x_2477_);
v___x_2479_ = l_Lean_instantiateMVarsCore(v_mctx_2478_, v_e_2472_);
v_fst_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_fst_2480_);
v_snd_2481_ = lean_ctor_get(v___x_2479_, 1);
lean_inc(v_snd_2481_);
lean_dec_ref(v___x_2479_);
v___x_2482_ = lean_st_ref_take(v___y_2473_);
v_cache_2483_ = lean_ctor_get(v___x_2482_, 1);
v_zetaDeltaFVarIds_2484_ = lean_ctor_get(v___x_2482_, 2);
v_postponed_2485_ = lean_ctor_get(v___x_2482_, 3);
v_diag_2486_ = lean_ctor_get(v___x_2482_, 4);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v___x_2482_, 0);
lean_dec(v_unused_2496_);
v___x_2488_ = v___x_2482_;
v_isShared_2489_ = v_isSharedCheck_2495_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_diag_2486_);
lean_inc(v_postponed_2485_);
lean_inc(v_zetaDeltaFVarIds_2484_);
lean_inc(v_cache_2483_);
lean_dec(v___x_2482_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2495_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v_snd_2481_);
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_snd_2481_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_cache_2483_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_zetaDeltaFVarIds_2484_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v_postponed_2485_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v_diag_2486_);
v___x_2491_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_st_ref_put(v___y_2473_, v___x_2491_);
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v_fst_2480_);
return v___x_2493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg___boxed(lean_object* v_e_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2497_, v___y_2498_);
lean_dec(v___y_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(lean_object* v_e_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2501_, v___y_2503_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___boxed(lean_object* v_e_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(v_e_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
return v_res_2514_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__0(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_unsigned_to_nat(0u);
v___x_2516_ = lean_nat_to_int(v___x_2515_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__1(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = l_Lean_Level_ofNat(v___x_2517_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__2(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = lean_box(0);
v___x_2520_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__1, &l_Lean_Meta_normLitValue___closed__1_once, _init_l_Lean_Meta_normLitValue___closed__1);
v___x_2521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v___x_2519_);
return v___x_2521_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__3(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_2523_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_2524_ = l_Lean_Expr_const___override(v___x_2523_, v___x_2522_);
return v___x_2524_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__4(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_box(0);
v___x_2526_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_2527_ = l_Lean_Expr_const___override(v___x_2526_, v___x_2525_);
return v___x_2527_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__7(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = lean_box(0);
v___x_2533_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__6));
v___x_2534_ = l_Lean_Expr_const___override(v___x_2533_, v___x_2532_);
return v___x_2534_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__8(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_2536_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_2537_ = l_Lean_Expr_const___override(v___x_2536_, v___x_2535_);
return v___x_2537_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__9(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = lean_box(0);
v___x_2539_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_2540_ = l_Lean_mkConst(v___x_2539_, v___x_2538_);
return v___x_2540_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__12(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_box(0);
v___x_2546_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__11));
v___x_2547_ = l_Lean_Expr_const___override(v___x_2546_, v___x_2545_);
return v___x_2547_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__15(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = lean_box(0);
v___x_2553_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__14));
v___x_2554_ = l_Lean_Expr_const___override(v___x_2553_, v___x_2552_);
return v___x_2554_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__16(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = lean_box(0);
v___x_2556_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_2557_ = l_Lean_Expr_const___override(v___x_2556_, v___x_2555_);
return v___x_2557_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__17(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = lean_box(0);
v___x_2559_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_2560_ = l_Lean_mkConst(v___x_2559_, v___x_2558_);
return v___x_2560_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__18(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = lean_box(0);
v___x_2562_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_2563_ = l_Lean_mkConst(v___x_2562_, v___x_2561_);
return v___x_2563_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__20(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2567_ = lean_box(0);
v___x_2568_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__19));
v___x_2569_ = l_Lean_Expr_const___override(v___x_2568_, v___x_2567_);
return v___x_2569_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__21(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_box(0);
v___x_2571_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_2572_ = l_Lean_mkConst(v___x_2571_, v___x_2570_);
return v___x_2572_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__23(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = lean_box(0);
v___x_2577_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__22));
v___x_2578_ = l_Lean_Expr_const___override(v___x_2577_, v___x_2576_);
return v___x_2578_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__24(void){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = lean_box(0);
v___x_2580_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_2581_ = l_Lean_mkConst(v___x_2580_, v___x_2579_);
return v___x_2581_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__26(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_box(0);
v___x_2586_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__25));
v___x_2587_ = l_Lean_Expr_const___override(v___x_2586_, v___x_2585_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__27(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = lean_box(0);
v___x_2589_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_2590_ = l_Lean_mkConst(v___x_2589_, v___x_2588_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__29(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_box(0);
v___x_2595_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__28));
v___x_2596_ = l_Lean_Expr_const___override(v___x_2595_, v___x_2594_);
return v___x_2596_;
}
}
static uint8_t _init_l_Lean_Meta_normLitValue___closed__30(void){
_start:
{
lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2597_ = lean_unsigned_to_nat(0u);
v___x_2598_ = lean_int8_of_nat(v___x_2597_);
return v___x_2598_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__31(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = lean_box(0);
v___x_2600_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_2601_ = l_Lean_Expr_const___override(v___x_2600_, v___x_2599_);
return v___x_2601_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__34(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = lean_box(0);
v___x_2607_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__33));
v___x_2608_ = l_Lean_Expr_const___override(v___x_2607_, v___x_2606_);
return v___x_2608_;
}
}
static uint16_t _init_l_Lean_Meta_normLitValue___closed__35(void){
_start:
{
lean_object* v___x_2609_; uint16_t v___x_2610_; 
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_int16_of_nat(v___x_2609_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__36(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_box(0);
v___x_2612_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_2613_ = l_Lean_Expr_const___override(v___x_2612_, v___x_2611_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__38(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_box(0);
v___x_2618_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__37));
v___x_2619_ = l_Lean_Expr_const___override(v___x_2618_, v___x_2617_);
return v___x_2619_;
}
}
static uint32_t _init_l_Lean_Meta_normLitValue___closed__39(void){
_start:
{
lean_object* v___x_2620_; uint32_t v___x_2621_; 
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_int32_of_nat(v___x_2620_);
return v___x_2621_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__40(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = lean_box(0);
v___x_2623_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_2624_ = l_Lean_Expr_const___override(v___x_2623_, v___x_2622_);
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__42(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_box(0);
v___x_2629_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__41));
v___x_2630_ = l_Lean_Expr_const___override(v___x_2629_, v___x_2628_);
return v___x_2630_;
}
}
static uint64_t _init_l_Lean_Meta_normLitValue___closed__43(void){
_start:
{
lean_object* v___x_2631_; uint64_t v___x_2632_; 
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = lean_int64_of_nat(v___x_2631_);
return v___x_2632_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__44(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_box(0);
v___x_2634_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_2635_ = l_Lean_Expr_const___override(v___x_2634_, v___x_2633_);
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__46(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = lean_box(0);
v___x_2640_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__45));
v___x_2641_ = l_Lean_Expr_const___override(v___x_2640_, v___x_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue(lean_object* v_e_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v___x_2648_; lean_object* v_a_2649_; lean_object* v___x_2650_; 
v___x_2648_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2642_, v_a_2644_);
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref(v___x_2648_);
v___x_2650_ = l_Lean_Meta_getNatValue_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_3033_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_3033_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2650_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_3033_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
if (lean_obj_tag(v_a_2651_) == 1)
{
lean_object* v_val_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_dec(v_a_2649_);
v_val_2655_ = lean_ctor_get(v_a_2651_, 0);
lean_inc(v_val_2655_);
lean_dec_ref_known(v_a_2651_, 1);
v___x_2656_ = l_Lean_mkNatLit(v_val_2655_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v___x_2656_);
v___x_2658_ = v___x_2653_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
else
{
lean_object* v___x_2660_; 
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_inc(v_a_2649_);
v___x_2660_ = l_Lean_Meta_getIntValue_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_3024_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2663_ = v___x_2660_;
v_isShared_2664_ = v_isSharedCheck_3024_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2660_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_3024_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
if (lean_obj_tag(v_a_2661_) == 1)
{
lean_object* v_val_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
lean_dec(v_a_2649_);
v_val_2665_ = lean_ctor_get(v_a_2661_, 0);
lean_inc(v_val_2665_);
lean_dec_ref_known(v_a_2661_, 1);
v___x_2666_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_2667_ = lean_int_dec_le(v___x_2666_, v_val_2665_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2668_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2669_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__4, &l_Lean_Meta_normLitValue___closed__4_once, _init_l_Lean_Meta_normLitValue___closed__4);
v___x_2670_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__7, &l_Lean_Meta_normLitValue___closed__7_once, _init_l_Lean_Meta_normLitValue___closed__7);
v___x_2671_ = lean_int_neg(v_val_2665_);
lean_dec(v_val_2665_);
v___x_2672_ = l_Int_toNat(v___x_2671_);
lean_dec(v___x_2671_);
v___x_2673_ = l_Lean_instToExprInt_mkNat(v___x_2672_);
v___x_2674_ = l_Lean_mkApp3(v___x_2668_, v___x_2669_, v___x_2670_, v___x_2673_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2674_);
v___x_2676_ = v___x_2663_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2678_ = l_Int_toNat(v_val_2665_);
lean_dec(v_val_2665_);
v___x_2679_ = l_Lean_instToExprInt_mkNat(v___x_2678_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2679_);
v___x_2681_ = v___x_2663_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
else
{
lean_object* v___x_2683_; 
lean_del_object(v___x_2663_);
lean_dec(v_a_2661_);
lean_inc(v_a_2649_);
v___x_2683_ = l_Lean_Meta_getFinValue_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_3015_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_3015_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_3015_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
if (lean_obj_tag(v_a_2684_) == 1)
{
lean_object* v_val_2688_; lean_object* v_fst_2689_; lean_object* v_snd_2690_; lean_object* v_r_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
lean_dec(v_a_2649_);
v_val_2688_ = lean_ctor_get(v_a_2684_, 0);
lean_inc(v_val_2688_);
lean_dec_ref_known(v_a_2684_, 1);
v_fst_2689_ = lean_ctor_get(v_val_2688_, 0);
lean_inc_n(v_fst_2689_, 2);
v_snd_2690_ = lean_ctor_get(v_val_2688_, 1);
lean_inc(v_snd_2690_);
lean_dec(v_val_2688_);
v_r_2691_ = l_Lean_mkRawNatLit(v_snd_2690_);
v___x_2692_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2693_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__9, &l_Lean_Meta_normLitValue___closed__9_once, _init_l_Lean_Meta_normLitValue___closed__9);
v___x_2694_ = l_Lean_mkNatLit(v_fst_2689_);
lean_inc_ref(v___x_2694_);
v___x_2695_ = l_Lean_Expr_app___override(v___x_2693_, v___x_2694_);
v___x_2696_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__12, &l_Lean_Meta_normLitValue___closed__12_once, _init_l_Lean_Meta_normLitValue___closed__12);
v___x_2697_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__15, &l_Lean_Meta_normLitValue___closed__15_once, _init_l_Lean_Meta_normLitValue___closed__15);
v___x_2698_ = lean_unsigned_to_nat(1u);
v___x_2699_ = lean_nat_sub(v_fst_2689_, v___x_2698_);
lean_dec(v_fst_2689_);
v___x_2700_ = l_Lean_mkNatLit(v___x_2699_);
v___x_2701_ = l_Lean_Expr_app___override(v___x_2697_, v___x_2700_);
lean_inc_ref(v_r_2691_);
v___x_2702_ = l_Lean_mkApp3(v___x_2696_, v___x_2694_, v___x_2701_, v_r_2691_);
v___x_2703_ = l_Lean_mkApp3(v___x_2692_, v___x_2695_, v_r_2691_, v___x_2702_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2703_);
v___x_2705_ = v___x_2686_;
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
lean_del_object(v___x_2686_);
lean_dec(v_a_2684_);
lean_inc(v_a_2649_);
v___x_2707_ = l_Lean_Meta_getBitVecValue_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_3006_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_3006_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_3006_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
if (lean_obj_tag(v_a_2708_) == 1)
{
lean_object* v_val_2712_; lean_object* v_fst_2713_; lean_object* v_snd_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
lean_dec(v_a_2649_);
v_val_2712_ = lean_ctor_get(v_a_2708_, 0);
lean_inc(v_val_2712_);
lean_dec_ref_known(v_a_2708_, 1);
v_fst_2713_ = lean_ctor_get(v_val_2712_, 0);
lean_inc(v_fst_2713_);
v_snd_2714_ = lean_ctor_get(v_val_2712_, 1);
lean_inc(v_snd_2714_);
lean_dec(v_val_2712_);
v___x_2715_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__16, &l_Lean_Meta_normLitValue___closed__16_once, _init_l_Lean_Meta_normLitValue___closed__16);
v___x_2716_ = l_Lean_mkNatLit(v_fst_2713_);
v___x_2717_ = l_Lean_mkNatLit(v_snd_2714_);
v___x_2718_ = l_Lean_mkAppB(v___x_2715_, v___x_2716_, v___x_2717_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2718_);
v___x_2720_ = v___x_2710_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
else
{
lean_object* v___x_2722_; 
lean_dec(v_a_2708_);
lean_inc(v_a_2649_);
v___x_2722_ = l_Lean_Meta_getStringValue_x3f(v_a_2649_);
if (lean_obj_tag(v___x_2722_) == 1)
{
lean_object* v_val_2723_; lean_object* v___x_2724_; lean_object* v___x_2726_; 
lean_dec(v_a_2649_);
v_val_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_val_2723_);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2724_ = l_Lean_mkStrLit(v_val_2723_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2724_);
v___x_2726_ = v___x_2710_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
else
{
lean_object* v___x_2728_; 
lean_dec(v___x_2722_);
lean_del_object(v___x_2710_);
lean_inc(v_a_2649_);
v___x_2728_ = l_Lean_Meta_getCharValue_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2997_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2731_ = v___x_2728_;
v_isShared_2732_ = v_isSharedCheck_2997_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2728_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2997_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
if (lean_obj_tag(v_a_2729_) == 1)
{
lean_object* v_val_2733_; lean_object* v___x_2734_; uint32_t v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_dec(v_a_2649_);
v_val_2733_ = lean_ctor_get(v_a_2729_, 0);
lean_inc(v_val_2733_);
lean_dec_ref_known(v_a_2729_, 1);
v___x_2734_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__17, &l_Lean_Meta_normLitValue___closed__17_once, _init_l_Lean_Meta_normLitValue___closed__17);
v___x_2735_ = lean_unbox_uint32(v_val_2733_);
lean_dec(v_val_2733_);
v___x_2736_ = lean_uint32_to_nat(v___x_2735_);
v___x_2737_ = l_Lean_mkRawNatLit(v___x_2736_);
v___x_2738_ = l_Lean_Expr_app___override(v___x_2734_, v___x_2737_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v___x_2738_);
v___x_2740_ = v___x_2731_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
else
{
lean_object* v___x_2742_; 
lean_del_object(v___x_2731_);
lean_dec(v_a_2729_);
lean_inc(v_a_2649_);
v___x_2742_ = l_Lean_Meta_getUInt8Value_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2988_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2988_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2988_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
if (lean_obj_tag(v_a_2743_) == 1)
{
lean_object* v_val_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v_r_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
lean_dec(v_a_2649_);
v_val_2747_ = lean_ctor_get(v_a_2743_, 0);
lean_inc(v_val_2747_);
lean_dec_ref_known(v_a_2743_, 1);
v___x_2748_ = lean_unbox(v_val_2747_);
lean_dec(v_val_2747_);
v___x_2749_ = lean_uint8_to_nat(v___x_2748_);
v_r_2750_ = l_Lean_mkRawNatLit(v___x_2749_);
v___x_2751_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2752_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__18, &l_Lean_Meta_normLitValue___closed__18_once, _init_l_Lean_Meta_normLitValue___closed__18);
v___x_2753_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__20, &l_Lean_Meta_normLitValue___closed__20_once, _init_l_Lean_Meta_normLitValue___closed__20);
lean_inc_ref(v_r_2750_);
v___x_2754_ = l_Lean_Expr_app___override(v___x_2753_, v_r_2750_);
v___x_2755_ = l_Lean_mkApp3(v___x_2751_, v___x_2752_, v_r_2750_, v___x_2754_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2755_);
v___x_2757_ = v___x_2745_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
else
{
lean_object* v___x_2759_; 
lean_del_object(v___x_2745_);
lean_dec(v_a_2743_);
lean_inc(v_a_2649_);
v___x_2759_ = l_Lean_Meta_getUInt16Value_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2979_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2979_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2979_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
if (lean_obj_tag(v_a_2760_) == 1)
{
lean_object* v_val_2764_; uint16_t v___x_2765_; lean_object* v___x_2766_; lean_object* v_r_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec(v_a_2649_);
v_val_2764_ = lean_ctor_get(v_a_2760_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v_a_2760_, 1);
v___x_2765_ = lean_unbox(v_val_2764_);
lean_dec(v_val_2764_);
v___x_2766_ = lean_uint16_to_nat(v___x_2765_);
v_r_2767_ = l_Lean_mkRawNatLit(v___x_2766_);
v___x_2768_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2769_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__21, &l_Lean_Meta_normLitValue___closed__21_once, _init_l_Lean_Meta_normLitValue___closed__21);
v___x_2770_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__23, &l_Lean_Meta_normLitValue___closed__23_once, _init_l_Lean_Meta_normLitValue___closed__23);
lean_inc_ref(v_r_2767_);
v___x_2771_ = l_Lean_Expr_app___override(v___x_2770_, v_r_2767_);
v___x_2772_ = l_Lean_mkApp3(v___x_2768_, v___x_2769_, v_r_2767_, v___x_2771_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2772_);
v___x_2774_ = v___x_2762_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
else
{
lean_object* v___x_2776_; 
lean_del_object(v___x_2762_);
lean_dec(v_a_2760_);
lean_inc(v_a_2649_);
v___x_2776_ = l_Lean_Meta_getUInt32Value_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2970_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2970_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2970_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
if (lean_obj_tag(v_a_2777_) == 1)
{
lean_object* v_val_2781_; uint32_t v___x_2782_; lean_object* v___x_2783_; lean_object* v_r_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
lean_dec(v_a_2649_);
v_val_2781_ = lean_ctor_get(v_a_2777_, 0);
lean_inc(v_val_2781_);
lean_dec_ref_known(v_a_2777_, 1);
v___x_2782_ = lean_unbox_uint32(v_val_2781_);
lean_dec(v_val_2781_);
v___x_2783_ = lean_uint32_to_nat(v___x_2782_);
v_r_2784_ = l_Lean_mkRawNatLit(v___x_2783_);
v___x_2785_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2786_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__24, &l_Lean_Meta_normLitValue___closed__24_once, _init_l_Lean_Meta_normLitValue___closed__24);
v___x_2787_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__26, &l_Lean_Meta_normLitValue___closed__26_once, _init_l_Lean_Meta_normLitValue___closed__26);
lean_inc_ref(v_r_2784_);
v___x_2788_ = l_Lean_Expr_app___override(v___x_2787_, v_r_2784_);
v___x_2789_ = l_Lean_mkApp3(v___x_2785_, v___x_2786_, v_r_2784_, v___x_2788_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2789_);
v___x_2791_ = v___x_2779_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
else
{
lean_object* v___x_2793_; 
lean_del_object(v___x_2779_);
lean_dec(v_a_2777_);
lean_inc(v_a_2649_);
v___x_2793_ = l_Lean_Meta_getUInt64Value_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2961_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2961_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2961_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
if (lean_obj_tag(v_a_2794_) == 1)
{
lean_object* v_val_2798_; uint64_t v___x_2799_; lean_object* v___x_2800_; lean_object* v_r_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
lean_dec(v_a_2649_);
v_val_2798_ = lean_ctor_get(v_a_2794_, 0);
lean_inc(v_val_2798_);
lean_dec_ref_known(v_a_2794_, 1);
v___x_2799_ = lean_unbox_uint64(v_val_2798_);
lean_dec(v_val_2798_);
v___x_2800_ = lean_uint64_to_nat(v___x_2799_);
v_r_2801_ = l_Lean_mkRawNatLit(v___x_2800_);
v___x_2802_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2803_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__27, &l_Lean_Meta_normLitValue___closed__27_once, _init_l_Lean_Meta_normLitValue___closed__27);
v___x_2804_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__29, &l_Lean_Meta_normLitValue___closed__29_once, _init_l_Lean_Meta_normLitValue___closed__29);
lean_inc_ref(v_r_2801_);
v___x_2805_ = l_Lean_Expr_app___override(v___x_2804_, v_r_2801_);
v___x_2806_ = l_Lean_mkApp3(v___x_2802_, v___x_2803_, v_r_2801_, v___x_2805_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2806_);
v___x_2808_ = v___x_2796_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
else
{
lean_object* v___x_2810_; 
lean_del_object(v___x_2796_);
lean_dec(v_a_2794_);
lean_inc(v_a_2649_);
v___x_2810_ = l_Lean_Meta_getInt8Value_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2952_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2952_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2952_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
if (lean_obj_tag(v_a_2811_) == 1)
{
lean_object* v_val_2815_; uint8_t v___x_2816_; uint8_t v___x_2817_; uint8_t v___x_2818_; 
lean_dec(v_a_2649_);
v_val_2815_ = lean_ctor_get(v_a_2811_, 0);
lean_inc(v_val_2815_);
lean_dec_ref_known(v_a_2811_, 1);
v___x_2816_ = lean_uint8_once(&l_Lean_Meta_normLitValue___closed__30, &l_Lean_Meta_normLitValue___closed__30_once, _init_l_Lean_Meta_normLitValue___closed__30);
v___x_2817_ = lean_unbox(v_val_2815_);
v___x_2818_ = lean_int8_dec_le(v___x_2816_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2829_; 
v___x_2819_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2820_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__31, &l_Lean_Meta_normLitValue___closed__31_once, _init_l_Lean_Meta_normLitValue___closed__31);
v___x_2821_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__34, &l_Lean_Meta_normLitValue___closed__34_once, _init_l_Lean_Meta_normLitValue___closed__34);
v___x_2822_ = lean_unbox(v_val_2815_);
lean_dec(v_val_2815_);
v___x_2823_ = lean_int8_to_int(v___x_2822_);
v___x_2824_ = lean_int_neg(v___x_2823_);
v___x_2825_ = l_Int_toNat(v___x_2824_);
lean_dec(v___x_2824_);
v___x_2826_ = l_Lean_instToExprInt8_mkNat(v___x_2825_);
v___x_2827_ = l_Lean_mkApp3(v___x_2819_, v___x_2820_, v___x_2821_, v___x_2826_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2827_);
v___x_2829_ = v___x_2813_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
else
{
uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2831_ = lean_unbox(v_val_2815_);
lean_dec(v_val_2815_);
v___x_2832_ = lean_int8_to_int(v___x_2831_);
v___x_2833_ = l_Int_toNat(v___x_2832_);
v___x_2834_ = l_Lean_instToExprInt8_mkNat(v___x_2833_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2834_);
v___x_2836_ = v___x_2813_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
else
{
lean_object* v___x_2838_; 
lean_del_object(v___x_2813_);
lean_dec(v_a_2811_);
lean_inc(v_a_2649_);
v___x_2838_ = l_Lean_Meta_getInt16Value_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2943_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2943_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2943_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
if (lean_obj_tag(v_a_2839_) == 1)
{
lean_object* v_val_2843_; uint16_t v___x_2844_; uint16_t v___x_2845_; uint8_t v___x_2846_; 
lean_dec(v_a_2649_);
v_val_2843_ = lean_ctor_get(v_a_2839_, 0);
lean_inc(v_val_2843_);
lean_dec_ref_known(v_a_2839_, 1);
v___x_2844_ = lean_uint16_once(&l_Lean_Meta_normLitValue___closed__35, &l_Lean_Meta_normLitValue___closed__35_once, _init_l_Lean_Meta_normLitValue___closed__35);
v___x_2845_ = lean_unbox(v_val_2843_);
v___x_2846_ = lean_int16_dec_le(v___x_2844_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint16_t v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2847_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2848_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__36, &l_Lean_Meta_normLitValue___closed__36_once, _init_l_Lean_Meta_normLitValue___closed__36);
v___x_2849_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__38, &l_Lean_Meta_normLitValue___closed__38_once, _init_l_Lean_Meta_normLitValue___closed__38);
v___x_2850_ = lean_unbox(v_val_2843_);
lean_dec(v_val_2843_);
v___x_2851_ = lean_int16_to_int(v___x_2850_);
v___x_2852_ = lean_int_neg(v___x_2851_);
v___x_2853_ = l_Int_toNat(v___x_2852_);
lean_dec(v___x_2852_);
v___x_2854_ = l_Lean_instToExprInt16_mkNat(v___x_2853_);
v___x_2855_ = l_Lean_mkApp3(v___x_2847_, v___x_2848_, v___x_2849_, v___x_2854_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2855_);
v___x_2857_ = v___x_2841_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
else
{
uint16_t v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2859_ = lean_unbox(v_val_2843_);
lean_dec(v_val_2843_);
v___x_2860_ = lean_int16_to_int(v___x_2859_);
v___x_2861_ = l_Int_toNat(v___x_2860_);
v___x_2862_ = l_Lean_instToExprInt16_mkNat(v___x_2861_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2862_);
v___x_2864_ = v___x_2841_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
else
{
lean_object* v___x_2866_; 
lean_del_object(v___x_2841_);
lean_dec(v_a_2839_);
lean_inc(v_a_2649_);
v___x_2866_ = l_Lean_Meta_getInt32Value_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2934_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2934_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2934_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
if (lean_obj_tag(v_a_2867_) == 1)
{
lean_object* v_val_2871_; uint32_t v___x_2872_; uint32_t v___x_2873_; uint8_t v___x_2874_; 
lean_dec(v_a_2649_);
v_val_2871_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_val_2871_);
lean_dec_ref_known(v_a_2867_, 1);
v___x_2872_ = lean_uint32_once(&l_Lean_Meta_normLitValue___closed__39, &l_Lean_Meta_normLitValue___closed__39_once, _init_l_Lean_Meta_normLitValue___closed__39);
v___x_2873_ = lean_unbox_uint32(v_val_2871_);
v___x_2874_ = lean_int32_dec_le(v___x_2872_, v___x_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; uint32_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2875_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2876_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__40, &l_Lean_Meta_normLitValue___closed__40_once, _init_l_Lean_Meta_normLitValue___closed__40);
v___x_2877_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__42, &l_Lean_Meta_normLitValue___closed__42_once, _init_l_Lean_Meta_normLitValue___closed__42);
v___x_2878_ = lean_unbox_uint32(v_val_2871_);
lean_dec(v_val_2871_);
v___x_2879_ = lean_int32_to_int(v___x_2878_);
v___x_2880_ = lean_int_neg(v___x_2879_);
lean_dec(v___x_2879_);
v___x_2881_ = l_Int_toNat(v___x_2880_);
lean_dec(v___x_2880_);
v___x_2882_ = l_Lean_instToExprInt32_mkNat(v___x_2881_);
v___x_2883_ = l_Lean_mkApp3(v___x_2875_, v___x_2876_, v___x_2877_, v___x_2882_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2883_);
v___x_2885_ = v___x_2869_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
else
{
uint32_t v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2887_ = lean_unbox_uint32(v_val_2871_);
lean_dec(v_val_2871_);
v___x_2888_ = lean_int32_to_int(v___x_2887_);
v___x_2889_ = l_Int_toNat(v___x_2888_);
lean_dec(v___x_2888_);
v___x_2890_ = l_Lean_instToExprInt32_mkNat(v___x_2889_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2890_);
v___x_2892_ = v___x_2869_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
else
{
lean_object* v___x_2894_; 
lean_del_object(v___x_2869_);
lean_dec(v_a_2867_);
lean_inc(v_a_2649_);
v___x_2894_ = l_Lean_Meta_getInt64Value_x3f(v_a_2649_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2925_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2925_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2894_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2925_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
if (lean_obj_tag(v_a_2895_) == 1)
{
lean_object* v_val_2899_; uint64_t v___x_2900_; uint64_t v___x_2901_; uint8_t v___x_2902_; 
lean_dec(v_a_2649_);
v_val_2899_ = lean_ctor_get(v_a_2895_, 0);
lean_inc(v_val_2899_);
lean_dec_ref_known(v_a_2895_, 1);
v___x_2900_ = lean_uint64_once(&l_Lean_Meta_normLitValue___closed__43, &l_Lean_Meta_normLitValue___closed__43_once, _init_l_Lean_Meta_normLitValue___closed__43);
v___x_2901_ = lean_unbox_uint64(v_val_2899_);
v___x_2902_ = lean_int64_dec_le(v___x_2900_, v___x_2901_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint64_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2903_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2904_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__44, &l_Lean_Meta_normLitValue___closed__44_once, _init_l_Lean_Meta_normLitValue___closed__44);
v___x_2905_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__46, &l_Lean_Meta_normLitValue___closed__46_once, _init_l_Lean_Meta_normLitValue___closed__46);
v___x_2906_ = lean_unbox_uint64(v_val_2899_);
lean_dec(v_val_2899_);
v___x_2907_ = lean_int64_to_int_sint(v___x_2906_);
v___x_2908_ = lean_int_neg(v___x_2907_);
lean_dec(v___x_2907_);
v___x_2909_ = l_Int_toNat(v___x_2908_);
lean_dec(v___x_2908_);
v___x_2910_ = l_Lean_instToExprInt64_mkNat(v___x_2909_);
v___x_2911_ = l_Lean_mkApp3(v___x_2903_, v___x_2904_, v___x_2905_, v___x_2910_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2911_);
v___x_2913_ = v___x_2897_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
else
{
uint64_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2915_ = lean_unbox_uint64(v_val_2899_);
lean_dec(v_val_2899_);
v___x_2916_ = lean_int64_to_int_sint(v___x_2915_);
v___x_2917_ = l_Int_toNat(v___x_2916_);
lean_dec(v___x_2916_);
v___x_2918_ = l_Lean_instToExprInt64_mkNat(v___x_2917_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2918_);
v___x_2920_ = v___x_2897_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
else
{
lean_object* v___x_2923_; 
lean_dec(v_a_2895_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v_a_2649_);
v___x_2923_ = v___x_2897_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2649_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_a_2649_);
v_a_2926_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2894_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2894_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec(v_a_2649_);
v_a_2935_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2866_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2866_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_dec(v_a_2649_);
v_a_2944_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2838_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2838_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec(v_a_2649_);
v_a_2953_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2810_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2810_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec(v_a_2649_);
v_a_2962_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2793_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2793_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v_a_2649_);
v_a_2971_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2776_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2776_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec(v_a_2649_);
v_a_2980_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2759_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2759_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec(v_a_2649_);
v_a_2989_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2742_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2742_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec(v_a_2649_);
v_a_2998_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2728_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2728_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec(v_a_2649_);
v_a_3007_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2707_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2707_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec(v_a_2649_);
v_a_3016_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2683_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2683_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec(v_a_2649_);
v_a_3025_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2660_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2660_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_a_2649_);
v_a_3034_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_2650_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_2650_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue___boxed(lean_object* v_e_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_Meta_normLitValue(v_e_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(lean_object* v_m_3055_, lean_object* v_s_3056_, lean_object* v_exp_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_s_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v_s_3068_ = l_Lean_Expr_consumeMData(v_s_3056_);
v___x_3069_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__0));
v___x_3070_ = l_Lean_Expr_isConstOf(v_s_3068_, v___x_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; uint8_t v___x_3072_; 
v___x_3071_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__1));
v___x_3072_ = l_Lean_Expr_isConstOf(v_s_3068_, v___x_3071_);
lean_dec_ref(v_s_3068_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_box(v___x_3072_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
return v___x_3074_;
}
else
{
goto v___jp_3063_;
}
}
else
{
lean_dec_ref(v_s_3068_);
goto v___jp_3063_;
}
v___jp_3063_:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Lean_Meta_isNatValue(v_m_3055_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; uint8_t v___x_3066_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
v___x_3066_ = lean_unbox(v_a_3065_);
if (v___x_3066_ == 0)
{
return v___x_3064_;
}
else
{
lean_object* v___x_3067_; 
lean_dec_ref_known(v___x_3064_, 1);
v___x_3067_ = l_Lean_Meta_isNatValue(v_exp_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3067_;
}
}
else
{
return v___x_3064_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___boxed(lean_object* v_m_3075_, lean_object* v_s_3076_, lean_object* v_exp_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_3075_, v_s_3076_, v_exp_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec_ref(v_exp_3077_);
lean_dec_ref(v_s_3076_);
lean_dec_ref(v_m_3075_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(lean_object* v_type_3084_, lean_object* v_m_3085_, lean_object* v_s_3086_, lean_object* v_exp_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lean_Meta_whnfD(v_type_3084_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3111_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3111_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3111_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3098_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_3099_ = l_Lean_Expr_isConstOf(v_a_3094_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; uint8_t v___x_3101_; 
v___x_3100_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_3101_ = l_Lean_Expr_isConstOf(v_a_3094_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3102_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_3103_ = l_Lean_Expr_isConstOf(v_a_3094_, v___x_3102_);
lean_dec(v_a_3094_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3104_ = lean_box(v___x_3103_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3104_);
v___x_3106_ = v___x_3096_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
else
{
lean_object* v___x_3108_; 
lean_del_object(v___x_3096_);
v___x_3108_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_3085_, v_s_3086_, v_exp_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
return v___x_3108_;
}
}
else
{
lean_object* v___x_3109_; 
lean_del_object(v___x_3096_);
lean_dec(v_a_3094_);
v___x_3109_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_3085_, v_s_3086_, v_exp_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
return v___x_3109_;
}
}
else
{
lean_object* v___x_3110_; 
lean_del_object(v___x_3096_);
lean_dec(v_a_3094_);
v___x_3110_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_3085_, v_s_3086_, v_exp_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
return v___x_3110_;
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
v_a_3112_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3093_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3093_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue___boxed(lean_object* v_type_3120_, lean_object* v_m_3121_, lean_object* v_s_3122_, lean_object* v_exp_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(v_type_3120_, v_m_3121_, v_s_3122_, v_exp_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec_ref(v_exp_3123_);
lean_dec_ref(v_s_3122_);
lean_dec_ref(v_m_3121_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue(lean_object* v_type_3130_, lean_object* v_n_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3137_ = l_Lean_Expr_consumeMData(v_n_3131_);
v___x_3138_ = l_Lean_Expr_isRawNatLit(v___x_3137_);
lean_dec_ref(v___x_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_dec_ref(v_type_3130_);
v___x_3139_ = lean_box(v___x_3138_);
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
return v___x_3140_;
}
else
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Lean_Meta_whnfD(v_type_3130_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3263_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3263_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3263_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_Expr_getAppFn(v_a_3142_);
if (lean_obj_tag(v___x_3146_) == 4)
{
lean_object* v_declName_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_declName_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_declName_3147_);
lean_dec_ref_known(v___x_3146_, 2);
v___x_3148_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_3149_ = lean_name_eq(v_declName_3147_, v___x_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3150_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_3151_ = lean_name_eq(v_declName_3147_, v___x_3150_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3152_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_3153_ = lean_name_eq(v_declName_3147_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; uint8_t v___x_3155_; 
v___x_3154_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_3155_ = lean_name_eq(v_declName_3147_, v___x_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3156_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_3157_ = lean_name_eq(v_declName_3147_, v___x_3156_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3158_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_3159_ = lean_name_eq(v_declName_3147_, v___x_3158_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_3161_ = lean_name_eq(v_declName_3147_, v___x_3160_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_3163_ = lean_name_eq(v_declName_3147_, v___x_3162_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3164_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_3165_ = lean_name_eq(v_declName_3147_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_3167_ = lean_name_eq(v_declName_3147_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3168_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_3169_ = lean_name_eq(v_declName_3147_, v___x_3168_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___x_3170_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_3171_ = lean_name_eq(v_declName_3147_, v___x_3170_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; uint8_t v___x_3173_; 
v___x_3172_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_3173_ = lean_name_eq(v_declName_3147_, v___x_3172_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; uint8_t v___x_3175_; 
v___x_3174_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_3175_ = lean_name_eq(v_declName_3147_, v___x_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3176_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_3177_ = lean_name_eq(v_declName_3147_, v___x_3176_);
lean_dec(v_declName_3147_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3180_; 
lean_dec(v_a_3142_);
v___x_3178_ = lean_box(v___x_3177_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3178_);
v___x_3180_ = v___x_3144_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_del_object(v___x_3144_);
v___x_3182_ = l_Lean_Expr_appArg_x21(v_a_3142_);
lean_dec(v_a_3142_);
v___x_3183_ = l_Lean_Meta_whnfD(v___x_3182_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3185_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3183_, 1);
v___x_3185_ = l_Lean_Meta_isNatValue(v_a_3184_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
lean_dec(v_a_3184_);
return v___x_3185_;
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
v_a_3186_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3183_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3183_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_dec(v_declName_3147_);
lean_del_object(v___x_3144_);
v___x_3194_ = l_Lean_Expr_appArg_x21(v_a_3142_);
lean_dec(v_a_3142_);
v___x_3195_ = l_Lean_Meta_whnfD(v___x_3194_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3197_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v___x_3197_ = l_Lean_Meta_isNonZeroNatValue(v_a_3196_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
lean_dec(v_a_3196_);
return v___x_3197_;
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
v_a_3198_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3195_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3195_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
else
{
lean_object* v___x_3206_; lean_object* v___x_3208_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3206_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3206_);
v___x_3208_ = v___x_3144_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3206_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3210_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3210_);
v___x_3212_ = v___x_3144_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3216_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3214_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3214_);
v___x_3216_ = v___x_3144_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3218_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3218_);
v___x_3220_ = v___x_3144_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3222_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3222_);
v___x_3224_ = v___x_3144_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3228_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3226_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3226_);
v___x_3228_ = v___x_3144_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3230_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3230_);
v___x_3232_ = v___x_3144_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3234_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3234_);
v___x_3236_ = v___x_3144_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3240_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3238_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3238_);
v___x_3240_ = v___x_3144_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
else
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3242_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3242_);
v___x_3244_ = v___x_3144_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
else
{
lean_object* v___x_3246_; lean_object* v___x_3248_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3246_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3246_);
v___x_3248_ = v___x_3144_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3252_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3250_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3250_);
v___x_3252_ = v___x_3144_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3250_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
else
{
lean_object* v___x_3254_; lean_object* v___x_3256_; 
lean_dec(v_declName_3147_);
lean_dec(v_a_3142_);
v___x_3254_ = lean_box(v___x_3138_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3254_);
v___x_3256_ = v___x_3144_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3254_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
else
{
uint8_t v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
lean_dec_ref(v___x_3146_);
lean_dec(v_a_3142_);
v___x_3258_ = 0;
v___x_3259_ = lean_box(v___x_3258_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3259_);
v___x_3261_ = v___x_3144_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
v_a_3264_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3141_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3141_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue___boxed(lean_object* v_type_3272_, lean_object* v_n_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue(v_type_3272_, v_n_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec_ref(v_n_3273_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue(lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_3280_, v_a_3282_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3390_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3293_ = v___x_3290_;
v_isShared_3294_ = v_isSharedCheck_3390_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3290_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3390_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3295_ = l_Lean_Expr_cleanupAnnotations(v_a_3291_);
lean_dec(v_a_3291_);
v___x_3296_ = l_Lean_Expr_isApp(v___x_3295_);
if (v___x_3296_ == 0)
{
lean_dec_ref(v___x_3295_);
lean_del_object(v___x_3293_);
goto v___jp_3286_;
}
else
{
lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3295_);
v___x_3298_ = l_Lean_Expr_isApp(v___x_3297_);
if (v___x_3298_ == 0)
{
lean_dec_ref(v___x_3297_);
lean_dec_ref(v___x_3295_);
lean_del_object(v___x_3293_);
goto v___jp_3286_;
}
else
{
lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3297_);
v___x_3300_ = l_Lean_Expr_isApp(v___x_3299_);
if (v___x_3300_ == 0)
{
lean_dec_ref(v___x_3299_);
lean_dec_ref(v___x_3297_);
lean_dec_ref(v___x_3295_);
lean_del_object(v___x_3293_);
goto v___jp_3286_;
}
else
{
lean_object* v_arg_3301_; lean_object* v_arg_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v_arg_3301_ = lean_ctor_get(v___x_3297_, 1);
lean_inc_ref(v_arg_3301_);
lean_dec_ref(v___x_3297_);
v_arg_3302_ = lean_ctor_get(v___x_3299_, 1);
lean_inc_ref(v_arg_3302_);
v___x_3303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3299_);
lean_dec_ref(v___x_3299_);
v___x_3304_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_3305_ = l_Lean_Expr_isConstOf(v___x_3303_, v___x_3304_);
if (v___x_3305_ == 0)
{
uint8_t v___x_3306_; 
lean_del_object(v___x_3293_);
v___x_3306_ = l_Lean_Expr_isApp(v___x_3303_);
if (v___x_3306_ == 0)
{
lean_dec_ref(v___x_3303_);
lean_dec_ref(v_arg_3302_);
lean_dec_ref(v_arg_3301_);
lean_dec_ref(v___x_3295_);
goto v___jp_3286_;
}
else
{
lean_object* v___x_3307_; uint8_t v___x_3308_; 
v___x_3307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3303_);
lean_dec_ref(v___x_3303_);
v___x_3308_ = l_Lean_Expr_isApp(v___x_3307_);
if (v___x_3308_ == 0)
{
lean_dec_ref(v___x_3307_);
lean_dec_ref(v_arg_3302_);
lean_dec_ref(v_arg_3301_);
lean_dec_ref(v___x_3295_);
goto v___jp_3286_;
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3309_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3307_);
v___x_3310_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_3311_ = l_Lean_Expr_isConstOf(v___x_3309_, v___x_3310_);
lean_dec_ref(v___x_3309_);
if (v___x_3311_ == 0)
{
lean_dec_ref(v___x_3307_);
lean_dec_ref(v_arg_3302_);
lean_dec_ref(v_arg_3301_);
lean_dec_ref(v___x_3295_);
goto v___jp_3286_;
}
else
{
lean_object* v_arg_3312_; lean_object* v_arg_3313_; lean_object* v___x_3314_; 
v_arg_3312_ = lean_ctor_get(v___x_3295_, 1);
lean_inc_ref(v_arg_3312_);
lean_dec_ref(v___x_3295_);
v_arg_3313_ = lean_ctor_get(v___x_3307_, 1);
lean_inc_ref(v_arg_3313_);
lean_dec_ref(v___x_3307_);
v___x_3314_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(v_arg_3313_, v_arg_3302_, v_arg_3301_, v_arg_3312_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
lean_dec_ref(v_arg_3312_);
lean_dec_ref(v_arg_3301_);
lean_dec_ref(v_arg_3302_);
return v___x_3314_;
}
}
}
}
else
{
lean_object* v___x_3315_; uint8_t v___x_3316_; 
lean_dec_ref(v___x_3303_);
lean_dec_ref(v___x_3295_);
v___x_3315_ = l_Lean_Expr_consumeMData(v_arg_3301_);
lean_dec_ref(v_arg_3301_);
v___x_3316_ = l_Lean_Expr_isRawNatLit(v___x_3315_);
lean_dec_ref(v___x_3315_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3319_; 
lean_dec_ref(v_arg_3302_);
v___x_3317_ = lean_box(v___x_3316_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v___x_3317_);
v___x_3319_ = v___x_3293_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
else
{
lean_object* v___x_3321_; 
lean_del_object(v___x_3293_);
v___x_3321_ = l_Lean_Meta_whnfD(v_arg_3302_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3381_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3381_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3381_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_Expr_getAppFn(v_a_3322_);
lean_dec(v_a_3322_);
if (lean_obj_tag(v___x_3326_) == 4)
{
lean_object* v_declName_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; 
v_declName_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_declName_3327_);
lean_dec_ref_known(v___x_3326_, 2);
v___x_3328_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_3329_ = lean_name_eq(v_declName_3327_, v___x_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3330_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_3331_ = lean_name_eq(v_declName_3327_, v___x_3330_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___x_3332_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_3333_ = lean_name_eq(v_declName_3327_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; uint8_t v___x_3335_; 
v___x_3334_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_3335_ = lean_name_eq(v_declName_3327_, v___x_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3336_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_3337_ = lean_name_eq(v_declName_3327_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; uint8_t v___x_3339_; 
v___x_3338_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_3339_ = lean_name_eq(v_declName_3327_, v___x_3338_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3340_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_3341_ = lean_name_eq(v_declName_3327_, v___x_3340_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; uint8_t v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3342_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_3343_ = lean_name_eq(v_declName_3327_, v___x_3342_);
lean_dec(v_declName_3327_);
v___x_3344_ = lean_box(v___x_3343_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3344_);
v___x_3346_ = v___x_3324_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3350_; 
lean_dec(v_declName_3327_);
v___x_3348_ = lean_box(v___x_3305_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3348_);
v___x_3350_ = v___x_3324_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3348_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3354_; 
lean_dec(v_declName_3327_);
v___x_3352_ = lean_box(v___x_3305_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3352_);
v___x_3354_ = v___x_3324_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
else
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
lean_dec(v_declName_3327_);
v___x_3356_ = lean_box(v___x_3305_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3356_);
v___x_3358_ = v___x_3324_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
else
{
lean_object* v___x_3360_; lean_object* v___x_3362_; 
lean_dec(v_declName_3327_);
v___x_3360_ = lean_box(v___x_3305_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3360_);
v___x_3362_ = v___x_3324_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3366_; 
lean_dec(v_declName_3327_);
v___x_3364_ = lean_box(v___x_3305_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3364_);
v___x_3366_ = v___x_3324_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
lean_dec(v_declName_3327_);
v___x_3368_ = lean_box(v___x_3305_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3368_);
v___x_3370_ = v___x_3324_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
else
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
lean_dec(v_declName_3327_);
v___x_3372_ = lean_box(v___x_3305_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3372_);
v___x_3374_ = v___x_3324_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3372_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
else
{
uint8_t v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
lean_dec_ref(v___x_3326_);
v___x_3376_ = 0;
v___x_3377_ = lean_box(v___x_3376_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3377_);
v___x_3379_ = v___x_3324_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
v_a_3382_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3321_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3321_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
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
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
v_a_3391_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3290_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3290_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
v___jp_3286_:
{
uint8_t v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3287_ = 0;
v___x_3288_ = lean_box(v___x_3287_);
v___x_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
return v___x_3289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue___boxed(lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue(v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(lean_object* v_e_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v___x_3416_; uint8_t v___x_3417_; 
v___x_3416_ = l_Lean_Expr_cleanupAnnotations(v_e_3406_);
v___x_3417_ = l_Lean_Expr_isApp(v___x_3416_);
if (v___x_3417_ == 0)
{
lean_dec_ref(v___x_3416_);
goto v___jp_3412_;
}
else
{
lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3416_);
lean_dec_ref(v___x_3416_);
v___x_3419_ = l_Lean_Expr_isApp(v___x_3418_);
if (v___x_3419_ == 0)
{
lean_dec_ref(v___x_3418_);
goto v___jp_3412_;
}
else
{
lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3420_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3418_);
v___x_3421_ = l_Lean_Expr_isApp(v___x_3420_);
if (v___x_3421_ == 0)
{
lean_dec_ref(v___x_3420_);
lean_dec_ref(v___x_3418_);
goto v___jp_3412_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3422_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3420_);
v___x_3423_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_3424_ = l_Lean_Expr_isConstOf(v___x_3422_, v___x_3423_);
lean_dec_ref(v___x_3422_);
if (v___x_3424_ == 0)
{
lean_dec_ref(v___x_3420_);
lean_dec_ref(v___x_3418_);
goto v___jp_3412_;
}
else
{
lean_object* v_arg_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v_arg_3425_ = lean_ctor_get(v___x_3418_, 1);
lean_inc_ref(v_arg_3425_);
lean_dec_ref(v___x_3418_);
v___x_3426_ = l_Lean_Expr_consumeMData(v_arg_3425_);
lean_dec_ref(v_arg_3425_);
v___x_3427_ = l_Lean_Expr_isRawNatLit(v___x_3426_);
lean_dec_ref(v___x_3426_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_dec_ref(v___x_3420_);
v___x_3428_ = lean_box(v___x_3427_);
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
else
{
lean_object* v_arg_3430_; lean_object* v___x_3431_; 
v_arg_3430_ = lean_ctor_get(v___x_3420_, 1);
lean_inc_ref(v_arg_3430_);
lean_dec_ref(v___x_3420_);
v___x_3431_ = l_Lean_Meta_whnfD(v_arg_3430_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3443_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3443_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3443_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; uint8_t v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3441_; 
v___x_3436_ = l_Lean_Expr_getAppFn(v_a_3432_);
lean_dec(v_a_3432_);
v___x_3437_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_3438_ = l_Lean_Expr_isConstOf(v___x_3436_, v___x_3437_);
lean_dec_ref(v___x_3436_);
v___x_3439_ = lean_box(v___x_3438_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v___x_3439_);
v___x_3441_ = v___x_3434_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
v_a_3444_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3431_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3431_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
}
}
}
v___jp_3412_:
{
uint8_t v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = 0;
v___x_3414_ = lean_box(v___x_3413_);
v___x_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
return v___x_3415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat___boxed(lean_object* v_e_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(v_e_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec_ref(v_e_3452_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue(lean_object* v_a_3459_, lean_object* v_b_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v___y_3467_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3472_ = l_Lean_Expr_cleanupAnnotations(v_a_3459_);
v___x_3473_ = l_Lean_Expr_isApp(v___x_3472_);
if (v___x_3473_ == 0)
{
lean_dec_ref(v___x_3472_);
v___y_3467_ = v_a_3459_;
goto v___jp_3466_;
}
else
{
lean_object* v___x_3474_; uint8_t v___x_3475_; 
v___x_3474_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3472_);
v___x_3475_ = l_Lean_Expr_isApp(v___x_3474_);
if (v___x_3475_ == 0)
{
lean_dec_ref(v___x_3474_);
lean_dec_ref(v___x_3472_);
v___y_3467_ = v_a_3459_;
goto v___jp_3466_;
}
else
{
lean_object* v___x_3476_; uint8_t v___x_3477_; 
v___x_3476_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3474_);
lean_dec_ref(v___x_3474_);
v___x_3477_ = l_Lean_Expr_isApp(v___x_3476_);
if (v___x_3477_ == 0)
{
lean_dec_ref(v___x_3476_);
lean_dec_ref(v___x_3472_);
v___y_3467_ = v_a_3459_;
goto v___jp_3466_;
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v___x_3478_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3476_);
lean_dec_ref(v___x_3476_);
v___x_3479_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_3480_ = l_Lean_Expr_isConstOf(v___x_3478_, v___x_3479_);
lean_dec_ref(v___x_3478_);
if (v___x_3480_ == 0)
{
lean_dec_ref(v___x_3472_);
v___y_3467_ = v_a_3459_;
goto v___jp_3466_;
}
else
{
lean_object* v_arg_3481_; 
lean_dec_ref(v_a_3459_);
v_arg_3481_ = lean_ctor_get(v___x_3472_, 1);
lean_inc_ref(v_arg_3481_);
lean_dec_ref(v___x_3472_);
v___y_3467_ = v_arg_3481_;
goto v___jp_3466_;
}
}
}
}
v___jp_3466_:
{
lean_object* v___x_3468_; 
v___x_3468_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(v___y_3467_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_);
lean_dec_ref(v___y_3467_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; uint8_t v___x_3470_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v___x_3470_ = lean_unbox(v_a_3469_);
if (v___x_3470_ == 0)
{
return v___x_3468_;
}
else
{
lean_object* v___x_3471_; 
lean_dec_ref_known(v___x_3468_, 1);
v___x_3471_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(v_b_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_);
return v___x_3471_;
}
}
else
{
return v___x_3468_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue___boxed(lean_object* v_a_3482_, lean_object* v_b_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue(v_a_3482_, v_b_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec_ref(v_b_3483_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue(lean_object* v_e_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v_w_3497_; lean_object* v_v_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___x_3507_; lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3612_; 
v___x_3507_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_3490_, v_a_3492_);
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3612_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3612_;
goto v_resetjp_3509_;
}
v___jp_3496_:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Meta_isNatValue(v_w_3497_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec_ref(v_w_3497_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; uint8_t v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
v___x_3505_ = lean_unbox(v_a_3504_);
if (v___x_3505_ == 0)
{
lean_dec_ref(v_v_3498_);
return v___x_3503_;
}
else
{
lean_object* v___x_3506_; 
lean_dec_ref_known(v___x_3503_, 1);
v___x_3506_ = l_Lean_Meta_isNatValue(v_v_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec_ref(v_v_3498_);
return v___x_3506_;
}
}
else
{
lean_dec_ref(v_v_3498_);
return v___x_3503_;
}
}
v_resetjp_3509_:
{
lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; 
if (lean_obj_tag(v_a_3508_) == 9)
{
lean_object* v_a_3601_; 
v_a_3601_ = lean_ctor_get(v_a_3508_, 0);
lean_inc_ref(v_a_3601_);
if (lean_obj_tag(v_a_3601_) == 1)
{
lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3610_; 
lean_dec_ref_known(v_a_3508_, 1);
lean_del_object(v___x_3510_);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_a_3601_);
if (v_isSharedCheck_3610_ == 0)
{
lean_object* v_unused_3611_; 
v_unused_3611_ = lean_ctor_get(v_a_3601_, 0);
lean_dec(v_unused_3611_);
v___x_3603_ = v_a_3601_;
v_isShared_3604_ = v_isSharedCheck_3610_;
goto v_resetjp_3602_;
}
else
{
lean_dec(v_a_3601_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3610_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
uint8_t v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3605_ = 1;
v___x_3606_ = lean_box(v___x_3605_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set_tag(v___x_3603_, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3606_);
v___x_3608_ = v___x_3603_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
else
{
lean_dec_ref(v_a_3601_);
v___y_3513_ = v_a_3491_;
v___y_3514_ = v_a_3492_;
v___y_3515_ = v_a_3493_;
v___y_3516_ = v_a_3494_;
goto v___jp_3512_;
}
}
else
{
v___y_3513_ = v_a_3491_;
v___y_3514_ = v_a_3492_;
v___y_3515_ = v_a_3493_;
v___y_3516_ = v_a_3494_;
goto v___jp_3512_;
}
v___jp_3512_:
{
lean_object* v___x_3517_; uint8_t v___x_3518_; 
v___x_3517_ = l_Lean_Expr_consumeMData(v_a_3508_);
v___x_3518_ = l_Lean_Expr_isRawNatLit(v___x_3517_);
lean_dec_ref(v___x_3517_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; 
lean_del_object(v___x_3510_);
v___x_3519_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_3508_, v___y_3514_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3588_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3588_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3588_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; uint8_t v___x_3525_; 
v___x_3524_ = l_Lean_Expr_cleanupAnnotations(v_a_3520_);
lean_dec(v_a_3520_);
v___x_3525_ = l_Lean_Expr_isApp(v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; lean_object* v___x_3528_; 
lean_dec_ref(v___x_3524_);
v___x_3526_ = lean_box(v___x_3518_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3526_);
v___x_3528_ = v___x_3522_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
else
{
lean_object* v_arg_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v_arg_3530_ = lean_ctor_get(v___x_3524_, 1);
lean_inc_ref(v_arg_3530_);
v___x_3531_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3524_);
lean_dec_ref(v___x_3524_);
v___x_3532_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_3533_ = l_Lean_Expr_isConstOf(v___x_3531_, v___x_3532_);
if (v___x_3533_ == 0)
{
uint8_t v___x_3534_; 
v___x_3534_ = l_Lean_Expr_isApp(v___x_3531_);
if (v___x_3534_ == 0)
{
lean_object* v___x_3535_; lean_object* v___x_3537_; 
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_arg_3530_);
v___x_3535_ = lean_box(v___x_3518_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3535_);
v___x_3537_ = v___x_3522_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
else
{
lean_object* v_arg_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v_arg_3539_ = lean_ctor_get(v___x_3531_, 1);
lean_inc_ref(v_arg_3539_);
v___x_3540_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3531_);
lean_dec_ref(v___x_3531_);
v___x_3541_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_3542_ = l_Lean_Expr_isConstOf(v___x_3540_, v___x_3541_);
if (v___x_3542_ == 0)
{
uint8_t v___x_3543_; 
v___x_3543_ = l_Lean_Expr_isApp(v___x_3540_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
lean_dec_ref(v___x_3540_);
lean_dec_ref(v_arg_3539_);
lean_dec_ref(v_arg_3530_);
v___x_3544_ = lean_box(v___x_3518_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3544_);
v___x_3546_ = v___x_3522_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
else
{
lean_object* v_arg_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v_arg_3548_ = lean_ctor_get(v___x_3540_, 1);
lean_inc_ref(v_arg_3548_);
v___x_3549_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3540_);
lean_dec_ref(v___x_3540_);
v___x_3550_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__4));
v___x_3551_ = l_Lean_Expr_isConstOf(v___x_3549_, v___x_3550_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3552_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_3553_ = l_Lean_Expr_isConstOf(v___x_3549_, v___x_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; uint8_t v___x_3555_; 
v___x_3554_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_3555_ = l_Lean_Expr_isConstOf(v___x_3549_, v___x_3554_);
if (v___x_3555_ == 0)
{
uint8_t v___x_3556_; 
v___x_3556_ = l_Lean_Expr_isApp(v___x_3549_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
lean_dec_ref(v___x_3549_);
lean_dec_ref(v_arg_3548_);
lean_dec_ref(v_arg_3539_);
lean_dec_ref(v_arg_3530_);
v___x_3557_ = lean_box(v___x_3518_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3557_);
v___x_3559_ = v___x_3522_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
else
{
lean_object* v___x_3561_; uint8_t v___x_3562_; 
v___x_3561_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3549_);
lean_dec_ref(v___x_3549_);
v___x_3562_ = l_Lean_Expr_isApp(v___x_3561_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; lean_object* v___x_3565_; 
lean_dec_ref(v___x_3561_);
lean_dec_ref(v_arg_3548_);
lean_dec_ref(v_arg_3539_);
lean_dec_ref(v_arg_3530_);
v___x_3563_ = lean_box(v___x_3518_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3563_);
v___x_3565_ = v___x_3522_;
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
lean_object* v___x_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v___x_3567_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3561_);
v___x_3568_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_3569_ = l_Lean_Expr_isConstOf(v___x_3567_, v___x_3568_);
if (v___x_3569_ == 0)
{
uint8_t v___x_3570_; 
lean_dec_ref(v___x_3561_);
lean_dec_ref(v_arg_3548_);
v___x_3570_ = l_Lean_Expr_isApp(v___x_3567_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; lean_object* v___x_3573_; 
lean_dec_ref(v___x_3567_);
lean_dec_ref(v_arg_3539_);
lean_dec_ref(v_arg_3530_);
v___x_3571_ = lean_box(v___x_3518_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3571_);
v___x_3573_ = v___x_3522_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
else
{
lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v___x_3575_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3567_);
lean_dec_ref(v___x_3567_);
v___x_3576_ = ((lean_object*)(l_Lean_Meta_getRatValue_x3f___closed__2));
v___x_3577_ = l_Lean_Expr_isConstOf(v___x_3575_, v___x_3576_);
lean_dec_ref(v___x_3575_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___x_3580_; 
lean_dec_ref(v_arg_3539_);
lean_dec_ref(v_arg_3530_);
v___x_3578_ = lean_box(v___x_3518_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3578_);
v___x_3580_ = v___x_3522_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
else
{
lean_object* v___x_3582_; 
lean_del_object(v___x_3522_);
v___x_3582_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue(v_arg_3539_, v_arg_3530_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec_ref(v_arg_3530_);
return v___x_3582_;
}
}
}
else
{
lean_object* v_arg_3583_; lean_object* v___x_3584_; 
lean_dec_ref(v___x_3567_);
lean_del_object(v___x_3522_);
v_arg_3583_ = lean_ctor_get(v___x_3561_, 1);
lean_inc_ref(v_arg_3583_);
lean_dec_ref(v___x_3561_);
v___x_3584_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(v_arg_3583_, v_arg_3548_, v_arg_3539_, v_arg_3530_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec_ref(v_arg_3530_);
lean_dec_ref(v_arg_3539_);
lean_dec_ref(v_arg_3548_);
return v___x_3584_;
}
}
}
}
else
{
lean_object* v___x_3585_; 
lean_dec_ref(v___x_3549_);
lean_dec_ref(v_arg_3530_);
lean_del_object(v___x_3522_);
v___x_3585_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue(v_arg_3548_, v_arg_3539_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec_ref(v_arg_3539_);
return v___x_3585_;
}
}
else
{
lean_object* v___x_3586_; 
lean_dec_ref(v___x_3549_);
lean_dec_ref(v_arg_3548_);
lean_dec_ref(v_arg_3539_);
lean_del_object(v___x_3522_);
v___x_3586_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue(v_arg_3530_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
return v___x_3586_;
}
}
else
{
lean_dec_ref(v___x_3549_);
lean_dec_ref(v_arg_3530_);
lean_del_object(v___x_3522_);
v_w_3497_ = v_arg_3548_;
v_v_3498_ = v_arg_3539_;
v___y_3499_ = v___y_3513_;
v___y_3500_ = v___y_3514_;
v___y_3501_ = v___y_3515_;
v___y_3502_ = v___y_3516_;
goto v___jp_3496_;
}
}
}
else
{
lean_dec_ref(v___x_3540_);
lean_del_object(v___x_3522_);
v_w_3497_ = v_arg_3539_;
v_v_3498_ = v_arg_3530_;
v___y_3499_ = v___y_3513_;
v___y_3500_ = v___y_3514_;
v___y_3501_ = v___y_3515_;
v___y_3502_ = v___y_3516_;
goto v___jp_3496_;
}
}
}
else
{
lean_object* v___x_3587_; 
lean_dec_ref(v___x_3531_);
lean_del_object(v___x_3522_);
v___x_3587_ = l_Lean_Meta_isNatValue(v_arg_3530_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec_ref(v_arg_3530_);
return v___x_3587_;
}
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
v_a_3589_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3519_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3519_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3599_; 
lean_dec(v_a_3508_);
v___x_3597_ = lean_box(v___x_3518_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3597_);
v___x_3599_ = v___x_3510_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3597_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue___boxed(lean_object* v_e_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_Meta_isLitValue(v_e_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
return v_res_3619_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__2(void){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3624_ = lean_box(0);
v___x_3625_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__1));
v___x_3626_ = l_Lean_mkConst(v___x_3625_, v___x_3624_);
return v___x_3626_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__5(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = lean_box(0);
v___x_3632_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__4));
v___x_3633_ = l_Lean_mkConst(v___x_3632_, v___x_3631_);
return v___x_3633_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__7(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3637_ = lean_box(0);
v___x_3638_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__6));
v___x_3639_ = l_Lean_mkConst(v___x_3638_, v___x_3637_);
return v___x_3639_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__10(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = lean_box(0);
v___x_3645_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__9));
v___x_3646_ = l_Lean_mkConst(v___x_3645_, v___x_3644_);
return v___x_3646_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__11(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = lean_unsigned_to_nat(1u);
v___x_3648_ = lean_nat_to_int(v___x_3647_);
return v___x_3648_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__15(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3654_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_3655_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__14));
v___x_3656_ = l_Lean_mkConst(v___x_3655_, v___x_3654_);
return v___x_3656_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__16(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3657_ = lean_box(0);
v___x_3658_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_3659_ = l_Lean_mkConst(v___x_3658_, v___x_3657_);
return v___x_3659_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__19(void){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = lean_box(0);
v___x_3664_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__18));
v___x_3665_ = l_Lean_mkConst(v___x_3664_, v___x_3663_);
return v___x_3665_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__22(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = lean_box(0);
v___x_3670_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__21));
v___x_3671_ = l_Lean_mkConst(v___x_3670_, v___x_3669_);
return v___x_3671_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__25(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3676_ = lean_box(0);
v___x_3677_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__24));
v___x_3678_ = l_Lean_mkConst(v___x_3677_, v___x_3676_);
return v___x_3678_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__28(void){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3683_ = lean_box(0);
v___x_3684_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__27));
v___x_3685_ = l_Lean_mkConst(v___x_3684_, v___x_3683_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor(lean_object* v_e_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_){
_start:
{
lean_object* v___x_3692_; lean_object* v_a_3693_; lean_object* v___x_3694_; 
v___x_3692_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_3686_, v_a_3688_);
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref(v___x_3692_);
v___x_3694_ = l_Lean_Meta_getNatValue_x3f(v_a_3693_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3784_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3697_ = v___x_3694_;
v_isShared_3698_ = v_isSharedCheck_3784_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3784_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
if (lean_obj_tag(v_a_3695_) == 1)
{
lean_object* v_val_3699_; lean_object* v___x_3700_; uint8_t v___x_3701_; 
lean_dec(v_a_3693_);
v_val_3699_ = lean_ctor_get(v_a_3695_, 0);
lean_inc(v_val_3699_);
lean_dec_ref_known(v_a_3695_, 1);
v___x_3700_ = lean_unsigned_to_nat(0u);
v___x_3701_ = lean_nat_dec_eq(v_val_3699_, v___x_3700_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3708_; 
v___x_3702_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__2, &l_Lean_Meta_litToCtor___closed__2_once, _init_l_Lean_Meta_litToCtor___closed__2);
v___x_3703_ = lean_unsigned_to_nat(1u);
v___x_3704_ = lean_nat_sub(v_val_3699_, v___x_3703_);
lean_dec(v_val_3699_);
v___x_3705_ = l_Lean_mkNatLit(v___x_3704_);
v___x_3706_ = l_Lean_Expr_app___override(v___x_3702_, v___x_3705_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3706_);
v___x_3708_ = v___x_3697_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
else
{
lean_object* v___x_3710_; lean_object* v___x_3712_; 
lean_dec(v_val_3699_);
v___x_3710_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__5, &l_Lean_Meta_litToCtor___closed__5_once, _init_l_Lean_Meta_litToCtor___closed__5);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3710_);
v___x_3712_ = v___x_3697_;
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
}
else
{
lean_object* v___x_3714_; 
lean_del_object(v___x_3697_);
lean_dec(v_a_3695_);
lean_inc(v_a_3693_);
v___x_3714_ = l_Lean_Meta_getIntValue_x3f(v_a_3693_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3775_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3717_ = v___x_3714_;
v_isShared_3718_ = v_isSharedCheck_3775_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3714_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3775_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
if (lean_obj_tag(v_a_3715_) == 1)
{
lean_object* v_val_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
lean_dec(v_a_3693_);
v_val_3719_ = lean_ctor_get(v_a_3715_, 0);
lean_inc(v_val_3719_);
lean_dec_ref_known(v_a_3715_, 1);
v___x_3720_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_3721_ = lean_int_dec_lt(v_val_3719_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3722_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__7, &l_Lean_Meta_litToCtor___closed__7_once, _init_l_Lean_Meta_litToCtor___closed__7);
v___x_3723_ = l_Int_toNat(v_val_3719_);
lean_dec(v_val_3719_);
v___x_3724_ = l_Lean_mkNatLit(v___x_3723_);
v___x_3725_ = l_Lean_Expr_app___override(v___x_3722_, v___x_3724_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3725_);
v___x_3727_ = v___x_3717_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
else
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3737_; 
v___x_3729_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__10, &l_Lean_Meta_litToCtor___closed__10_once, _init_l_Lean_Meta_litToCtor___closed__10);
v___x_3730_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__11, &l_Lean_Meta_litToCtor___closed__11_once, _init_l_Lean_Meta_litToCtor___closed__11);
v___x_3731_ = lean_int_add(v_val_3719_, v___x_3730_);
lean_dec(v_val_3719_);
v___x_3732_ = lean_int_neg(v___x_3731_);
lean_dec(v___x_3731_);
v___x_3733_ = l_Int_toNat(v___x_3732_);
lean_dec(v___x_3732_);
v___x_3734_ = l_Lean_mkNatLit(v___x_3733_);
v___x_3735_ = l_Lean_Expr_app___override(v___x_3729_, v___x_3734_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3735_);
v___x_3737_ = v___x_3717_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3735_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
else
{
lean_object* v___x_3739_; 
lean_del_object(v___x_3717_);
lean_dec(v_a_3715_);
lean_inc(v_a_3693_);
v___x_3739_ = l_Lean_Meta_getFinValue_x3f(v_a_3693_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3766_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3742_ = v___x_3739_;
v_isShared_3743_ = v_isSharedCheck_3766_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3766_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
if (lean_obj_tag(v_a_3740_) == 1)
{
lean_object* v_val_3744_; lean_object* v_fst_3745_; lean_object* v_snd_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3761_; 
lean_dec(v_a_3693_);
v_val_3744_ = lean_ctor_get(v_a_3740_, 0);
lean_inc(v_val_3744_);
lean_dec_ref_known(v_a_3740_, 1);
v_fst_3745_ = lean_ctor_get(v_val_3744_, 0);
lean_inc(v_fst_3745_);
v_snd_3746_ = lean_ctor_get(v_val_3744_, 1);
lean_inc(v_snd_3746_);
lean_dec(v_val_3744_);
v___x_3747_ = l_Lean_mkNatLit(v_snd_3746_);
v___x_3748_ = l_Lean_mkNatLit(v_fst_3745_);
v___x_3749_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__15, &l_Lean_Meta_litToCtor___closed__15_once, _init_l_Lean_Meta_litToCtor___closed__15);
v___x_3750_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__16, &l_Lean_Meta_litToCtor___closed__16_once, _init_l_Lean_Meta_litToCtor___closed__16);
v___x_3751_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__19, &l_Lean_Meta_litToCtor___closed__19_once, _init_l_Lean_Meta_litToCtor___closed__19);
lean_inc_ref_n(v___x_3748_, 2);
lean_inc_ref_n(v___x_3747_, 2);
v___x_3752_ = l_Lean_mkApp4(v___x_3749_, v___x_3750_, v___x_3751_, v___x_3747_, v___x_3748_);
v___x_3753_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__22, &l_Lean_Meta_litToCtor___closed__22_once, _init_l_Lean_Meta_litToCtor___closed__22);
v___x_3754_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__25, &l_Lean_Meta_litToCtor___closed__25_once, _init_l_Lean_Meta_litToCtor___closed__25);
v___x_3755_ = l_Lean_mkAppB(v___x_3754_, v___x_3747_, v___x_3748_);
v___x_3756_ = l_Lean_eagerReflBoolTrue;
v___x_3757_ = l_Lean_mkApp3(v___x_3753_, v___x_3752_, v___x_3755_, v___x_3756_);
v___x_3758_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__28, &l_Lean_Meta_litToCtor___closed__28_once, _init_l_Lean_Meta_litToCtor___closed__28);
v___x_3759_ = l_Lean_mkApp3(v___x_3758_, v___x_3748_, v___x_3747_, v___x_3757_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v___x_3759_);
v___x_3761_ = v___x_3742_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3759_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
else
{
lean_object* v___x_3764_; 
lean_dec(v_a_3740_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v_a_3693_);
v___x_3764_ = v___x_3742_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3693_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec(v_a_3693_);
v_a_3767_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3739_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3739_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec(v_a_3693_);
v_a_3776_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3714_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3714_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec(v_a_3693_);
v_a_3785_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3694_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3694_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor___boxed(lean_object* v_e_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_Meta_litToCtor(v_e_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_);
lean_dec(v_a_3797_);
lean_dec_ref(v_a_3796_);
lean_dec(v_a_3795_);
lean_dec_ref(v_a_3794_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(lean_object* v_fst_3802_, lean_object* v_snd_3803_, lean_object* v_x_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3810_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0));
v___x_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3811_, 0, v_fst_3802_);
lean_ctor_set(v___x_3811_, 1, v_snd_3803_);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
v___x_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_fst_3815_, lean_object* v_snd_3816_, lean_object* v_x_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3815_, v_snd_3816_, v_x_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(lean_object* v_f_3835_, lean_object* v_a_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v___y_3843_; lean_object* v_snd_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3951_; 
v_snd_3863_ = lean_ctor_get(v_a_3836_, 1);
v_isSharedCheck_3951_ = !lean_is_exclusive(v_a_3836_);
if (v_isSharedCheck_3951_ == 0)
{
lean_object* v_unused_3952_; 
v_unused_3952_ = lean_ctor_get(v_a_3836_, 0);
lean_dec(v_unused_3952_);
v___x_3865_ = v_a_3836_;
v_isShared_3866_ = v_isSharedCheck_3951_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_snd_3863_);
lean_dec(v_a_3836_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3951_;
goto v_resetjp_3864_;
}
v___jp_3842_:
{
if (lean_obj_tag(v___y_3843_) == 0)
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3854_; 
v_a_3844_ = lean_ctor_get(v___y_3843_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___y_3843_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3846_ = v___y_3843_;
v_isShared_3847_ = v_isSharedCheck_3854_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___y_3843_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3854_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
if (lean_obj_tag(v_a_3844_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3850_; 
lean_dec_ref(v_f_3835_);
v_a_3848_ = lean_ctor_get(v_a_3844_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v_a_3844_, 1);
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 0, v_a_3848_);
v___x_3850_ = v___x_3846_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
else
{
lean_object* v_a_3852_; 
lean_del_object(v___x_3846_);
v_a_3852_ = lean_ctor_get(v_a_3844_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v_a_3844_, 1);
v_a_3836_ = v_a_3852_;
goto _start;
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec_ref(v_f_3835_);
v_a_3855_ = lean_ctor_get(v___y_3843_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___y_3843_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___y_3843_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___y_3843_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
v_resetjp_3864_:
{
lean_object* v_fst_3867_; lean_object* v_snd_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3950_; 
v_fst_3867_ = lean_ctor_get(v_snd_3863_, 0);
v_snd_3868_ = lean_ctor_get(v_snd_3863_, 1);
v_isSharedCheck_3950_ = !lean_is_exclusive(v_snd_3863_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3870_ = v_snd_3863_;
v_isShared_3871_ = v_isSharedCheck_3950_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_snd_3868_);
lean_inc(v_fst_3867_);
lean_dec(v_snd_3863_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3950_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = lean_box(0);
lean_inc(v_fst_3867_);
v___x_3873_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_fst_3867_, v___y_3838_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3941_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3876_ = v___x_3873_;
v_isShared_3877_ = v_isSharedCheck_3941_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3873_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3941_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3878_; uint8_t v___x_3879_; 
v___x_3878_ = l_Lean_Expr_cleanupAnnotations(v_a_3874_);
lean_dec(v_a_3874_);
v___x_3879_ = l_Lean_Expr_isApp(v___x_3878_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3876_);
lean_del_object(v___x_3870_);
lean_del_object(v___x_3865_);
v___x_3880_ = lean_box(0);
v___x_3881_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3867_, v_snd_3868_, v___x_3880_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
v___y_3843_ = v___x_3881_;
goto v___jp_3842_;
}
else
{
lean_object* v___x_3882_; lean_object* v___x_3883_; uint8_t v___x_3884_; 
v___x_3882_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3878_);
v___x_3883_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2));
v___x_3884_ = l_Lean_Expr_isConstOf(v___x_3882_, v___x_3883_);
if (v___x_3884_ == 0)
{
uint8_t v___x_3885_; 
lean_del_object(v___x_3876_);
v___x_3885_ = l_Lean_Expr_isApp(v___x_3882_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
lean_dec_ref(v___x_3882_);
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3870_);
lean_del_object(v___x_3865_);
v___x_3886_ = lean_box(0);
v___x_3887_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3867_, v_snd_3868_, v___x_3886_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
v___y_3843_ = v___x_3887_;
goto v___jp_3842_;
}
else
{
lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3888_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3882_);
v___x_3889_ = l_Lean_Expr_isApp(v___x_3888_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
lean_dec_ref(v___x_3888_);
lean_dec_ref(v___x_3882_);
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3870_);
lean_del_object(v___x_3865_);
v___x_3890_ = lean_box(0);
v___x_3891_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3867_, v_snd_3868_, v___x_3890_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
v___y_3843_ = v___x_3891_;
goto v___jp_3842_;
}
else
{
lean_object* v___x_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3892_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3888_);
lean_dec_ref(v___x_3888_);
v___x_3893_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4));
v___x_3894_ = l_Lean_Expr_isConstOf(v___x_3892_, v___x_3893_);
lean_dec_ref(v___x_3892_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
lean_dec_ref(v___x_3882_);
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3870_);
lean_del_object(v___x_3865_);
v___x_3895_ = lean_box(0);
v___x_3896_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3867_, v_snd_3868_, v___x_3895_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
v___y_3843_ = v___x_3896_;
goto v___jp_3842_;
}
else
{
lean_object* v_arg_3897_; lean_object* v_arg_3898_; lean_object* v___x_3899_; 
v_arg_3897_ = lean_ctor_get(v___x_3878_, 1);
lean_inc_ref(v_arg_3897_);
lean_dec_ref(v___x_3878_);
v_arg_3898_ = lean_ctor_get(v___x_3882_, 1);
lean_inc_ref(v_arg_3898_);
lean_dec_ref(v___x_3882_);
lean_inc_ref(v_f_3835_);
lean_inc(v___y_3840_);
lean_inc_ref(v___y_3839_);
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
v___x_3899_ = lean_apply_6(v_f_3835_, v_arg_3898_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, lean_box(0));
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3923_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_3923_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3923_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
if (lean_obj_tag(v_a_3900_) == 1)
{
lean_object* v_val_3904_; lean_object* v___x_3905_; lean_object* v___x_3907_; 
lean_del_object(v___x_3902_);
lean_dec(v_fst_3867_);
v_val_3904_ = lean_ctor_get(v_a_3900_, 0);
lean_inc(v_val_3904_);
lean_dec_ref_known(v_a_3900_, 1);
v___x_3905_ = lean_array_push(v_snd_3868_, v_val_3904_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 1, v___x_3905_);
lean_ctor_set(v___x_3870_, 0, v_arg_3897_);
v___x_3907_ = v___x_3870_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_arg_3897_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3909_; 
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 1, v___x_3907_);
lean_ctor_set(v___x_3865_, 0, v___x_3872_);
v___x_3909_ = v___x_3865_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3872_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
v_a_3836_ = v___x_3909_;
goto _start;
}
}
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec(v_a_3900_);
lean_dec_ref(v_arg_3897_);
lean_dec_ref(v_f_3835_);
v___x_3913_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5));
if (v_isShared_3871_ == 0)
{
v___x_3915_ = v___x_3870_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_fst_3867_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v_snd_3868_);
v___x_3915_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3917_; 
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 1, v___x_3915_);
lean_ctor_set(v___x_3865_, 0, v___x_3913_);
v___x_3917_ = v___x_3865_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3913_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3919_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3917_);
v___x_3919_ = v___x_3902_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec_ref(v_arg_3897_);
lean_del_object(v___x_3870_);
lean_dec(v_snd_3868_);
lean_dec(v_fst_3867_);
lean_del_object(v___x_3865_);
lean_dec_ref(v_f_3835_);
v_a_3924_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3899_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3899_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3933_; 
lean_dec_ref(v___x_3882_);
lean_dec_ref(v___x_3878_);
lean_dec_ref(v_f_3835_);
if (v_isShared_3871_ == 0)
{
v___x_3933_ = v___x_3870_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_fst_3867_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_snd_3868_);
v___x_3933_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3935_; 
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 1, v___x_3933_);
lean_ctor_set(v___x_3865_, 0, v___x_3872_);
v___x_3935_ = v___x_3865_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3872_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v___x_3933_);
v___x_3935_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3937_; 
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 0, v___x_3935_);
v___x_3937_ = v___x_3876_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_del_object(v___x_3870_);
lean_dec(v_snd_3868_);
lean_dec(v_fst_3867_);
lean_del_object(v___x_3865_);
lean_dec_ref(v_f_3835_);
v_a_3942_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3873_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3873_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___boxed(lean_object* v_f_3953_, lean_object* v_a_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_3953_, v_a_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg(lean_object* v_e_3963_, lean_object* v_f_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_4007_; 
v___x_3970_ = l_Lean_Expr_consumeMData(v_e_3963_);
v___x_3971_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_3970_, v_a_3966_);
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3974_ = v___x_3971_;
v_isShared_3975_ = v_isSharedCheck_4007_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3971_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_4007_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3976_ = ((lean_object*)(l_Lean_Meta_getListLitOf_x3f___redArg___closed__0));
v___x_3977_ = lean_box(0);
v___x_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3978_, 0, v_a_3972_);
lean_ctor_set(v___x_3978_, 1, v___x_3976_);
v___x_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3977_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_3964_, v___x_3979_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3998_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3983_ = v___x_3980_;
v_isShared_3984_ = v_isSharedCheck_3998_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3980_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3998_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v_fst_3985_; 
v_fst_3985_ = lean_ctor_get(v_a_3981_, 0);
if (lean_obj_tag(v_fst_3985_) == 0)
{
lean_object* v_snd_3986_; lean_object* v_snd_3987_; lean_object* v___x_3989_; 
v_snd_3986_ = lean_ctor_get(v_a_3981_, 1);
lean_inc(v_snd_3986_);
lean_dec(v_a_3981_);
v_snd_3987_ = lean_ctor_get(v_snd_3986_, 1);
lean_inc(v_snd_3987_);
lean_dec(v_snd_3986_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set_tag(v___x_3974_, 1);
lean_ctor_set(v___x_3974_, 0, v_snd_3987_);
v___x_3989_ = v___x_3974_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_snd_3987_);
v___x_3989_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3991_; 
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v___x_3989_);
v___x_3991_ = v___x_3983_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
else
{
lean_object* v_val_3994_; lean_object* v___x_3996_; 
lean_inc_ref(v_fst_3985_);
lean_dec(v_a_3981_);
lean_del_object(v___x_3974_);
v_val_3994_ = lean_ctor_get(v_fst_3985_, 0);
lean_inc(v_val_3994_);
lean_dec_ref_known(v_fst_3985_, 1);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v_val_3994_);
v___x_3996_ = v___x_3983_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_val_3994_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
else
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_del_object(v___x_3974_);
v_a_3999_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3980_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3980_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___boxed(lean_object* v_e_4008_, lean_object* v_f_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_4008_, v_f_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
lean_dec_ref(v_e_4008_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f(lean_object* v_00_u03b1_4016_, lean_object* v_e_4017_, lean_object* v_f_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_4017_, v_f_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___boxed(lean_object* v_00_u03b1_4025_, lean_object* v_e_4026_, lean_object* v_f_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Lean_Meta_getListLitOf_x3f(v_00_u03b1_4025_, v_e_4026_, v_f_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_e_4026_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(lean_object* v_00_u03b1_4034_, lean_object* v_f_4035_, lean_object* v_inst_4036_, lean_object* v_a_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v___x_4043_; 
v___x_4043_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_4035_, v_a_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___boxed(lean_object* v_00_u03b1_4044_, lean_object* v_f_4045_, lean_object* v_inst_4046_, lean_object* v_a_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(v_00_u03b1_4044_, v_f_4045_, v_inst_4046_, v_a_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0(lean_object* v_s_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4060_, 0, v_s_4054_);
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0___boxed(lean_object* v_s_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Lean_Meta_getListLit_x3f___lam__0(v_s_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f(lean_object* v_e_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v___f_4076_; lean_object* v___x_4077_; 
v___f_4076_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_4077_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_4070_, v___f_4076_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___boxed(lean_object* v_e_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_Meta_getListLit_x3f(v_e_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec(v_a_4080_);
lean_dec_ref(v_a_4079_);
lean_dec_ref(v_e_4078_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg(lean_object* v_e_4089_, lean_object* v_f_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v_a_4101_; lean_object* v___x_4102_; 
v___x_4099_ = l_Lean_Expr_consumeMData(v_e_4089_);
v___x_4100_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_4099_, v_a_4092_);
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref(v___x_4100_);
v___x_4102_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_4101_, v_a_4092_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v___x_4102_, 1);
v___x_4104_ = l_Lean_Expr_cleanupAnnotations(v_a_4103_);
lean_dec(v_a_4103_);
v___x_4105_ = l_Lean_Expr_isApp(v___x_4104_);
if (v___x_4105_ == 0)
{
lean_dec_ref(v___x_4104_);
lean_dec_ref(v_f_4090_);
goto v___jp_4096_;
}
else
{
lean_object* v___x_4106_; uint8_t v___x_4107_; 
v___x_4106_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4104_);
v___x_4107_ = l_Lean_Expr_isApp(v___x_4106_);
if (v___x_4107_ == 0)
{
lean_dec_ref(v___x_4106_);
lean_dec_ref(v___x_4104_);
lean_dec_ref(v_f_4090_);
goto v___jp_4096_;
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
v___x_4108_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4106_);
lean_dec_ref(v___x_4106_);
v___x_4109_ = ((lean_object*)(l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1));
v___x_4110_ = l_Lean_Expr_isConstOf(v___x_4108_, v___x_4109_);
lean_dec_ref(v___x_4108_);
if (v___x_4110_ == 0)
{
lean_dec_ref(v___x_4104_);
lean_dec_ref(v_f_4090_);
goto v___jp_4096_;
}
else
{
lean_object* v_arg_4111_; lean_object* v___x_4112_; 
v_arg_4111_ = lean_ctor_get(v___x_4104_, 1);
lean_inc_ref(v_arg_4111_);
lean_dec_ref(v___x_4104_);
v___x_4112_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_arg_4111_, v_f_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_);
lean_dec_ref(v_arg_4111_);
return v___x_4112_;
}
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec_ref(v_f_4090_);
v_a_4113_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4102_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4102_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
v___jp_4096_:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4097_ = lean_box(0);
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
return v___x_4098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___boxed(lean_object* v_e_4121_, lean_object* v_f_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_4121_, v_f_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
lean_dec_ref(v_e_4121_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f(lean_object* v_00_u03b1_4129_, lean_object* v_e_4130_, lean_object* v_f_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_4130_, v_f_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___boxed(lean_object* v_00_u03b1_4138_, lean_object* v_e_4139_, lean_object* v_f_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Meta_getArrayLitOf_x3f(v_00_u03b1_4138_, v_e_4139_, v_f_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec_ref(v_e_4139_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object* v_e_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_){
_start:
{
lean_object* v___f_4153_; lean_object* v___x_4154_; 
v___f_4153_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_4154_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_4147_, v___f_4153_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f___boxed(lean_object* v_e_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l_Lean_Meta_getArrayLit_x3f(v_e_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
lean_dec(v_a_4159_);
lean_dec_ref(v_a_4158_);
lean_dec(v_a_4157_);
lean_dec_ref(v_a_4156_);
lean_dec_ref(v_e_4155_);
return v_res_4161_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
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
res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
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
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
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
res = initialize_Lean_Util_SafeExponentiation(builtin);
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
