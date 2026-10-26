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
double lean_float_of_nat(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
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
double lean_float_negate(double);
lean_object* lean_nat_pow(lean_object*, lean_object*);
float lean_float32_of_nat(lean_object*);
float l_Float32_ofScientific(lean_object*, uint8_t, lean_object*);
float lean_float32_negate(float);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(lean_object* v_e_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Expr_consumeMData(v_e_442_);
if (lean_obj_tag(v___x_443_) == 4)
{
lean_object* v_declName_444_; 
v_declName_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_declName_444_);
lean_dec_ref_known(v___x_443_, 2);
if (lean_obj_tag(v_declName_444_) == 1)
{
lean_object* v_pre_445_; 
v_pre_445_ = lean_ctor_get(v_declName_444_, 0);
lean_inc(v_pre_445_);
if (lean_obj_tag(v_pre_445_) == 1)
{
lean_object* v_pre_446_; 
v_pre_446_ = lean_ctor_get(v_pre_445_, 0);
if (lean_obj_tag(v_pre_446_) == 0)
{
lean_object* v_str_447_; lean_object* v_str_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_str_447_ = lean_ctor_get(v_declName_444_, 1);
lean_inc_ref(v_str_447_);
lean_dec_ref_known(v_declName_444_, 2);
v_str_448_ = lean_ctor_get(v_pre_445_, 1);
lean_inc_ref(v_str_448_);
lean_dec_ref_known(v_pre_445_, 2);
v___x_449_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0));
v___x_450_ = lean_string_dec_eq(v_str_448_, v___x_449_);
lean_dec_ref(v_str_448_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
lean_dec_ref(v_str_447_);
v___x_451_ = lean_box(0);
return v___x_451_;
}
else
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1));
v___x_453_ = lean_string_dec_eq(v_str_447_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2));
v___x_455_ = lean_string_dec_eq(v_str_447_, v___x_454_);
lean_dec_ref(v_str_447_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_box(0);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_box(v___x_453_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec_ref(v_str_447_);
v___x_459_ = lean_box(v___x_453_);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
}
else
{
lean_object* v___x_461_; 
lean_dec_ref_known(v_pre_445_, 2);
lean_dec_ref_known(v_declName_444_, 2);
v___x_461_ = lean_box(0);
return v___x_461_;
}
}
else
{
lean_object* v___x_462_; 
lean_dec(v_pre_445_);
lean_dec_ref_known(v_declName_444_, 2);
v___x_462_ = lean_box(0);
return v___x_462_;
}
}
else
{
lean_object* v___x_463_; 
lean_dec(v_declName_444_);
v___x_463_ = lean_box(0);
return v___x_463_;
}
}
else
{
lean_object* v___x_464_; 
lean_dec_ref(v___x_443_);
v___x_464_ = lean_box(0);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___boxed(lean_object* v_e_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_e_465_);
lean_dec_ref(v_e_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f_spec__0(lean_object* v_a_467_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_nat_to_int(v_a_467_);
v___x_469_ = l_Rat_ofInt(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(lean_object* v_e_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___x_521_; 
lean_inc_ref(v_e_478_);
v___x_521_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_478_, v_a_480_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = l_Lean_Expr_cleanupAnnotations(v_a_522_);
lean_dec(v_a_522_);
v___x_524_ = l_Lean_Expr_isApp(v___x_523_);
if (v___x_524_ == 0)
{
lean_dec_ref(v___x_523_);
v___y_485_ = v_a_479_;
v___y_486_ = v_a_480_;
v___y_487_ = v_a_481_;
v___y_488_ = v_a_482_;
goto v___jp_484_;
}
else
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = l_Lean_Expr_appFnCleanup___redArg(v___x_523_);
v___x_526_ = l_Lean_Expr_isApp(v___x_525_);
if (v___x_526_ == 0)
{
lean_dec_ref(v___x_525_);
lean_dec_ref(v___x_523_);
v___y_485_ = v_a_479_;
v___y_486_ = v_a_480_;
v___y_487_ = v_a_481_;
v___y_488_ = v_a_482_;
goto v___jp_484_;
}
else
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = l_Lean_Expr_appFnCleanup___redArg(v___x_525_);
v___x_528_ = l_Lean_Expr_isApp(v___x_527_);
if (v___x_528_ == 0)
{
lean_dec_ref(v___x_527_);
lean_dec_ref(v___x_525_);
lean_dec_ref(v___x_523_);
v___y_485_ = v_a_479_;
v___y_486_ = v_a_480_;
v___y_487_ = v_a_481_;
v___y_488_ = v_a_482_;
goto v___jp_484_;
}
else
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = l_Lean_Expr_appFnCleanup___redArg(v___x_527_);
v___x_530_ = l_Lean_Expr_isApp(v___x_529_);
if (v___x_530_ == 0)
{
lean_dec_ref(v___x_529_);
lean_dec_ref(v___x_527_);
lean_dec_ref(v___x_525_);
lean_dec_ref(v___x_523_);
v___y_485_ = v_a_479_;
v___y_486_ = v_a_480_;
v___y_487_ = v_a_481_;
v___y_488_ = v_a_482_;
goto v___jp_484_;
}
else
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = l_Lean_Expr_appFnCleanup___redArg(v___x_529_);
lean_dec_ref(v___x_529_);
v___x_532_ = l_Lean_Expr_isApp(v___x_531_);
if (v___x_532_ == 0)
{
lean_dec_ref(v___x_531_);
lean_dec_ref(v___x_527_);
lean_dec_ref(v___x_525_);
lean_dec_ref(v___x_523_);
v___y_485_ = v_a_479_;
v___y_486_ = v_a_480_;
v___y_487_ = v_a_481_;
v___y_488_ = v_a_482_;
goto v___jp_484_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = l_Lean_Expr_appFnCleanup___redArg(v___x_531_);
v___x_534_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_535_ = l_Lean_Expr_isConstOf(v___x_533_, v___x_534_);
lean_dec_ref(v___x_533_);
if (v___x_535_ == 0)
{
lean_dec_ref(v___x_531_);
lean_dec_ref(v___x_527_);
lean_dec_ref(v___x_525_);
lean_dec_ref(v___x_523_);
v___y_485_ = v_a_479_;
v___y_486_ = v_a_480_;
v___y_487_ = v_a_481_;
v___y_488_ = v_a_482_;
goto v___jp_484_;
}
else
{
lean_object* v_arg_536_; lean_object* v_arg_537_; lean_object* v_arg_538_; lean_object* v_arg_539_; lean_object* v___x_540_; 
lean_dec_ref(v_e_478_);
v_arg_536_ = lean_ctor_get(v___x_523_, 1);
lean_inc_ref(v_arg_536_);
lean_dec_ref(v___x_523_);
v_arg_537_ = lean_ctor_get(v___x_525_, 1);
lean_inc_ref(v_arg_537_);
lean_dec_ref(v___x_525_);
v_arg_538_ = lean_ctor_get(v___x_527_, 1);
lean_inc_ref(v_arg_538_);
lean_dec_ref(v___x_527_);
v_arg_539_ = lean_ctor_get(v___x_531_, 1);
lean_inc_ref(v_arg_539_);
lean_dec_ref(v___x_531_);
v___x_540_ = l_Lean_Meta_whnfD(v_arg_539_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_607_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_607_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_607_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_607_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_546_ = l_Lean_Expr_isConstOf(v_a_541_, v___x_545_);
lean_dec(v_a_541_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_549_; 
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_537_);
lean_dec_ref(v_arg_536_);
v___x_547_ = lean_box(0);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_547_);
v___x_549_ = v___x_543_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
else
{
lean_object* v___x_551_; 
v___x_551_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_537_);
lean_dec_ref(v_arg_537_);
if (lean_obj_tag(v___x_551_) == 1)
{
lean_object* v_val_552_; lean_object* v___x_553_; 
lean_del_object(v___x_543_);
v_val_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_val_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_553_ = l_Lean_Meta_getNatValue_x3f(v_arg_538_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec_ref(v_arg_538_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_594_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_594_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_594_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_594_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
if (lean_obj_tag(v_a_554_) == 0)
{
lean_object* v___x_558_; lean_object* v___x_560_; 
lean_dec(v_val_552_);
lean_dec_ref(v_arg_536_);
v___x_558_ = lean_box(0);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
else
{
lean_object* v_val_562_; lean_object* v___x_563_; 
lean_del_object(v___x_556_);
v_val_562_ = lean_ctor_get(v_a_554_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v_a_554_, 1);
v___x_563_ = l_Lean_Meta_getNatValue_x3f(v_arg_536_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec_ref(v_arg_536_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_585_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_585_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_585_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_585_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
if (lean_obj_tag(v_a_564_) == 0)
{
lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec(v_val_562_);
lean_dec(v_val_552_);
v___x_568_ = lean_box(0);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_584_; 
v_val_572_ = lean_ctor_get(v_a_564_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_564_);
if (v_isSharedCheck_584_ == 0)
{
v___x_574_ = v_a_564_;
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v_a_564_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_576_ = lean_unbox(v_val_552_);
lean_dec(v_val_552_);
v___x_577_ = l_Rat_ofScientific(v_val_562_, v___x_576_, v_val_572_);
lean_dec(v_val_572_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_577_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_579_);
v___x_581_ = v___x_566_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v_val_562_);
lean_dec(v_val_552_);
v_a_586_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_563_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_563_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec(v_val_552_);
lean_dec_ref(v_arg_536_);
v_a_595_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_553_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_553_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_605_; 
lean_dec(v___x_551_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_536_);
v___x_603_ = lean_box(0);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_603_);
v___x_605_ = v___x_543_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_537_);
lean_dec_ref(v_arg_536_);
v_a_608_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_540_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_540_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
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
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_e_478_);
v_a_616_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_521_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_521_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
v___jp_484_:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_490_ = l_Lean_Meta_getOfNatValue_x3f(v_e_478_, v___x_489_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_512_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_512_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_512_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_512_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
if (lean_obj_tag(v_a_491_) == 0)
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = lean_box(0);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
else
{
lean_object* v_val_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_511_; 
v_val_499_ = lean_ctor_get(v_a_491_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_a_491_);
if (v_isSharedCheck_511_ == 0)
{
v___x_501_ = v_a_491_;
v_isShared_502_ = v_isSharedCheck_511_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_val_499_);
lean_dec(v_a_491_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_511_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_fst_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v_fst_503_ = lean_ctor_get(v_val_499_, 0);
lean_inc(v_fst_503_);
lean_dec(v_val_499_);
v___x_504_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f_spec__0(v_fst_503_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_504_);
v___x_506_ = v___x_501_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_510_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_506_);
v___x_508_ = v___x_493_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_a_513_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_490_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_490_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___boxed(lean_object* v_e_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(lean_object* v_e_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
lean_inc_ref(v_e_631_);
v___x_641_ = l_Lean_Meta_getOfNatValue_x3f(v_e_631_, v___x_640_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_711_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_711_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_711_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_711_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
if (lean_obj_tag(v_a_642_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v_e_631_);
v_val_646_ = lean_ctor_get(v_a_642_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v_a_642_);
if (v_isSharedCheck_658_ == 0)
{
v___x_648_ = v_a_642_;
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_val_646_);
lean_dec(v_a_642_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_fst_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v_fst_650_ = lean_ctor_get(v_val_646_, 0);
lean_inc(v_fst_650_);
lean_dec(v_val_646_);
v___x_651_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f_spec__0(v_fst_650_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_651_);
v___x_653_ = v___x_648_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_651_);
v___x_653_ = v_reuseFailAlloc_657_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_655_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_653_);
v___x_655_ = v___x_644_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
else
{
lean_object* v___x_659_; 
lean_del_object(v___x_644_);
lean_dec(v_a_642_);
v___x_659_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_631_, v_a_633_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
v___x_661_ = l_Lean_Expr_cleanupAnnotations(v_a_660_);
lean_dec(v_a_660_);
v___x_662_ = l_Lean_Expr_isApp(v___x_661_);
if (v___x_662_ == 0)
{
lean_dec_ref(v___x_661_);
goto v___jp_637_;
}
else
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = l_Lean_Expr_appFnCleanup___redArg(v___x_661_);
v___x_664_ = l_Lean_Expr_isApp(v___x_663_);
if (v___x_664_ == 0)
{
lean_dec_ref(v___x_663_);
lean_dec_ref(v___x_661_);
goto v___jp_637_;
}
else
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = l_Lean_Expr_appFnCleanup___redArg(v___x_663_);
lean_dec_ref(v___x_663_);
v___x_666_ = l_Lean_Expr_isApp(v___x_665_);
if (v___x_666_ == 0)
{
lean_dec_ref(v___x_665_);
lean_dec_ref(v___x_661_);
goto v___jp_637_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_667_ = l_Lean_Expr_appFnCleanup___redArg(v___x_665_);
lean_dec_ref(v___x_665_);
v___x_668_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_669_ = l_Lean_Expr_isConstOf(v___x_667_, v___x_668_);
lean_dec_ref(v___x_667_);
if (v___x_669_ == 0)
{
lean_dec_ref(v___x_661_);
goto v___jp_637_;
}
else
{
lean_object* v_arg_670_; lean_object* v___x_671_; 
v_arg_670_ = lean_ctor_get(v___x_661_, 1);
lean_inc_ref(v_arg_670_);
lean_dec_ref(v___x_661_);
v___x_671_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_670_, v___x_640_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_694_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_694_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_694_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_694_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
if (lean_obj_tag(v_a_672_) == 1)
{
lean_object* v_val_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_689_; 
v_val_676_ = lean_ctor_get(v_a_672_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v_a_672_);
if (v_isSharedCheck_689_ == 0)
{
v___x_678_ = v_a_672_;
v_isShared_679_ = v_isSharedCheck_689_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_val_676_);
lean_dec(v_a_672_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_689_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_fst_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v_fst_680_ = lean_ctor_get(v_val_676_, 0);
lean_inc(v_fst_680_);
lean_dec(v_val_676_);
v___x_681_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f_spec__0(v_fst_680_);
v___x_682_ = l_Rat_neg(v___x_681_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_682_);
v___x_684_ = v___x_678_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_688_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_686_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_684_);
v___x_686_ = v___x_674_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_692_; 
lean_dec(v_a_672_);
v___x_690_ = lean_box(0);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_690_);
v___x_692_ = v___x_674_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
v_a_695_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_671_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_671_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
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
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_a_703_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_659_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_659_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v_e_631_);
v_a_712_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_641_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_641_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
v___jp_637_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_box(0);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___boxed(lean_object* v_e_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getRatValue_x3f(lean_object* v_e_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_738_; 
lean_inc_ref(v_e_732_);
v___x_738_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_732_, v_a_734_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = l_Lean_Expr_cleanupAnnotations(v_a_739_);
lean_dec(v_a_739_);
v___x_741_ = l_Lean_Expr_isApp(v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
lean_dec_ref(v___x_740_);
v___x_742_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = l_Lean_Expr_appFnCleanup___redArg(v___x_740_);
v___x_744_ = l_Lean_Expr_isApp(v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
lean_dec_ref(v___x_743_);
lean_dec_ref(v___x_740_);
v___x_745_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_745_;
}
else
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = l_Lean_Expr_appFnCleanup___redArg(v___x_743_);
v___x_747_ = l_Lean_Expr_isApp(v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
lean_dec_ref(v___x_746_);
lean_dec_ref(v___x_743_);
lean_dec_ref(v___x_740_);
v___x_748_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_748_;
}
else
{
lean_object* v_arg_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_arg_749_ = lean_ctor_get(v___x_740_, 1);
lean_inc_ref(v_arg_749_);
lean_dec_ref(v___x_740_);
v___x_750_ = l_Lean_Expr_appFnCleanup___redArg(v___x_746_);
lean_dec_ref(v___x_746_);
v___x_751_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_752_ = l_Lean_Expr_isConstOf(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
uint8_t v___x_753_; 
v___x_753_ = l_Lean_Expr_isApp(v___x_750_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v_arg_749_);
lean_dec_ref(v___x_743_);
v___x_754_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_754_;
}
else
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = l_Lean_Expr_appFnCleanup___redArg(v___x_750_);
lean_dec_ref(v___x_750_);
v___x_756_ = l_Lean_Expr_isApp(v___x_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec_ref(v___x_755_);
lean_dec_ref(v_arg_749_);
lean_dec_ref(v___x_743_);
v___x_757_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_758_ = l_Lean_Expr_appFnCleanup___redArg(v___x_755_);
lean_dec_ref(v___x_755_);
v___x_759_ = l_Lean_Expr_isApp(v___x_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; 
lean_dec_ref(v___x_758_);
lean_dec_ref(v_arg_749_);
lean_dec_ref(v___x_743_);
v___x_760_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_760_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = l_Lean_Expr_appFnCleanup___redArg(v___x_758_);
lean_dec_ref(v___x_758_);
v___x_762_ = ((lean_object*)(l_Lean_Meta_getRatValue_x3f___closed__2));
v___x_763_ = l_Lean_Expr_isConstOf(v___x_761_, v___x_762_);
lean_dec_ref(v___x_761_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
lean_dec_ref(v_arg_749_);
lean_dec_ref(v___x_743_);
v___x_764_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_764_;
}
else
{
lean_object* v_arg_765_; lean_object* v___x_766_; 
lean_dec_ref(v_e_732_);
v_arg_765_ = lean_ctor_get(v___x_743_, 1);
lean_inc_ref(v_arg_765_);
lean_dec_ref(v___x_743_);
v___x_766_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_arg_765_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_809_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_809_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_809_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_809_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
if (lean_obj_tag(v_a_767_) == 1)
{
lean_object* v_val_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_del_object(v___x_769_);
v_val_771_ = lean_ctor_get(v_a_767_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v_a_767_, 1);
v___x_772_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_773_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_749_, v___x_772_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_796_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_796_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_796_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_796_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
if (lean_obj_tag(v_a_774_) == 1)
{
lean_object* v_val_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_791_; 
v_val_778_ = lean_ctor_get(v_a_774_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v_a_774_);
if (v_isSharedCheck_791_ == 0)
{
v___x_780_ = v_a_774_;
v_isShared_781_ = v_isSharedCheck_791_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_val_778_);
lean_dec(v_a_774_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_791_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_fst_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v_fst_782_ = lean_ctor_get(v_val_778_, 0);
lean_inc(v_fst_782_);
lean_dec(v_val_778_);
v___x_783_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f_spec__0(v_fst_782_);
v___x_784_ = l_Rat_div(v_val_771_, v___x_783_);
lean_dec(v_val_771_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_784_);
v___x_786_ = v___x_780_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_786_);
v___x_788_ = v___x_776_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_794_; 
lean_dec(v_a_774_);
lean_dec(v_val_771_);
v___x_792_ = lean_box(0);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_792_);
v___x_794_ = v___x_776_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec(v_val_771_);
v_a_797_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_773_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_773_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec(v_a_767_);
lean_dec_ref(v_arg_749_);
v___x_805_ = lean_box(0);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_805_);
v___x_807_ = v___x_769_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_dec_ref(v_arg_749_);
return v___x_766_;
}
}
}
}
}
}
else
{
lean_object* v___x_810_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_743_);
lean_dec_ref(v_e_732_);
v___x_810_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f(v_arg_749_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_831_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_831_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_831_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_831_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
if (lean_obj_tag(v_a_811_) == 1)
{
lean_object* v_val_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_826_; 
v_val_815_ = lean_ctor_get(v_a_811_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_a_811_);
if (v_isSharedCheck_826_ == 0)
{
v___x_817_ = v_a_811_;
v_isShared_818_ = v_isSharedCheck_826_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_val_815_);
lean_dec(v_a_811_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_826_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = l_Rat_neg(v_val_815_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_819_);
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_825_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_823_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_821_);
v___x_823_ = v___x_813_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec(v_a_811_);
v___x_827_ = lean_box(0);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_827_);
v___x_829_ = v___x_813_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
return v___x_810_;
}
}
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec_ref(v_e_732_);
v_a_832_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_738_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_738_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getRatValue_x3f___boxed(lean_object* v_e_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Meta_getRatValue_x3f(v_e_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f(lean_object* v_e_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_851_, v_a_853_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = l_Lean_Expr_cleanupAnnotations(v_a_861_);
lean_dec(v_a_861_);
v___x_863_ = l_Lean_Expr_isApp(v___x_862_);
if (v___x_863_ == 0)
{
lean_dec_ref(v___x_862_);
goto v___jp_857_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = l_Lean_Expr_appFnCleanup___redArg(v___x_862_);
v___x_865_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_866_ = l_Lean_Expr_isConstOf(v___x_864_, v___x_865_);
lean_dec_ref(v___x_864_);
if (v___x_866_ == 0)
{
lean_dec_ref(v___x_862_);
goto v___jp_857_;
}
else
{
lean_object* v_arg_867_; lean_object* v___x_868_; 
v_arg_867_ = lean_ctor_get(v___x_862_, 1);
lean_inc_ref(v_arg_867_);
lean_dec_ref(v___x_862_);
v___x_868_ = l_Lean_Meta_getNatValue_x3f(v_arg_867_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec_ref(v_arg_867_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_890_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_890_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_890_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_890_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
if (lean_obj_tag(v_a_869_) == 1)
{
lean_object* v_val_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_885_; 
v_val_873_ = lean_ctor_get(v_a_869_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v_a_869_);
if (v_isSharedCheck_885_ == 0)
{
v___x_875_ = v_a_869_;
v_isShared_876_ = v_isSharedCheck_885_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_val_873_);
lean_dec(v_a_869_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_885_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
uint32_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_877_ = l_Char_ofNat(v_val_873_);
lean_dec(v_val_873_);
v___x_878_ = lean_box_uint32(v___x_877_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_878_);
v___x_880_ = v___x_875_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_884_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_880_);
v___x_882_ = v___x_871_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v___x_886_; lean_object* v___x_888_; 
lean_dec(v_a_869_);
v___x_886_ = lean_box(0);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_886_);
v___x_888_ = v___x_871_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
v_a_891_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_868_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_868_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v_a_899_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_860_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_860_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
v___jp_857_:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_box(0);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f___boxed(lean_object* v_e_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Meta_getCharValue_x3f(v_e_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStringValue_x3f(lean_object* v_e_914_){
_start:
{
if (lean_obj_tag(v_e_914_) == 9)
{
lean_object* v_a_915_; 
v_a_915_ = lean_ctor_get(v_e_914_, 0);
lean_inc_ref(v_a_915_);
lean_dec_ref_known(v_e_914_, 1);
if (lean_obj_tag(v_a_915_) == 1)
{
lean_object* v_val_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
v_val_916_ = lean_ctor_get(v_a_915_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v_a_915_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v_a_915_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_val_916_);
lean_dec(v_a_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_val_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
lean_object* v___x_924_; 
lean_dec_ref(v_a_915_);
v___x_924_ = lean_box(0);
return v___x_924_;
}
}
else
{
lean_object* v___x_925_; 
lean_dec_ref(v_e_914_);
v___x_925_ = lean_box(0);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f(lean_object* v_e_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_936_ = l_Lean_Meta_getOfNatValue_x3f(v_e_929_, v___x_935_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_1005_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_1005_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_1005_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
if (lean_obj_tag(v_a_937_) == 0)
{
lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_941_ = lean_box(0);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
else
{
lean_object* v_val_945_; lean_object* v_fst_946_; lean_object* v_snd_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_1004_; 
lean_del_object(v___x_939_);
v_val_945_ = lean_ctor_get(v_a_937_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v_a_937_, 1);
v_fst_946_ = lean_ctor_get(v_val_945_, 0);
v_snd_947_ = lean_ctor_get(v_val_945_, 1);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_val_945_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_949_ = v_val_945_;
v_isShared_950_ = v_isSharedCheck_1004_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_snd_947_);
lean_inc(v_fst_946_);
lean_dec(v_val_945_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_1004_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = l_Lean_Expr_appArg_x21(v_snd_947_);
lean_dec(v_snd_947_);
v___x_952_ = l_Lean_Meta_whnfD(v___x_951_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_954_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v___x_954_ = l_Lean_Meta_getNatValue_x3f(v_a_953_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
lean_dec(v_a_953_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_987_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_987_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_987_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_987_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
if (lean_obj_tag(v_a_955_) == 0)
{
lean_object* v___x_959_; lean_object* v___x_961_; 
lean_del_object(v___x_949_);
lean_dec(v_fst_946_);
v___x_959_ = lean_box(0);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
else
{
lean_object* v_val_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_986_; 
v_val_963_ = lean_ctor_get(v_a_955_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v_a_955_);
if (v_isSharedCheck_986_ == 0)
{
v___x_965_ = v_a_955_;
v_isShared_966_ = v_isSharedCheck_986_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_val_963_);
lean_dec(v_a_955_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_986_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_zero_967_; uint8_t v_isZero_968_; 
v_zero_967_ = lean_unsigned_to_nat(0u);
v_isZero_968_ = lean_nat_dec_eq(v_val_963_, v_zero_967_);
if (v_isZero_968_ == 1)
{
lean_object* v___x_969_; lean_object* v___x_971_; 
lean_del_object(v___x_965_);
lean_dec(v_val_963_);
lean_del_object(v___x_949_);
lean_dec(v_fst_946_);
v___x_969_ = lean_box(0);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_969_);
v___x_971_ = v___x_957_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
else
{
lean_object* v_one_973_; lean_object* v_n_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
v_one_973_ = lean_unsigned_to_nat(1u);
v_n_974_ = lean_nat_sub(v_val_963_, v_one_973_);
lean_dec(v_val_963_);
v___x_975_ = lean_nat_add(v_n_974_, v_one_973_);
lean_dec(v_n_974_);
v___x_976_ = lean_nat_mod(v_fst_946_, v___x_975_);
lean_dec(v_fst_946_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v___x_976_);
lean_ctor_set(v___x_949_, 0, v___x_975_);
v___x_978_ = v___x_949_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_976_);
v___x_978_ = v_reuseFailAlloc_985_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_978_);
v___x_980_ = v___x_965_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_984_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_980_);
v___x_982_ = v___x_957_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
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
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_del_object(v___x_949_);
lean_dec(v_fst_946_);
v_a_988_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_954_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_954_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_del_object(v___x_949_);
lean_dec(v_fst_946_);
v_a_996_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_952_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_952_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_a_1006_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_936_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_936_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f___boxed(lean_object* v_e_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Meta_getFinValue_x3f(v_e_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object* v_e_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v_nExpr_1113_; lean_object* v_vExpr_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___x_1169_; 
lean_inc_ref(v_e_1031_);
v___x_1169_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1031_, v_a_1033_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = l_Lean_Expr_cleanupAnnotations(v_a_1170_);
lean_dec(v_a_1170_);
v___x_1172_ = l_Lean_Expr_isApp(v___x_1171_);
if (v___x_1172_ == 0)
{
lean_dec_ref(v___x_1171_);
v___y_1038_ = v_a_1032_;
v___y_1039_ = v_a_1033_;
v___y_1040_ = v_a_1034_;
v___y_1041_ = v_a_1035_;
goto v___jp_1037_;
}
else
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1171_);
v___x_1174_ = l_Lean_Expr_isApp(v___x_1173_);
if (v___x_1174_ == 0)
{
lean_dec_ref(v___x_1173_);
lean_dec_ref(v___x_1171_);
v___y_1038_ = v_a_1032_;
v___y_1039_ = v_a_1033_;
v___y_1040_ = v_a_1034_;
v___y_1041_ = v_a_1035_;
goto v___jp_1037_;
}
else
{
lean_object* v_arg_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_arg_1175_ = lean_ctor_get(v___x_1173_, 1);
lean_inc_ref(v_arg_1175_);
v___x_1176_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1173_);
lean_dec_ref(v___x_1173_);
v___x_1177_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_1178_ = l_Lean_Expr_isConstOf(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint8_t v___x_1179_; 
lean_dec_ref(v___x_1171_);
v___x_1179_ = l_Lean_Expr_isApp(v___x_1176_);
if (v___x_1179_ == 0)
{
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_arg_1175_);
v___y_1038_ = v_a_1032_;
v___y_1039_ = v_a_1033_;
v___y_1040_ = v_a_1034_;
v___y_1041_ = v_a_1035_;
goto v___jp_1037_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1176_);
v___x_1181_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__4));
v___x_1182_ = l_Lean_Expr_isConstOf(v___x_1180_, v___x_1181_);
lean_dec_ref(v___x_1180_);
if (v___x_1182_ == 0)
{
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_arg_1175_);
v___y_1038_ = v_a_1032_;
v___y_1039_ = v_a_1033_;
v___y_1040_ = v_a_1034_;
v___y_1041_ = v_a_1035_;
goto v___jp_1037_;
}
else
{
lean_object* v_arg_1183_; 
lean_dec_ref(v_e_1031_);
v_arg_1183_ = lean_ctor_get(v___x_1176_, 1);
lean_inc_ref(v_arg_1183_);
lean_dec_ref(v___x_1176_);
v_nExpr_1113_ = v_arg_1183_;
v_vExpr_1114_ = v_arg_1175_;
v___y_1115_ = v_a_1032_;
v___y_1116_ = v_a_1033_;
v___y_1117_ = v_a_1034_;
v___y_1118_ = v_a_1035_;
goto v___jp_1112_;
}
}
}
else
{
lean_object* v_arg_1184_; 
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_e_1031_);
v_arg_1184_ = lean_ctor_get(v___x_1171_, 1);
lean_inc_ref(v_arg_1184_);
lean_dec_ref(v___x_1171_);
v_nExpr_1113_ = v_arg_1175_;
v_vExpr_1114_ = v_arg_1184_;
v___y_1115_ = v_a_1032_;
v___y_1116_ = v_a_1033_;
v___y_1117_ = v_a_1034_;
v___y_1118_ = v_a_1035_;
goto v___jp_1112_;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v_e_1031_);
v_a_1185_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1169_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1169_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
v___jp_1037_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_1043_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1031_, v___x_1042_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1103_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1103_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1103_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
if (lean_obj_tag(v_a_1044_) == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = lean_box(0);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1048_);
v___x_1050_ = v___x_1046_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
else
{
lean_object* v_val_1052_; lean_object* v_fst_1053_; lean_object* v_snd_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1102_; 
lean_del_object(v___x_1046_);
v_val_1052_ = lean_ctor_get(v_a_1044_, 0);
lean_inc(v_val_1052_);
lean_dec_ref_known(v_a_1044_, 1);
v_fst_1053_ = lean_ctor_get(v_val_1052_, 0);
v_snd_1054_ = lean_ctor_get(v_val_1052_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_val_1052_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1056_ = v_val_1052_;
v_isShared_1057_ = v_isSharedCheck_1102_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_snd_1054_);
lean_inc(v_fst_1053_);
lean_dec(v_val_1052_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1102_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = l_Lean_Expr_appArg_x21(v_snd_1054_);
lean_dec(v_snd_1054_);
v___x_1059_ = l_Lean_Meta_whnfD(v___x_1058_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = l_Lean_Meta_getNatValue_x3f(v_a_1060_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v_a_1060_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1085_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1085_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1085_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
if (lean_obj_tag(v_a_1062_) == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
lean_del_object(v___x_1056_);
lean_dec(v_fst_1053_);
v___x_1066_ = lean_box(0);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
else
{
lean_object* v_val_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1084_; 
v_val_1070_ = lean_ctor_get(v_a_1062_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_a_1062_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1072_ = v_a_1062_;
v_isShared_1073_ = v_isSharedCheck_1084_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_val_1070_);
lean_dec(v_a_1062_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1084_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = l_BitVec_ofNat(v_val_1070_, v_fst_1053_);
lean_dec(v_fst_1053_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1074_);
lean_ctor_set(v___x_1056_, 0, v_val_1070_);
v___x_1076_ = v___x_1056_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_val_1070_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1076_);
v___x_1078_ = v___x_1072_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1078_);
v___x_1080_ = v___x_1064_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_del_object(v___x_1056_);
lean_dec(v_fst_1053_);
v_a_1086_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1061_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1061_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_del_object(v___x_1056_);
lean_dec(v_fst_1053_);
v_a_1094_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1059_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1059_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1043_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1043_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
v___jp_1112_:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Meta_getNatValue_x3f(v_nExpr_1113_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec_ref(v_nExpr_1113_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1160_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1160_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1160_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
if (lean_obj_tag(v_a_1120_) == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_dec_ref(v_vExpr_1114_);
v___x_1124_ = lean_box(0);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
else
{
lean_object* v_val_1128_; lean_object* v___x_1129_; 
lean_del_object(v___x_1122_);
v_val_1128_ = lean_ctor_get(v_a_1120_, 0);
lean_inc(v_val_1128_);
lean_dec_ref_known(v_a_1120_, 1);
v___x_1129_ = l_Lean_Meta_getNatValue_x3f(v_vExpr_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec_ref(v_vExpr_1114_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1151_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1151_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1151_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
if (lean_obj_tag(v_a_1130_) == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
lean_dec(v_val_1128_);
v___x_1134_ = lean_box(0);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
else
{
lean_object* v_val_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1150_; 
v_val_1138_ = lean_ctor_get(v_a_1130_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_a_1130_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1140_ = v_a_1130_;
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_val_1138_);
lean_dec(v_a_1130_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1142_ = l_BitVec_ofNat(v_val_1128_, v_val_1138_);
lean_dec(v_val_1138_);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v_val_1128_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1145_);
v___x_1147_ = v___x_1132_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_val_1128_);
v_a_1152_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1129_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1129_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v_vExpr_1114_);
v_a_1161_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1119_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1119_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f___boxed(lean_object* v_e_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Meta_getBitVecValue_x3f(v_e_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
return v_res_1199_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__0(void){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1200_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__1(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__0, &l_Lean_Meta_getLitValueModulus_x3f___closed__0_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__0);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__2(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_cstr_to_nat("4294967296");
v___x_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLitValueModulus_x3f(lean_object* v_00_u03b1_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03b1_1233_, v_a_1235_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = l_Lean_Expr_cleanupAnnotations(v_a_1255_);
lean_dec(v_a_1255_);
v___x_1257_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_1258_ = l_Lean_Expr_isConstOf(v___x_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_1260_ = l_Lean_Expr_isConstOf(v___x_1256_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_1262_ = l_Lean_Expr_isConstOf(v___x_1256_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_1264_ = l_Lean_Expr_isConstOf(v___x_1256_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_1266_ = l_Lean_Expr_isConstOf(v___x_1256_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_1268_ = l_Lean_Expr_isConstOf(v___x_1256_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_1270_ = l_Lean_Expr_isConstOf(v___x_1256_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_1272_ = l_Lean_Expr_isConstOf(v___x_1256_, v___x_1271_);
if (v___x_1272_ == 0)
{
uint8_t v___x_1273_; 
v___x_1273_ = l_Lean_Expr_isApp(v___x_1256_);
if (v___x_1273_ == 0)
{
lean_dec_ref(v___x_1256_);
goto v___jp_1251_;
}
else
{
lean_object* v_arg_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_arg_1274_ = lean_ctor_get(v___x_1256_, 1);
lean_inc_ref(v_arg_1274_);
v___x_1275_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1256_);
lean_dec_ref(v___x_1256_);
v___x_1276_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_1277_ = l_Lean_Expr_isConstOf(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_1279_ = l_Lean_Expr_isConstOf(v___x_1275_, v___x_1278_);
lean_dec_ref(v___x_1275_);
if (v___x_1279_ == 0)
{
lean_dec_ref(v_arg_1274_);
goto v___jp_1251_;
}
else
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_Meta_getNatValue_x3f(v_arg_1274_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
lean_dec_ref(v_arg_1274_);
return v___x_1280_;
}
}
else
{
lean_object* v___x_1281_; 
lean_dec_ref(v___x_1275_);
v___x_1281_ = l_Lean_Meta_getNatValue_x3f(v_arg_1274_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
lean_dec_ref(v_arg_1274_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1303_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1303_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1303_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
if (lean_obj_tag(v_a_1282_) == 1)
{
lean_object* v_val_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1298_; 
v_val_1286_ = lean_ctor_get(v_a_1282_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_a_1282_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1288_ = v_a_1282_;
v_isShared_1289_ = v_isSharedCheck_1298_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_val_1286_);
lean_dec(v_a_1282_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1298_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_unsigned_to_nat(2u);
v___x_1291_ = lean_nat_pow(v___x_1290_, v_val_1286_);
lean_dec(v_val_1286_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1291_);
v___x_1293_ = v___x_1288_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1295_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1293_);
v___x_1295_ = v___x_1284_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
lean_dec(v_a_1282_);
v___x_1299_ = lean_box(0);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1299_);
v___x_1301_ = v___x_1284_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
return v___x_1281_;
}
}
}
}
else
{
lean_dec_ref(v___x_1256_);
goto v___jp_1248_;
}
}
else
{
lean_dec_ref(v___x_1256_);
goto v___jp_1245_;
}
}
else
{
lean_dec_ref(v___x_1256_);
goto v___jp_1242_;
}
}
else
{
lean_dec_ref(v___x_1256_);
goto v___jp_1239_;
}
}
else
{
lean_dec_ref(v___x_1256_);
goto v___jp_1248_;
}
}
else
{
lean_dec_ref(v___x_1256_);
goto v___jp_1245_;
}
}
else
{
lean_dec_ref(v___x_1256_);
goto v___jp_1242_;
}
}
else
{
lean_dec_ref(v___x_1256_);
goto v___jp_1239_;
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
v_a_1304_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1254_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1254_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
v___jp_1239_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__1, &l_Lean_Meta_getLitValueModulus_x3f___closed__1_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__1);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
v___jp_1242_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__2, &l_Lean_Meta_getLitValueModulus_x3f___closed__2_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__2);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
v___jp_1245_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__3));
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
v___jp_1248_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__4));
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
v___jp_1251_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_box(0);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLitValueModulus_x3f___boxed(lean_object* v_00_u03b1_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Meta_getLitValueModulus_x3f(v_00_u03b1_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object* v_e_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_1326_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1319_, v___x_1325_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1349_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1349_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1349_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
if (lean_obj_tag(v_a_1327_) == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = lean_box(0);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1331_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
else
{
lean_object* v_val_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1348_; 
v_val_1335_ = lean_ctor_get(v_a_1327_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_a_1327_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1337_ = v_a_1327_;
v_isShared_1338_ = v_isSharedCheck_1348_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_val_1335_);
lean_dec(v_a_1327_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1348_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_fst_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v_fst_1339_ = lean_ctor_get(v_val_1335_, 0);
lean_inc(v_fst_1339_);
lean_dec(v_val_1335_);
v___x_1340_ = lean_uint8_of_nat(v_fst_1339_);
lean_dec(v_fst_1339_);
v___x_1341_ = lean_box(v___x_1340_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1341_);
v___x_1343_ = v___x_1337_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1345_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1343_);
v___x_1345_ = v___x_1329_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
v_a_1350_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1326_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1326_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f___boxed(lean_object* v_e_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Meta_getUInt8Value_x3f(v_e_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object* v_e_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_1372_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1365_, v___x_1371_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1395_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1395_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1395_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
if (lean_obj_tag(v_a_1373_) == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = lean_box(0);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1377_);
v___x_1379_ = v___x_1375_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
else
{
lean_object* v_val_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1394_; 
v_val_1381_ = lean_ctor_get(v_a_1373_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_a_1373_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1383_ = v_a_1373_;
v_isShared_1384_ = v_isSharedCheck_1394_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_val_1381_);
lean_dec(v_a_1373_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1394_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v_fst_1385_; uint16_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v_fst_1385_ = lean_ctor_get(v_val_1381_, 0);
lean_inc(v_fst_1385_);
lean_dec(v_val_1381_);
v___x_1386_ = lean_uint16_of_nat(v_fst_1385_);
lean_dec(v_fst_1385_);
v___x_1387_ = lean_box(v___x_1386_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1387_);
v___x_1389_ = v___x_1383_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1389_);
v___x_1391_ = v___x_1375_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
v_a_1396_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1372_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1372_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f___boxed(lean_object* v_e_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Meta_getUInt16Value_x3f(v_e_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object* v_e_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_1418_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1411_, v___x_1417_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1441_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1441_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1441_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
if (lean_obj_tag(v_a_1419_) == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_box(0);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1423_);
v___x_1425_ = v___x_1421_;
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
else
{
lean_object* v_val_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1440_; 
v_val_1427_ = lean_ctor_get(v_a_1419_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_a_1419_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1429_ = v_a_1419_;
v_isShared_1430_ = v_isSharedCheck_1440_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_val_1427_);
lean_dec(v_a_1419_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1440_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_fst_1431_; uint32_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v_fst_1431_ = lean_ctor_get(v_val_1427_, 0);
lean_inc(v_fst_1431_);
lean_dec(v_val_1427_);
v___x_1432_ = lean_uint32_of_nat(v_fst_1431_);
lean_dec(v_fst_1431_);
v___x_1433_ = lean_box_uint32(v___x_1432_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1433_);
v___x_1435_ = v___x_1429_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1437_; 
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1435_);
v___x_1437_ = v___x_1421_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_a_1442_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1418_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1418_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f___boxed(lean_object* v_e_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_Meta_getUInt32Value_x3f(v_e_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object* v_e_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_1464_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1457_, v___x_1463_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1487_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1487_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1487_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
if (lean_obj_tag(v_a_1465_) == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1469_ = lean_box(0);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1469_);
v___x_1471_ = v___x_1467_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
else
{
lean_object* v_val_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1486_; 
v_val_1473_ = lean_ctor_get(v_a_1465_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_a_1465_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1475_ = v_a_1465_;
v_isShared_1476_ = v_isSharedCheck_1486_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_val_1473_);
lean_dec(v_a_1465_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1486_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_fst_1477_; uint64_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v_fst_1477_ = lean_ctor_get(v_val_1473_, 0);
lean_inc(v_fst_1477_);
lean_dec(v_val_1473_);
v___x_1478_ = lean_uint64_of_nat(v_fst_1477_);
lean_dec(v_fst_1477_);
v___x_1479_ = lean_box_uint64(v___x_1478_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1479_);
v___x_1481_ = v___x_1475_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1481_);
v___x_1483_ = v___x_1467_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
v_a_1488_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1464_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1464_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f___boxed(lean_object* v_e_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Meta_getUInt64Value_x3f(v_e_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(lean_object* v_e_1503_, lean_object* v_typeDeclName_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___x_1546_; 
lean_inc_ref(v_e_1503_);
v___x_1546_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1503_, v_a_1506_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1548_ = l_Lean_Expr_cleanupAnnotations(v_a_1547_);
lean_dec(v_a_1547_);
v___x_1549_ = l_Lean_Expr_isApp(v___x_1548_);
if (v___x_1549_ == 0)
{
lean_dec_ref(v___x_1548_);
v___y_1511_ = v_a_1505_;
v___y_1512_ = v_a_1506_;
v___y_1513_ = v_a_1507_;
v___y_1514_ = v_a_1508_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1548_);
v___x_1551_ = l_Lean_Expr_isApp(v___x_1550_);
if (v___x_1551_ == 0)
{
lean_dec_ref(v___x_1550_);
lean_dec_ref(v___x_1548_);
v___y_1511_ = v_a_1505_;
v___y_1512_ = v_a_1506_;
v___y_1513_ = v_a_1507_;
v___y_1514_ = v_a_1508_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1550_);
lean_dec_ref(v___x_1550_);
v___x_1553_ = l_Lean_Expr_isApp(v___x_1552_);
if (v___x_1553_ == 0)
{
lean_dec_ref(v___x_1552_);
lean_dec_ref(v___x_1548_);
v___y_1511_ = v_a_1505_;
v___y_1512_ = v_a_1506_;
v___y_1513_ = v_a_1507_;
v___y_1514_ = v_a_1508_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1552_);
lean_dec_ref(v___x_1552_);
v___x_1555_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1556_ = l_Lean_Expr_isConstOf(v___x_1554_, v___x_1555_);
lean_dec_ref(v___x_1554_);
if (v___x_1556_ == 0)
{
lean_dec_ref(v___x_1548_);
v___y_1511_ = v_a_1505_;
v___y_1512_ = v_a_1506_;
v___y_1513_ = v_a_1507_;
v___y_1514_ = v_a_1508_;
goto v___jp_1510_;
}
else
{
lean_object* v_arg_1557_; lean_object* v___x_1558_; 
lean_dec_ref(v_e_1503_);
v_arg_1557_ = lean_ctor_get(v___x_1548_, 1);
lean_inc_ref(v_arg_1557_);
lean_dec_ref(v___x_1548_);
v___x_1558_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_1557_, v_typeDeclName_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1581_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1581_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1581_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
if (lean_obj_tag(v_a_1559_) == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_box(0);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1563_);
v___x_1565_ = v___x_1561_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
else
{
lean_object* v_val_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1580_; 
v_val_1567_ = lean_ctor_get(v_a_1559_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_a_1559_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1569_ = v_a_1559_;
v_isShared_1570_ = v_isSharedCheck_1580_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_val_1567_);
lean_dec(v_a_1559_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1580_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v_fst_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
v_fst_1571_ = lean_ctor_get(v_val_1567_, 0);
lean_inc(v_fst_1571_);
lean_dec(v_val_1567_);
v___x_1572_ = lean_nat_to_int(v_fst_1571_);
v___x_1573_ = lean_int_neg(v___x_1572_);
lean_dec(v___x_1572_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1573_);
v___x_1575_ = v___x_1569_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1577_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1575_);
v___x_1577_ = v___x_1561_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_a_1582_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1558_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1558_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
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
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v_e_1503_);
v_a_1590_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1546_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1546_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
v___jp_1510_:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1503_, v_typeDeclName_1504_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1537_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1537_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1537_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
if (lean_obj_tag(v_a_1516_) == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_box(0);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1520_);
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
else
{
lean_object* v_val_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1536_; 
v_val_1524_ = lean_ctor_get(v_a_1516_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_a_1516_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1526_ = v_a_1516_;
v_isShared_1527_ = v_isSharedCheck_1536_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_val_1524_);
lean_dec(v_a_1516_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1536_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_fst_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v_fst_1528_ = lean_ctor_get(v_val_1524_, 0);
lean_inc(v_fst_1528_);
lean_dec(v_val_1524_);
v___x_1529_ = lean_nat_to_int(v_fst_1528_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1529_);
v___x_1531_ = v___x_1526_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1531_);
v___x_1533_ = v___x_1518_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_a_1538_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1515_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1515_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f___boxed(lean_object* v_e_1598_, lean_object* v_typeDeclName_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1598_, v_typeDeclName_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_typeDeclName_1599_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt8Value_x3f(lean_object* v_e_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_1613_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1606_, v___x_1612_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1635_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1635_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1635_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
if (lean_obj_tag(v_a_1614_) == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1618_ = lean_box(0);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1618_);
v___x_1620_ = v___x_1616_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
else
{
lean_object* v_val_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1634_; 
v_val_1622_ = lean_ctor_get(v_a_1614_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_a_1614_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1624_ = v_a_1614_;
v_isShared_1625_ = v_isSharedCheck_1634_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_val_1622_);
lean_dec(v_a_1614_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1634_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
uint8_t v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1626_ = lean_int8_of_int(v_val_1622_);
lean_dec(v_val_1622_);
v___x_1627_ = lean_box(v___x_1626_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1627_);
v___x_1629_ = v___x_1624_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1631_; 
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1629_);
v___x_1631_ = v___x_1616_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
v_a_1636_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1613_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1613_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt8Value_x3f___boxed(lean_object* v_e_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Meta_getInt8Value_x3f(v_e_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt16Value_x3f(lean_object* v_e_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_1658_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1651_, v___x_1657_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1680_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1680_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1680_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
if (lean_obj_tag(v_a_1659_) == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = lean_box(0);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1663_);
v___x_1665_ = v___x_1661_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
else
{
lean_object* v_val_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1679_; 
v_val_1667_ = lean_ctor_get(v_a_1659_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_a_1659_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1669_ = v_a_1659_;
v_isShared_1670_ = v_isSharedCheck_1679_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_val_1667_);
lean_dec(v_a_1659_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1679_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
uint16_t v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1671_ = lean_int16_of_int(v_val_1667_);
lean_dec(v_val_1667_);
v___x_1672_ = lean_box(v___x_1671_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___x_1672_);
v___x_1674_ = v___x_1669_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1676_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1674_);
v___x_1676_ = v___x_1661_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
v_a_1681_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1658_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1658_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt16Value_x3f___boxed(lean_object* v_e_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Meta_getInt16Value_x3f(v_e_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt32Value_x3f(lean_object* v_e_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_1703_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1696_, v___x_1702_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1725_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1725_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1725_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
if (lean_obj_tag(v_a_1704_) == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1708_ = lean_box(0);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1708_);
v___x_1710_ = v___x_1706_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
else
{
lean_object* v_val_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1724_; 
v_val_1712_ = lean_ctor_get(v_a_1704_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_a_1704_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1714_ = v_a_1704_;
v_isShared_1715_ = v_isSharedCheck_1724_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_val_1712_);
lean_dec(v_a_1704_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1724_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
uint32_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1716_ = lean_int32_of_int(v_val_1712_);
lean_dec(v_val_1712_);
v___x_1717_ = lean_box_uint32(v___x_1716_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1717_);
v___x_1719_ = v___x_1714_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1721_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1719_);
v___x_1721_ = v___x_1706_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
v_a_1726_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1703_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1703_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt32Value_x3f___boxed(lean_object* v_e_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Meta_getInt32Value_x3f(v_e_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt64Value_x3f(lean_object* v_e_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_1748_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getSignedOfNatValue_x3f(v_e_1741_, v___x_1747_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1770_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1770_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1770_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
if (lean_obj_tag(v_a_1749_) == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = lean_box(0);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1753_);
v___x_1755_ = v___x_1751_;
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
else
{
lean_object* v_val_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1769_; 
v_val_1757_ = lean_ctor_get(v_a_1749_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_a_1749_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1759_ = v_a_1749_;
v_isShared_1760_ = v_isSharedCheck_1769_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_val_1757_);
lean_dec(v_a_1749_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1769_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
uint64_t v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1761_ = lean_int64_of_int(v_val_1757_);
lean_dec(v_val_1757_);
v___x_1762_ = lean_box_uint64(v___x_1761_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1762_);
v___x_1764_ = v___x_1759_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1764_);
v___x_1766_ = v___x_1751_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1748_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1748_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInt64Value_x3f___boxed(lean_object* v_e_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Meta_getInt64Value_x3f(v_e_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(lean_object* v_e_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___x_1833_; 
lean_inc_ref(v_e_1789_);
v___x_1833_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1789_, v_a_1791_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = l_Lean_Expr_cleanupAnnotations(v_a_1834_);
lean_dec(v_a_1834_);
v___x_1836_ = l_Lean_Expr_isApp(v___x_1835_);
if (v___x_1836_ == 0)
{
lean_dec_ref(v___x_1835_);
v___y_1796_ = v_a_1790_;
v___y_1797_ = v_a_1791_;
v___y_1798_ = v_a_1792_;
v___y_1799_ = v_a_1793_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1835_);
v___x_1838_ = l_Lean_Expr_isApp(v___x_1837_);
if (v___x_1838_ == 0)
{
lean_dec_ref(v___x_1837_);
lean_dec_ref(v___x_1835_);
v___y_1796_ = v_a_1790_;
v___y_1797_ = v_a_1791_;
v___y_1798_ = v_a_1792_;
v___y_1799_ = v_a_1793_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1837_);
v___x_1840_ = l_Lean_Expr_isApp(v___x_1839_);
if (v___x_1840_ == 0)
{
lean_dec_ref(v___x_1839_);
lean_dec_ref(v___x_1837_);
lean_dec_ref(v___x_1835_);
v___y_1796_ = v_a_1790_;
v___y_1797_ = v_a_1791_;
v___y_1798_ = v_a_1792_;
v___y_1799_ = v_a_1793_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1839_);
v___x_1842_ = l_Lean_Expr_isApp(v___x_1841_);
if (v___x_1842_ == 0)
{
lean_dec_ref(v___x_1841_);
lean_dec_ref(v___x_1839_);
lean_dec_ref(v___x_1837_);
lean_dec_ref(v___x_1835_);
v___y_1796_ = v_a_1790_;
v___y_1797_ = v_a_1791_;
v___y_1798_ = v_a_1792_;
v___y_1799_ = v_a_1793_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1841_);
lean_dec_ref(v___x_1841_);
v___x_1844_ = l_Lean_Expr_isApp(v___x_1843_);
if (v___x_1844_ == 0)
{
lean_dec_ref(v___x_1843_);
lean_dec_ref(v___x_1839_);
lean_dec_ref(v___x_1837_);
lean_dec_ref(v___x_1835_);
v___y_1796_ = v_a_1790_;
v___y_1797_ = v_a_1791_;
v___y_1798_ = v_a_1792_;
v___y_1799_ = v_a_1793_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1843_);
v___x_1846_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_1847_ = l_Lean_Expr_isConstOf(v___x_1845_, v___x_1846_);
lean_dec_ref(v___x_1845_);
if (v___x_1847_ == 0)
{
lean_dec_ref(v___x_1843_);
lean_dec_ref(v___x_1839_);
lean_dec_ref(v___x_1837_);
lean_dec_ref(v___x_1835_);
v___y_1796_ = v_a_1790_;
v___y_1797_ = v_a_1791_;
v___y_1798_ = v_a_1792_;
v___y_1799_ = v_a_1793_;
goto v___jp_1795_;
}
else
{
lean_object* v_arg_1848_; lean_object* v_arg_1849_; lean_object* v_arg_1850_; lean_object* v_arg_1851_; lean_object* v___x_1852_; 
lean_dec_ref(v_e_1789_);
v_arg_1848_ = lean_ctor_get(v___x_1835_, 1);
lean_inc_ref(v_arg_1848_);
lean_dec_ref(v___x_1835_);
v_arg_1849_ = lean_ctor_get(v___x_1837_, 1);
lean_inc_ref(v_arg_1849_);
lean_dec_ref(v___x_1837_);
v_arg_1850_ = lean_ctor_get(v___x_1839_, 1);
lean_inc_ref(v_arg_1850_);
lean_dec_ref(v___x_1839_);
v_arg_1851_ = lean_ctor_get(v___x_1843_, 1);
lean_inc_ref(v_arg_1851_);
lean_dec_ref(v___x_1843_);
v___x_1852_ = l_Lean_Meta_whnfD(v_arg_1851_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1920_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1920_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1920_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1858_ = l_Lean_Expr_isConstOf(v_a_1853_, v___x_1857_);
lean_dec(v_a_1853_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
lean_dec_ref(v_arg_1850_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1848_);
v___x_1859_ = lean_box(0);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1859_);
v___x_1861_ = v___x_1855_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
else
{
lean_object* v___x_1863_; 
v___x_1863_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_1849_);
lean_dec_ref(v_arg_1849_);
if (lean_obj_tag(v___x_1863_) == 1)
{
lean_object* v_val_1864_; lean_object* v___x_1865_; 
lean_del_object(v___x_1855_);
v_val_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v___x_1865_ = l_Lean_Meta_getNatValue_x3f(v_arg_1850_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
lean_dec_ref(v_arg_1850_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1907_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1907_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1907_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
if (lean_obj_tag(v_a_1866_) == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_dec(v_val_1864_);
lean_dec_ref(v_arg_1848_);
v___x_1870_ = lean_box(0);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1870_);
v___x_1872_ = v___x_1868_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
else
{
lean_object* v_val_1874_; lean_object* v___x_1875_; 
lean_del_object(v___x_1868_);
v_val_1874_ = lean_ctor_get(v_a_1866_, 0);
lean_inc(v_val_1874_);
lean_dec_ref_known(v_a_1866_, 1);
v___x_1875_ = l_Lean_Meta_getNatValue_x3f(v_arg_1848_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
lean_dec_ref(v_arg_1848_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1898_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1898_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1898_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
if (lean_obj_tag(v_a_1876_) == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
lean_dec(v_val_1874_);
lean_dec(v_val_1864_);
v___x_1880_ = lean_box(0);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1880_);
v___x_1882_ = v___x_1878_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
else
{
lean_object* v_val_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1897_; 
v_val_1884_ = lean_ctor_get(v_a_1876_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_a_1876_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1886_ = v_a_1876_;
v_isShared_1887_ = v_isSharedCheck_1897_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_val_1884_);
lean_dec(v_a_1876_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1897_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
uint8_t v___x_1888_; double v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1888_ = lean_unbox(v_val_1864_);
lean_dec(v_val_1864_);
v___x_1889_ = l_Float_ofScientific(v_val_1874_, v___x_1888_, v_val_1884_);
v___x_1890_ = lean_box_float(v___x_1889_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1890_);
v___x_1892_ = v___x_1886_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1894_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1892_);
v___x_1894_ = v___x_1878_;
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
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v_val_1874_);
lean_dec(v_val_1864_);
v_a_1899_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1875_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1875_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec(v_val_1864_);
lean_dec_ref(v_arg_1848_);
v_a_1908_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1865_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1865_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
lean_dec(v___x_1863_);
lean_dec_ref(v_arg_1850_);
lean_dec_ref(v_arg_1848_);
v___x_1916_ = lean_box(0);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1916_);
v___x_1918_ = v___x_1855_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v_arg_1850_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1848_);
v_a_1921_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1852_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1852_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
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
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_e_1789_);
v_a_1929_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1833_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1833_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
v___jp_1795_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1801_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1789_, v___x_1800_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1824_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1824_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1824_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
if (lean_obj_tag(v_a_1802_) == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1806_ = lean_box(0);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1806_);
v___x_1808_ = v___x_1804_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
else
{
lean_object* v_val_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1823_; 
v_val_1810_ = lean_ctor_get(v_a_1802_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_a_1802_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1812_ = v_a_1802_;
v_isShared_1813_ = v_isSharedCheck_1823_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_val_1810_);
lean_dec(v_a_1802_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1823_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_fst_1814_; double v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v_fst_1814_ = lean_ctor_get(v_val_1810_, 0);
lean_inc(v_fst_1814_);
lean_dec(v_val_1810_);
v___x_1815_ = lean_float_of_nat(v_fst_1814_);
v___x_1816_ = lean_box_float(v___x_1815_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1816_);
v___x_1818_ = v___x_1812_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1820_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1818_);
v___x_1820_ = v___x_1804_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1801_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1801_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___boxed(lean_object* v_e_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f(lean_object* v_e_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1953_; 
lean_inc_ref(v_e_1944_);
v___x_1953_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
if (lean_obj_tag(v_a_1954_) == 1)
{
lean_dec_ref(v_e_1944_);
return v___x_1953_;
}
else
{
lean_object* v___x_1955_; 
lean_dec_ref_known(v___x_1953_, 1);
v___x_1955_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1944_, v_a_1946_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = l_Lean_Expr_cleanupAnnotations(v_a_1956_);
lean_dec(v_a_1956_);
v___x_1958_ = l_Lean_Expr_isApp(v___x_1957_);
if (v___x_1958_ == 0)
{
lean_dec_ref(v___x_1957_);
goto v___jp_1950_;
}
else
{
lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1959_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1957_);
v___x_1960_ = l_Lean_Expr_isApp(v___x_1959_);
if (v___x_1960_ == 0)
{
lean_dec_ref(v___x_1959_);
lean_dec_ref(v___x_1957_);
goto v___jp_1950_;
}
else
{
lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1959_);
lean_dec_ref(v___x_1959_);
v___x_1962_ = l_Lean_Expr_isApp(v___x_1961_);
if (v___x_1962_ == 0)
{
lean_dec_ref(v___x_1961_);
lean_dec_ref(v___x_1957_);
goto v___jp_1950_;
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1963_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1961_);
lean_dec_ref(v___x_1961_);
v___x_1964_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1965_ = l_Lean_Expr_isConstOf(v___x_1963_, v___x_1964_);
lean_dec_ref(v___x_1963_);
if (v___x_1965_ == 0)
{
lean_dec_ref(v___x_1957_);
goto v___jp_1950_;
}
else
{
lean_object* v_arg_1966_; lean_object* v___x_1967_; 
v_arg_1966_ = lean_ctor_get(v___x_1957_, 1);
lean_inc_ref(v_arg_1966_);
lean_dec_ref(v___x_1957_);
v___x_1967_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_arg_1966_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1990_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_1990_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1990_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
if (lean_obj_tag(v_a_1968_) == 1)
{
lean_object* v_val_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1985_; 
v_val_1972_ = lean_ctor_get(v_a_1968_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_a_1968_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1974_ = v_a_1968_;
v_isShared_1975_ = v_isSharedCheck_1985_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_val_1972_);
lean_dec(v_a_1968_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1985_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
double v___x_1976_; double v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1976_ = lean_unbox_float(v_val_1972_);
lean_dec(v_val_1972_);
v___x_1977_ = lean_float_negate(v___x_1976_);
v___x_1978_ = lean_box_float(v___x_1977_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1978_);
v___x_1980_ = v___x_1974_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1982_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1980_);
v___x_1982_ = v___x_1970_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_dec(v_a_1968_);
v___x_1986_ = lean_box(0);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1986_);
v___x_1988_ = v___x_1970_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
return v___x_1967_;
}
}
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
v_a_1991_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1955_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1955_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1944_);
return v___x_1953_;
}
v___jp_1950_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_box(0);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f___boxed(lean_object* v_e_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Meta_getFloatValue_x3f(v_e_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(lean_object* v_e_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___x_2053_; 
lean_inc_ref(v_e_2009_);
v___x_2053_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2009_, v_a_2011_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2055_ = l_Lean_Expr_cleanupAnnotations(v_a_2054_);
lean_dec(v_a_2054_);
v___x_2056_ = l_Lean_Expr_isApp(v___x_2055_);
if (v___x_2056_ == 0)
{
lean_dec_ref(v___x_2055_);
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2055_);
v___x_2058_ = l_Lean_Expr_isApp(v___x_2057_);
if (v___x_2058_ == 0)
{
lean_dec_ref(v___x_2057_);
lean_dec_ref(v___x_2055_);
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2057_);
v___x_2060_ = l_Lean_Expr_isApp(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec_ref(v___x_2059_);
lean_dec_ref(v___x_2057_);
lean_dec_ref(v___x_2055_);
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2059_);
v___x_2062_ = l_Lean_Expr_isApp(v___x_2061_);
if (v___x_2062_ == 0)
{
lean_dec_ref(v___x_2061_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v___x_2057_);
lean_dec_ref(v___x_2055_);
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2061_);
lean_dec_ref(v___x_2061_);
v___x_2064_ = l_Lean_Expr_isApp(v___x_2063_);
if (v___x_2064_ == 0)
{
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v___x_2057_);
lean_dec_ref(v___x_2055_);
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2065_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2063_);
v___x_2066_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_2067_ = l_Lean_Expr_isConstOf(v___x_2065_, v___x_2066_);
lean_dec_ref(v___x_2065_);
if (v___x_2067_ == 0)
{
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v___x_2057_);
lean_dec_ref(v___x_2055_);
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
goto v___jp_2015_;
}
else
{
lean_object* v_arg_2068_; lean_object* v_arg_2069_; lean_object* v_arg_2070_; lean_object* v_arg_2071_; lean_object* v___x_2072_; 
lean_dec_ref(v_e_2009_);
v_arg_2068_ = lean_ctor_get(v___x_2055_, 1);
lean_inc_ref(v_arg_2068_);
lean_dec_ref(v___x_2055_);
v_arg_2069_ = lean_ctor_get(v___x_2057_, 1);
lean_inc_ref(v_arg_2069_);
lean_dec_ref(v___x_2057_);
v_arg_2070_ = lean_ctor_get(v___x_2059_, 1);
lean_inc_ref(v_arg_2070_);
lean_dec_ref(v___x_2059_);
v_arg_2071_ = lean_ctor_get(v___x_2063_, 1);
lean_inc_ref(v_arg_2071_);
lean_dec_ref(v___x_2063_);
v___x_2072_ = l_Lean_Meta_whnfD(v_arg_2071_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2140_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2140_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2140_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_2078_ = l_Lean_Expr_isConstOf(v_a_2073_, v___x_2077_);
lean_dec(v_a_2073_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2068_);
v___x_2079_ = lean_box(0);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2079_);
v___x_2081_ = v___x_2075_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
else
{
lean_object* v___x_2083_; 
v___x_2083_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_2069_);
lean_dec_ref(v_arg_2069_);
if (lean_obj_tag(v___x_2083_) == 1)
{
lean_object* v_val_2084_; lean_object* v___x_2085_; 
lean_del_object(v___x_2075_);
v_val_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_val_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v___x_2085_ = l_Lean_Meta_getNatValue_x3f(v_arg_2070_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
lean_dec_ref(v_arg_2070_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2127_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2127_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2127_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
if (lean_obj_tag(v_a_2086_) == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
lean_dec(v_val_2084_);
lean_dec_ref(v_arg_2068_);
v___x_2090_ = lean_box(0);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2090_);
v___x_2092_ = v___x_2088_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
else
{
lean_object* v_val_2094_; lean_object* v___x_2095_; 
lean_del_object(v___x_2088_);
v_val_2094_ = lean_ctor_get(v_a_2086_, 0);
lean_inc(v_val_2094_);
lean_dec_ref_known(v_a_2086_, 1);
v___x_2095_ = l_Lean_Meta_getNatValue_x3f(v_arg_2068_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
lean_dec_ref(v_arg_2068_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2118_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2118_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2118_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
if (lean_obj_tag(v_a_2096_) == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_dec(v_val_2094_);
lean_dec(v_val_2084_);
v___x_2100_ = lean_box(0);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2100_);
v___x_2102_ = v___x_2098_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
else
{
lean_object* v_val_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2117_; 
v_val_2104_ = lean_ctor_get(v_a_2096_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_a_2096_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2106_ = v_a_2096_;
v_isShared_2107_ = v_isSharedCheck_2117_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_val_2104_);
lean_dec(v_a_2096_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2117_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
uint8_t v___x_2108_; float v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2108_ = lean_unbox(v_val_2084_);
lean_dec(v_val_2084_);
v___x_2109_ = l_Float32_ofScientific(v_val_2094_, v___x_2108_, v_val_2104_);
v___x_2110_ = lean_box_float32(v___x_2109_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2110_);
v___x_2112_ = v___x_2106_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2112_);
v___x_2114_ = v___x_2098_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_val_2094_);
lean_dec(v_val_2084_);
v_a_2119_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2095_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2095_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v_val_2084_);
lean_dec_ref(v_arg_2068_);
v_a_2128_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2085_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2085_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
lean_dec(v___x_2083_);
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2068_);
v___x_2136_ = lean_box(0);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2136_);
v___x_2138_ = v___x_2075_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref(v_arg_2070_);
lean_dec_ref(v_arg_2069_);
lean_dec_ref(v_arg_2068_);
v_a_2141_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2072_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2072_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
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
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec_ref(v_e_2009_);
v_a_2149_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2053_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2053_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
v___jp_2015_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_2021_ = l_Lean_Meta_getOfNatValue_x3f(v_e_2009_, v___x_2020_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2044_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2044_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2044_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
if (lean_obj_tag(v_a_2022_) == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2026_ = lean_box(0);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2026_);
v___x_2028_ = v___x_2024_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
else
{
lean_object* v_val_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2043_; 
v_val_2030_ = lean_ctor_get(v_a_2022_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_a_2022_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2032_ = v_a_2022_;
v_isShared_2033_ = v_isSharedCheck_2043_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_val_2030_);
lean_dec(v_a_2022_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2043_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_fst_2034_; float v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v_fst_2034_ = lean_ctor_get(v_val_2030_, 0);
lean_inc(v_fst_2034_);
lean_dec(v_val_2030_);
v___x_2035_ = lean_float32_of_nat(v_fst_2034_);
v___x_2036_ = lean_box_float32(v___x_2035_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2036_);
v___x_2038_ = v___x_2032_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2038_);
v___x_2040_ = v___x_2024_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
v_a_2045_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2021_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2021_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___boxed(lean_object* v_e_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f(lean_object* v_e_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2173_; 
lean_inc_ref(v_e_2164_);
v___x_2173_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
if (lean_obj_tag(v_a_2174_) == 1)
{
lean_dec_ref(v_e_2164_);
return v___x_2173_;
}
else
{
lean_object* v___x_2175_; 
lean_dec_ref_known(v___x_2173_, 1);
v___x_2175_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2164_, v_a_2166_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = l_Lean_Expr_cleanupAnnotations(v_a_2176_);
lean_dec(v_a_2176_);
v___x_2178_ = l_Lean_Expr_isApp(v___x_2177_);
if (v___x_2178_ == 0)
{
lean_dec_ref(v___x_2177_);
goto v___jp_2170_;
}
else
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2177_);
v___x_2180_ = l_Lean_Expr_isApp(v___x_2179_);
if (v___x_2180_ == 0)
{
lean_dec_ref(v___x_2179_);
lean_dec_ref(v___x_2177_);
goto v___jp_2170_;
}
else
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2179_);
lean_dec_ref(v___x_2179_);
v___x_2182_ = l_Lean_Expr_isApp(v___x_2181_);
if (v___x_2182_ == 0)
{
lean_dec_ref(v___x_2181_);
lean_dec_ref(v___x_2177_);
goto v___jp_2170_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2183_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2181_);
lean_dec_ref(v___x_2181_);
v___x_2184_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_2185_ = l_Lean_Expr_isConstOf(v___x_2183_, v___x_2184_);
lean_dec_ref(v___x_2183_);
if (v___x_2185_ == 0)
{
lean_dec_ref(v___x_2177_);
goto v___jp_2170_;
}
else
{
lean_object* v_arg_2186_; lean_object* v___x_2187_; 
v_arg_2186_ = lean_ctor_get(v___x_2177_, 1);
lean_inc_ref(v_arg_2186_);
lean_dec_ref(v___x_2177_);
v___x_2187_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_arg_2186_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2210_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2210_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2210_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
if (lean_obj_tag(v_a_2188_) == 1)
{
lean_object* v_val_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2205_; 
v_val_2192_ = lean_ctor_get(v_a_2188_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_a_2188_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2194_ = v_a_2188_;
v_isShared_2195_ = v_isSharedCheck_2205_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_val_2192_);
lean_dec(v_a_2188_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2205_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
float v___x_2196_; float v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2196_ = lean_unbox_float32(v_val_2192_);
lean_dec(v_val_2192_);
v___x_2197_ = lean_float32_negate(v___x_2196_);
v___x_2198_ = lean_box_float32(v___x_2197_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2198_);
v___x_2200_ = v___x_2194_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2202_; 
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2200_);
v___x_2202_ = v___x_2190_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2208_; 
lean_dec(v_a_2188_);
v___x_2206_ = lean_box(0);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2206_);
v___x_2208_ = v___x_2190_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
return v___x_2187_;
}
}
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
v_a_2211_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2175_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2175_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2164_);
return v___x_2173_;
}
v___jp_2170_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_box(0);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f___boxed(lean_object* v_e_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_Meta_getFloat32Value_x3f(v_e_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(lean_object* v_e_2226_, lean_object* v___y_2227_){
_start:
{
uint8_t v___x_2229_; 
v___x_2229_ = l_Lean_Expr_hasMVar(v_e_2226_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v_e_2226_);
return v___x_2230_;
}
else
{
lean_object* v___x_2231_; lean_object* v_mctx_2232_; lean_object* v___x_2233_; lean_object* v_fst_2234_; lean_object* v_snd_2235_; lean_object* v___x_2236_; lean_object* v_cache_2237_; lean_object* v_zetaDeltaFVarIds_2238_; lean_object* v_postponed_2239_; lean_object* v_diag_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2249_; 
v___x_2231_ = lean_st_ref_get(v___y_2227_);
v_mctx_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc_ref(v_mctx_2232_);
lean_dec(v___x_2231_);
v___x_2233_ = l_Lean_instantiateMVarsCore(v_mctx_2232_, v_e_2226_);
v_fst_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_fst_2234_);
v_snd_2235_ = lean_ctor_get(v___x_2233_, 1);
lean_inc(v_snd_2235_);
lean_dec_ref(v___x_2233_);
v___x_2236_ = lean_st_ref_take(v___y_2227_);
v_cache_2237_ = lean_ctor_get(v___x_2236_, 1);
v_zetaDeltaFVarIds_2238_ = lean_ctor_get(v___x_2236_, 2);
v_postponed_2239_ = lean_ctor_get(v___x_2236_, 3);
v_diag_2240_ = lean_ctor_get(v___x_2236_, 4);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; 
v_unused_2250_ = lean_ctor_get(v___x_2236_, 0);
lean_dec(v_unused_2250_);
v___x_2242_ = v___x_2236_;
v_isShared_2243_ = v_isSharedCheck_2249_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_diag_2240_);
lean_inc(v_postponed_2239_);
lean_inc(v_zetaDeltaFVarIds_2238_);
lean_inc(v_cache_2237_);
lean_dec(v___x_2236_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2249_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v_snd_2235_);
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_snd_2235_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_cache_2237_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_zetaDeltaFVarIds_2238_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v_postponed_2239_);
lean_ctor_set(v_reuseFailAlloc_2248_, 4, v_diag_2240_);
v___x_2245_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = lean_st_ref_put(v___y_2227_, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_fst_2234_);
return v___x_2247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg___boxed(lean_object* v_e_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2251_, v___y_2252_);
lean_dec(v___y_2252_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(lean_object* v_e_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2255_, v___y_2257_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___boxed(lean_object* v_e_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(v_e_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
return v_res_2268_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__0(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = lean_nat_to_int(v___x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__1(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_unsigned_to_nat(0u);
v___x_2272_ = l_Lean_Level_ofNat(v___x_2271_);
return v___x_2272_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__2(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__1, &l_Lean_Meta_normLitValue___closed__1_once, _init_l_Lean_Meta_normLitValue___closed__1);
v___x_2275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___x_2273_);
return v___x_2275_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__3(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_2277_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_2278_ = l_Lean_Expr_const___override(v___x_2277_, v___x_2276_);
return v___x_2278_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__4(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_box(0);
v___x_2280_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_2281_ = l_Lean_Expr_const___override(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__7(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_box(0);
v___x_2287_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__6));
v___x_2288_ = l_Lean_Expr_const___override(v___x_2287_, v___x_2286_);
return v___x_2288_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__8(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_2290_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_2291_ = l_Lean_Expr_const___override(v___x_2290_, v___x_2289_);
return v___x_2291_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__9(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_box(0);
v___x_2293_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_2294_ = l_Lean_mkConst(v___x_2293_, v___x_2292_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__12(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = lean_box(0);
v___x_2300_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__11));
v___x_2301_ = l_Lean_Expr_const___override(v___x_2300_, v___x_2299_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__15(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2306_ = lean_box(0);
v___x_2307_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__14));
v___x_2308_ = l_Lean_Expr_const___override(v___x_2307_, v___x_2306_);
return v___x_2308_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__16(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = lean_box(0);
v___x_2310_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_2311_ = l_Lean_Expr_const___override(v___x_2310_, v___x_2309_);
return v___x_2311_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__17(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = lean_box(0);
v___x_2313_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_2314_ = l_Lean_mkConst(v___x_2313_, v___x_2312_);
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__18(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2315_ = lean_box(0);
v___x_2316_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_2317_ = l_Lean_mkConst(v___x_2316_, v___x_2315_);
return v___x_2317_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__20(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = lean_box(0);
v___x_2322_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__19));
v___x_2323_ = l_Lean_Expr_const___override(v___x_2322_, v___x_2321_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__21(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_box(0);
v___x_2325_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_2326_ = l_Lean_mkConst(v___x_2325_, v___x_2324_);
return v___x_2326_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__23(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = lean_box(0);
v___x_2331_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__22));
v___x_2332_ = l_Lean_Expr_const___override(v___x_2331_, v___x_2330_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__24(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = lean_box(0);
v___x_2334_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_2335_ = l_Lean_mkConst(v___x_2334_, v___x_2333_);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__26(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2339_ = lean_box(0);
v___x_2340_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__25));
v___x_2341_ = l_Lean_Expr_const___override(v___x_2340_, v___x_2339_);
return v___x_2341_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__27(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2342_ = lean_box(0);
v___x_2343_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_2344_ = l_Lean_mkConst(v___x_2343_, v___x_2342_);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__29(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2348_ = lean_box(0);
v___x_2349_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__28));
v___x_2350_ = l_Lean_Expr_const___override(v___x_2349_, v___x_2348_);
return v___x_2350_;
}
}
static uint8_t _init_l_Lean_Meta_normLitValue___closed__30(void){
_start:
{
lean_object* v___x_2351_; uint8_t v___x_2352_; 
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2352_ = lean_int8_of_nat(v___x_2351_);
return v___x_2352_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__31(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = lean_box(0);
v___x_2354_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_2355_ = l_Lean_Expr_const___override(v___x_2354_, v___x_2353_);
return v___x_2355_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__34(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = lean_box(0);
v___x_2361_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__33));
v___x_2362_ = l_Lean_Expr_const___override(v___x_2361_, v___x_2360_);
return v___x_2362_;
}
}
static uint16_t _init_l_Lean_Meta_normLitValue___closed__35(void){
_start:
{
lean_object* v___x_2363_; uint16_t v___x_2364_; 
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = lean_int16_of_nat(v___x_2363_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__36(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_2367_ = l_Lean_Expr_const___override(v___x_2366_, v___x_2365_);
return v___x_2367_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__38(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = lean_box(0);
v___x_2372_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__37));
v___x_2373_ = l_Lean_Expr_const___override(v___x_2372_, v___x_2371_);
return v___x_2373_;
}
}
static uint32_t _init_l_Lean_Meta_normLitValue___closed__39(void){
_start:
{
lean_object* v___x_2374_; uint32_t v___x_2375_; 
v___x_2374_ = lean_unsigned_to_nat(0u);
v___x_2375_ = lean_int32_of_nat(v___x_2374_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__40(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = lean_box(0);
v___x_2377_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_2378_ = l_Lean_Expr_const___override(v___x_2377_, v___x_2376_);
return v___x_2378_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__42(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = lean_box(0);
v___x_2383_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__41));
v___x_2384_ = l_Lean_Expr_const___override(v___x_2383_, v___x_2382_);
return v___x_2384_;
}
}
static uint64_t _init_l_Lean_Meta_normLitValue___closed__43(void){
_start:
{
lean_object* v___x_2385_; uint64_t v___x_2386_; 
v___x_2385_ = lean_unsigned_to_nat(0u);
v___x_2386_ = lean_int64_of_nat(v___x_2385_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__44(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = lean_box(0);
v___x_2388_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_2389_ = l_Lean_Expr_const___override(v___x_2388_, v___x_2387_);
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__46(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2393_ = lean_box(0);
v___x_2394_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__45));
v___x_2395_ = l_Lean_Expr_const___override(v___x_2394_, v___x_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue(lean_object* v_e_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v_a_2403_; lean_object* v___x_2404_; 
v___x_2402_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2396_, v_a_2398_);
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2402_);
v___x_2404_ = l_Lean_Meta_getNatValue_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2787_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2787_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2787_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
if (lean_obj_tag(v_a_2405_) == 1)
{
lean_object* v_val_2409_; lean_object* v___x_2410_; lean_object* v___x_2412_; 
lean_dec(v_a_2403_);
v_val_2409_ = lean_ctor_get(v_a_2405_, 0);
lean_inc(v_val_2409_);
lean_dec_ref_known(v_a_2405_, 1);
v___x_2410_ = l_Lean_mkNatLit(v_val_2409_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___x_2410_);
v___x_2412_ = v___x_2407_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
else
{
lean_object* v___x_2414_; 
lean_del_object(v___x_2407_);
lean_dec(v_a_2405_);
lean_inc(v_a_2403_);
v___x_2414_ = l_Lean_Meta_getIntValue_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2778_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2778_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2778_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
if (lean_obj_tag(v_a_2415_) == 1)
{
lean_object* v_val_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
lean_dec(v_a_2403_);
v_val_2419_ = lean_ctor_get(v_a_2415_, 0);
lean_inc(v_val_2419_);
lean_dec_ref_known(v_a_2415_, 1);
v___x_2420_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_2421_ = lean_int_dec_le(v___x_2420_, v_val_2419_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
v___x_2422_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2423_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__4, &l_Lean_Meta_normLitValue___closed__4_once, _init_l_Lean_Meta_normLitValue___closed__4);
v___x_2424_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__7, &l_Lean_Meta_normLitValue___closed__7_once, _init_l_Lean_Meta_normLitValue___closed__7);
v___x_2425_ = lean_int_neg(v_val_2419_);
lean_dec(v_val_2419_);
v___x_2426_ = l_Int_toNat(v___x_2425_);
lean_dec(v___x_2425_);
v___x_2427_ = l_Lean_instToExprInt_mkNat(v___x_2426_);
v___x_2428_ = l_Lean_mkApp3(v___x_2422_, v___x_2423_, v___x_2424_, v___x_2427_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2428_);
v___x_2430_ = v___x_2417_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2432_ = l_Int_toNat(v_val_2419_);
lean_dec(v_val_2419_);
v___x_2433_ = l_Lean_instToExprInt_mkNat(v___x_2432_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2433_);
v___x_2435_ = v___x_2417_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
else
{
lean_object* v___x_2437_; 
lean_del_object(v___x_2417_);
lean_dec(v_a_2415_);
lean_inc(v_a_2403_);
v___x_2437_ = l_Lean_Meta_getFinValue_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2769_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2769_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2769_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
if (lean_obj_tag(v_a_2438_) == 1)
{
lean_object* v_val_2442_; lean_object* v_fst_2443_; lean_object* v_snd_2444_; lean_object* v_r_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2459_; 
lean_dec(v_a_2403_);
v_val_2442_ = lean_ctor_get(v_a_2438_, 0);
lean_inc(v_val_2442_);
lean_dec_ref_known(v_a_2438_, 1);
v_fst_2443_ = lean_ctor_get(v_val_2442_, 0);
lean_inc_n(v_fst_2443_, 2);
v_snd_2444_ = lean_ctor_get(v_val_2442_, 1);
lean_inc(v_snd_2444_);
lean_dec(v_val_2442_);
v_r_2445_ = l_Lean_mkRawNatLit(v_snd_2444_);
v___x_2446_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2447_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__9, &l_Lean_Meta_normLitValue___closed__9_once, _init_l_Lean_Meta_normLitValue___closed__9);
v___x_2448_ = l_Lean_mkNatLit(v_fst_2443_);
lean_inc_ref(v___x_2448_);
v___x_2449_ = l_Lean_Expr_app___override(v___x_2447_, v___x_2448_);
v___x_2450_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__12, &l_Lean_Meta_normLitValue___closed__12_once, _init_l_Lean_Meta_normLitValue___closed__12);
v___x_2451_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__15, &l_Lean_Meta_normLitValue___closed__15_once, _init_l_Lean_Meta_normLitValue___closed__15);
v___x_2452_ = lean_unsigned_to_nat(1u);
v___x_2453_ = lean_nat_sub(v_fst_2443_, v___x_2452_);
lean_dec(v_fst_2443_);
v___x_2454_ = l_Lean_mkNatLit(v___x_2453_);
v___x_2455_ = l_Lean_Expr_app___override(v___x_2451_, v___x_2454_);
lean_inc_ref(v_r_2445_);
v___x_2456_ = l_Lean_mkApp3(v___x_2450_, v___x_2448_, v___x_2455_, v_r_2445_);
v___x_2457_ = l_Lean_mkApp3(v___x_2446_, v___x_2449_, v_r_2445_, v___x_2456_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2457_);
v___x_2459_ = v___x_2440_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
else
{
lean_object* v___x_2461_; 
lean_del_object(v___x_2440_);
lean_dec(v_a_2438_);
lean_inc(v_a_2403_);
v___x_2461_ = l_Lean_Meta_getBitVecValue_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2760_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2760_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2760_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
if (lean_obj_tag(v_a_2462_) == 1)
{
lean_object* v_val_2466_; lean_object* v_fst_2467_; lean_object* v_snd_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_a_2403_);
v_val_2466_ = lean_ctor_get(v_a_2462_, 0);
lean_inc(v_val_2466_);
lean_dec_ref_known(v_a_2462_, 1);
v_fst_2467_ = lean_ctor_get(v_val_2466_, 0);
lean_inc(v_fst_2467_);
v_snd_2468_ = lean_ctor_get(v_val_2466_, 1);
lean_inc(v_snd_2468_);
lean_dec(v_val_2466_);
v___x_2469_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__16, &l_Lean_Meta_normLitValue___closed__16_once, _init_l_Lean_Meta_normLitValue___closed__16);
v___x_2470_ = l_Lean_mkNatLit(v_fst_2467_);
v___x_2471_ = l_Lean_mkNatLit(v_snd_2468_);
v___x_2472_ = l_Lean_mkAppB(v___x_2469_, v___x_2470_, v___x_2471_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2472_);
v___x_2474_ = v___x_2464_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
else
{
lean_object* v___x_2476_; 
lean_dec(v_a_2462_);
lean_inc(v_a_2403_);
v___x_2476_ = l_Lean_Meta_getStringValue_x3f(v_a_2403_);
if (lean_obj_tag(v___x_2476_) == 1)
{
lean_object* v_val_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
lean_dec(v_a_2403_);
v_val_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_val_2477_);
lean_dec_ref_known(v___x_2476_, 1);
v___x_2478_ = l_Lean_mkStrLit(v_val_2477_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2478_);
v___x_2480_ = v___x_2464_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
else
{
lean_object* v___x_2482_; 
lean_dec(v___x_2476_);
lean_del_object(v___x_2464_);
lean_inc(v_a_2403_);
v___x_2482_ = l_Lean_Meta_getCharValue_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2751_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2751_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2751_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
if (lean_obj_tag(v_a_2483_) == 1)
{
lean_object* v_val_2487_; lean_object* v___x_2488_; uint32_t v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2494_; 
lean_dec(v_a_2403_);
v_val_2487_ = lean_ctor_get(v_a_2483_, 0);
lean_inc(v_val_2487_);
lean_dec_ref_known(v_a_2483_, 1);
v___x_2488_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__17, &l_Lean_Meta_normLitValue___closed__17_once, _init_l_Lean_Meta_normLitValue___closed__17);
v___x_2489_ = lean_unbox_uint32(v_val_2487_);
lean_dec(v_val_2487_);
v___x_2490_ = lean_uint32_to_nat(v___x_2489_);
v___x_2491_ = l_Lean_mkRawNatLit(v___x_2490_);
v___x_2492_ = l_Lean_Expr_app___override(v___x_2488_, v___x_2491_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2492_);
v___x_2494_ = v___x_2485_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
else
{
lean_object* v___x_2496_; 
lean_del_object(v___x_2485_);
lean_dec(v_a_2483_);
lean_inc(v_a_2403_);
v___x_2496_ = l_Lean_Meta_getUInt8Value_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2742_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2742_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2742_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
if (lean_obj_tag(v_a_2497_) == 1)
{
lean_object* v_val_2501_; uint8_t v___x_2502_; lean_object* v___x_2503_; lean_object* v_r_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
lean_dec(v_a_2403_);
v_val_2501_ = lean_ctor_get(v_a_2497_, 0);
lean_inc(v_val_2501_);
lean_dec_ref_known(v_a_2497_, 1);
v___x_2502_ = lean_unbox(v_val_2501_);
lean_dec(v_val_2501_);
v___x_2503_ = lean_uint8_to_nat(v___x_2502_);
v_r_2504_ = l_Lean_mkRawNatLit(v___x_2503_);
v___x_2505_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2506_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__18, &l_Lean_Meta_normLitValue___closed__18_once, _init_l_Lean_Meta_normLitValue___closed__18);
v___x_2507_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__20, &l_Lean_Meta_normLitValue___closed__20_once, _init_l_Lean_Meta_normLitValue___closed__20);
lean_inc_ref(v_r_2504_);
v___x_2508_ = l_Lean_Expr_app___override(v___x_2507_, v_r_2504_);
v___x_2509_ = l_Lean_mkApp3(v___x_2505_, v___x_2506_, v_r_2504_, v___x_2508_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2509_);
v___x_2511_ = v___x_2499_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
else
{
lean_object* v___x_2513_; 
lean_del_object(v___x_2499_);
lean_dec(v_a_2497_);
lean_inc(v_a_2403_);
v___x_2513_ = l_Lean_Meta_getUInt16Value_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2733_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2733_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2733_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
if (lean_obj_tag(v_a_2514_) == 1)
{
lean_object* v_val_2518_; uint16_t v___x_2519_; lean_object* v___x_2520_; lean_object* v_r_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_dec(v_a_2403_);
v_val_2518_ = lean_ctor_get(v_a_2514_, 0);
lean_inc(v_val_2518_);
lean_dec_ref_known(v_a_2514_, 1);
v___x_2519_ = lean_unbox(v_val_2518_);
lean_dec(v_val_2518_);
v___x_2520_ = lean_uint16_to_nat(v___x_2519_);
v_r_2521_ = l_Lean_mkRawNatLit(v___x_2520_);
v___x_2522_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2523_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__21, &l_Lean_Meta_normLitValue___closed__21_once, _init_l_Lean_Meta_normLitValue___closed__21);
v___x_2524_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__23, &l_Lean_Meta_normLitValue___closed__23_once, _init_l_Lean_Meta_normLitValue___closed__23);
lean_inc_ref(v_r_2521_);
v___x_2525_ = l_Lean_Expr_app___override(v___x_2524_, v_r_2521_);
v___x_2526_ = l_Lean_mkApp3(v___x_2522_, v___x_2523_, v_r_2521_, v___x_2525_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2526_);
v___x_2528_ = v___x_2516_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
else
{
lean_object* v___x_2530_; 
lean_del_object(v___x_2516_);
lean_dec(v_a_2514_);
lean_inc(v_a_2403_);
v___x_2530_ = l_Lean_Meta_getUInt32Value_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2724_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2724_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2724_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
if (lean_obj_tag(v_a_2531_) == 1)
{
lean_object* v_val_2535_; uint32_t v___x_2536_; lean_object* v___x_2537_; lean_object* v_r_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_dec(v_a_2403_);
v_val_2535_ = lean_ctor_get(v_a_2531_, 0);
lean_inc(v_val_2535_);
lean_dec_ref_known(v_a_2531_, 1);
v___x_2536_ = lean_unbox_uint32(v_val_2535_);
lean_dec(v_val_2535_);
v___x_2537_ = lean_uint32_to_nat(v___x_2536_);
v_r_2538_ = l_Lean_mkRawNatLit(v___x_2537_);
v___x_2539_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2540_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__24, &l_Lean_Meta_normLitValue___closed__24_once, _init_l_Lean_Meta_normLitValue___closed__24);
v___x_2541_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__26, &l_Lean_Meta_normLitValue___closed__26_once, _init_l_Lean_Meta_normLitValue___closed__26);
lean_inc_ref(v_r_2538_);
v___x_2542_ = l_Lean_Expr_app___override(v___x_2541_, v_r_2538_);
v___x_2543_ = l_Lean_mkApp3(v___x_2539_, v___x_2540_, v_r_2538_, v___x_2542_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2543_);
v___x_2545_ = v___x_2533_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
else
{
lean_object* v___x_2547_; 
lean_del_object(v___x_2533_);
lean_dec(v_a_2531_);
lean_inc(v_a_2403_);
v___x_2547_ = l_Lean_Meta_getUInt64Value_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2715_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2715_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2715_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
if (lean_obj_tag(v_a_2548_) == 1)
{
lean_object* v_val_2552_; uint64_t v___x_2553_; lean_object* v___x_2554_; lean_object* v_r_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
lean_dec(v_a_2403_);
v_val_2552_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_val_2552_);
lean_dec_ref_known(v_a_2548_, 1);
v___x_2553_ = lean_unbox_uint64(v_val_2552_);
lean_dec(v_val_2552_);
v___x_2554_ = lean_uint64_to_nat(v___x_2553_);
v_r_2555_ = l_Lean_mkRawNatLit(v___x_2554_);
v___x_2556_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_2557_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__27, &l_Lean_Meta_normLitValue___closed__27_once, _init_l_Lean_Meta_normLitValue___closed__27);
v___x_2558_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__29, &l_Lean_Meta_normLitValue___closed__29_once, _init_l_Lean_Meta_normLitValue___closed__29);
lean_inc_ref(v_r_2555_);
v___x_2559_ = l_Lean_Expr_app___override(v___x_2558_, v_r_2555_);
v___x_2560_ = l_Lean_mkApp3(v___x_2556_, v___x_2557_, v_r_2555_, v___x_2559_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2560_);
v___x_2562_ = v___x_2550_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
else
{
lean_object* v___x_2564_; 
lean_del_object(v___x_2550_);
lean_dec(v_a_2548_);
lean_inc(v_a_2403_);
v___x_2564_ = l_Lean_Meta_getInt8Value_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2706_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2706_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2706_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
if (lean_obj_tag(v_a_2565_) == 1)
{
lean_object* v_val_2569_; uint8_t v___x_2570_; uint8_t v___x_2571_; uint8_t v___x_2572_; 
lean_dec(v_a_2403_);
v_val_2569_ = lean_ctor_get(v_a_2565_, 0);
lean_inc(v_val_2569_);
lean_dec_ref_known(v_a_2565_, 1);
v___x_2570_ = lean_uint8_once(&l_Lean_Meta_normLitValue___closed__30, &l_Lean_Meta_normLitValue___closed__30_once, _init_l_Lean_Meta_normLitValue___closed__30);
v___x_2571_ = lean_unbox(v_val_2569_);
v___x_2572_ = lean_int8_dec_le(v___x_2570_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2573_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2574_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__31, &l_Lean_Meta_normLitValue___closed__31_once, _init_l_Lean_Meta_normLitValue___closed__31);
v___x_2575_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__34, &l_Lean_Meta_normLitValue___closed__34_once, _init_l_Lean_Meta_normLitValue___closed__34);
v___x_2576_ = lean_unbox(v_val_2569_);
lean_dec(v_val_2569_);
v___x_2577_ = lean_int8_to_int(v___x_2576_);
v___x_2578_ = lean_int_neg(v___x_2577_);
v___x_2579_ = l_Int_toNat(v___x_2578_);
lean_dec(v___x_2578_);
v___x_2580_ = l_Lean_instToExprInt8_mkNat(v___x_2579_);
v___x_2581_ = l_Lean_mkApp3(v___x_2573_, v___x_2574_, v___x_2575_, v___x_2580_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2581_);
v___x_2583_ = v___x_2567_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
else
{
uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2585_ = lean_unbox(v_val_2569_);
lean_dec(v_val_2569_);
v___x_2586_ = lean_int8_to_int(v___x_2585_);
v___x_2587_ = l_Int_toNat(v___x_2586_);
v___x_2588_ = l_Lean_instToExprInt8_mkNat(v___x_2587_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2588_);
v___x_2590_ = v___x_2567_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
else
{
lean_object* v___x_2592_; 
lean_del_object(v___x_2567_);
lean_dec(v_a_2565_);
lean_inc(v_a_2403_);
v___x_2592_ = l_Lean_Meta_getInt16Value_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2697_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2697_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2697_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
if (lean_obj_tag(v_a_2593_) == 1)
{
lean_object* v_val_2597_; uint16_t v___x_2598_; uint16_t v___x_2599_; uint8_t v___x_2600_; 
lean_dec(v_a_2403_);
v_val_2597_ = lean_ctor_get(v_a_2593_, 0);
lean_inc(v_val_2597_);
lean_dec_ref_known(v_a_2593_, 1);
v___x_2598_ = lean_uint16_once(&l_Lean_Meta_normLitValue___closed__35, &l_Lean_Meta_normLitValue___closed__35_once, _init_l_Lean_Meta_normLitValue___closed__35);
v___x_2599_ = lean_unbox(v_val_2597_);
v___x_2600_ = lean_int16_dec_le(v___x_2598_, v___x_2599_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; uint16_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2601_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2602_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__36, &l_Lean_Meta_normLitValue___closed__36_once, _init_l_Lean_Meta_normLitValue___closed__36);
v___x_2603_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__38, &l_Lean_Meta_normLitValue___closed__38_once, _init_l_Lean_Meta_normLitValue___closed__38);
v___x_2604_ = lean_unbox(v_val_2597_);
lean_dec(v_val_2597_);
v___x_2605_ = lean_int16_to_int(v___x_2604_);
v___x_2606_ = lean_int_neg(v___x_2605_);
v___x_2607_ = l_Int_toNat(v___x_2606_);
lean_dec(v___x_2606_);
v___x_2608_ = l_Lean_instToExprInt16_mkNat(v___x_2607_);
v___x_2609_ = l_Lean_mkApp3(v___x_2601_, v___x_2602_, v___x_2603_, v___x_2608_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2609_);
v___x_2611_ = v___x_2595_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
else
{
uint16_t v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
v___x_2613_ = lean_unbox(v_val_2597_);
lean_dec(v_val_2597_);
v___x_2614_ = lean_int16_to_int(v___x_2613_);
v___x_2615_ = l_Int_toNat(v___x_2614_);
v___x_2616_ = l_Lean_instToExprInt16_mkNat(v___x_2615_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2616_);
v___x_2618_ = v___x_2595_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
else
{
lean_object* v___x_2620_; 
lean_del_object(v___x_2595_);
lean_dec(v_a_2593_);
lean_inc(v_a_2403_);
v___x_2620_ = l_Lean_Meta_getInt32Value_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2688_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2688_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2688_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
if (lean_obj_tag(v_a_2621_) == 1)
{
lean_object* v_val_2625_; uint32_t v___x_2626_; uint32_t v___x_2627_; uint8_t v___x_2628_; 
lean_dec(v_a_2403_);
v_val_2625_ = lean_ctor_get(v_a_2621_, 0);
lean_inc(v_val_2625_);
lean_dec_ref_known(v_a_2621_, 1);
v___x_2626_ = lean_uint32_once(&l_Lean_Meta_normLitValue___closed__39, &l_Lean_Meta_normLitValue___closed__39_once, _init_l_Lean_Meta_normLitValue___closed__39);
v___x_2627_ = lean_unbox_uint32(v_val_2625_);
v___x_2628_ = lean_int32_dec_le(v___x_2626_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; uint32_t v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2629_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2630_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__40, &l_Lean_Meta_normLitValue___closed__40_once, _init_l_Lean_Meta_normLitValue___closed__40);
v___x_2631_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__42, &l_Lean_Meta_normLitValue___closed__42_once, _init_l_Lean_Meta_normLitValue___closed__42);
v___x_2632_ = lean_unbox_uint32(v_val_2625_);
lean_dec(v_val_2625_);
v___x_2633_ = lean_int32_to_int(v___x_2632_);
v___x_2634_ = lean_int_neg(v___x_2633_);
lean_dec(v___x_2633_);
v___x_2635_ = l_Int_toNat(v___x_2634_);
lean_dec(v___x_2634_);
v___x_2636_ = l_Lean_instToExprInt32_mkNat(v___x_2635_);
v___x_2637_ = l_Lean_mkApp3(v___x_2629_, v___x_2630_, v___x_2631_, v___x_2636_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2637_);
v___x_2639_ = v___x_2623_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
else
{
uint32_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2641_ = lean_unbox_uint32(v_val_2625_);
lean_dec(v_val_2625_);
v___x_2642_ = lean_int32_to_int(v___x_2641_);
v___x_2643_ = l_Int_toNat(v___x_2642_);
lean_dec(v___x_2642_);
v___x_2644_ = l_Lean_instToExprInt32_mkNat(v___x_2643_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2644_);
v___x_2646_ = v___x_2623_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
else
{
lean_object* v___x_2648_; 
lean_del_object(v___x_2623_);
lean_dec(v_a_2621_);
lean_inc(v_a_2403_);
v___x_2648_ = l_Lean_Meta_getInt64Value_x3f(v_a_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2679_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2679_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2679_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
if (lean_obj_tag(v_a_2649_) == 1)
{
lean_object* v_val_2653_; uint64_t v___x_2654_; uint64_t v___x_2655_; uint8_t v___x_2656_; 
lean_dec(v_a_2403_);
v_val_2653_ = lean_ctor_get(v_a_2649_, 0);
lean_inc(v_val_2653_);
lean_dec_ref_known(v_a_2649_, 1);
v___x_2654_ = lean_uint64_once(&l_Lean_Meta_normLitValue___closed__43, &l_Lean_Meta_normLitValue___closed__43_once, _init_l_Lean_Meta_normLitValue___closed__43);
v___x_2655_ = lean_unbox_uint64(v_val_2653_);
v___x_2656_ = lean_int64_dec_le(v___x_2654_, v___x_2655_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; uint64_t v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2657_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_2658_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__44, &l_Lean_Meta_normLitValue___closed__44_once, _init_l_Lean_Meta_normLitValue___closed__44);
v___x_2659_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__46, &l_Lean_Meta_normLitValue___closed__46_once, _init_l_Lean_Meta_normLitValue___closed__46);
v___x_2660_ = lean_unbox_uint64(v_val_2653_);
lean_dec(v_val_2653_);
v___x_2661_ = lean_int64_to_int_sint(v___x_2660_);
v___x_2662_ = lean_int_neg(v___x_2661_);
lean_dec(v___x_2661_);
v___x_2663_ = l_Int_toNat(v___x_2662_);
lean_dec(v___x_2662_);
v___x_2664_ = l_Lean_instToExprInt64_mkNat(v___x_2663_);
v___x_2665_ = l_Lean_mkApp3(v___x_2657_, v___x_2658_, v___x_2659_, v___x_2664_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2665_);
v___x_2667_ = v___x_2651_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
else
{
uint64_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2669_ = lean_unbox_uint64(v_val_2653_);
lean_dec(v_val_2653_);
v___x_2670_ = lean_int64_to_int_sint(v___x_2669_);
v___x_2671_ = l_Int_toNat(v___x_2670_);
lean_dec(v___x_2670_);
v___x_2672_ = l_Lean_instToExprInt64_mkNat(v___x_2671_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2672_);
v___x_2674_ = v___x_2651_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
else
{
lean_object* v___x_2677_; 
lean_dec(v_a_2649_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v_a_2403_);
v___x_2677_ = v___x_2651_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2403_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec(v_a_2403_);
v_a_2680_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2648_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2648_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v_a_2403_);
v_a_2689_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2620_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2620_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v_a_2403_);
v_a_2698_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2592_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2592_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v_a_2403_);
v_a_2707_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2564_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2564_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec(v_a_2403_);
v_a_2716_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2547_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2547_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_a_2403_);
v_a_2725_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2530_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2530_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_a_2403_);
v_a_2734_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2513_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2513_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_a_2403_);
v_a_2743_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2496_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2496_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v_a_2403_);
v_a_2752_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2482_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2482_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_a_2403_);
v_a_2761_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2461_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2461_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_a_2403_);
v_a_2770_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2437_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2437_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_a_2403_);
v_a_2779_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2414_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2414_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_a_2403_);
v_a_2788_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2404_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2404_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue___boxed(lean_object* v_e_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Meta_normLitValue(v_e_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(lean_object* v_m_2809_, lean_object* v_s_2810_, lean_object* v_exp_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_s_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_s_2822_ = l_Lean_Expr_consumeMData(v_s_2810_);
v___x_2823_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__0));
v___x_2824_ = l_Lean_Expr_isConstOf(v_s_2822_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___closed__1));
v___x_2826_ = l_Lean_Expr_isConstOf(v_s_2822_, v___x_2825_);
lean_dec_ref(v_s_2822_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_box(v___x_2826_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
else
{
goto v___jp_2817_;
}
}
else
{
lean_dec_ref(v_s_2822_);
goto v___jp_2817_;
}
v___jp_2817_:
{
lean_object* v___x_2818_; 
v___x_2818_ = l_Lean_Meta_isNatValue(v_m_2809_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; uint8_t v___x_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v___x_2820_ = lean_unbox(v_a_2819_);
if (v___x_2820_ == 0)
{
return v___x_2818_;
}
else
{
lean_object* v___x_2821_; 
lean_dec_ref_known(v___x_2818_, 1);
v___x_2821_ = l_Lean_Meta_isNatValue(v_exp_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
return v___x_2821_;
}
}
else
{
return v___x_2818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs___boxed(lean_object* v_m_2829_, lean_object* v_s_2830_, lean_object* v_exp_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_2829_, v_s_2830_, v_exp_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec_ref(v_exp_2831_);
lean_dec_ref(v_s_2830_);
lean_dec_ref(v_m_2829_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(lean_object* v_type_2838_, lean_object* v_m_2839_, lean_object* v_s_2840_, lean_object* v_exp_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_Meta_whnfD(v_type_2838_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2865_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2865_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2865_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2852_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_2853_ = l_Lean_Expr_isConstOf(v_a_2848_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; uint8_t v___x_2855_; 
v___x_2854_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_2855_ = l_Lean_Expr_isConstOf(v_a_2848_, v___x_2854_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2856_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_2857_ = l_Lean_Expr_isConstOf(v_a_2848_, v___x_2856_);
lean_dec(v_a_2848_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2860_; 
v___x_2858_ = lean_box(v___x_2857_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2858_);
v___x_2860_ = v___x_2850_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
else
{
lean_object* v___x_2862_; 
lean_del_object(v___x_2850_);
v___x_2862_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_2839_, v_s_2840_, v_exp_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
return v___x_2862_;
}
}
else
{
lean_object* v___x_2863_; 
lean_del_object(v___x_2850_);
lean_dec(v_a_2848_);
v___x_2863_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_2839_, v_s_2840_, v_exp_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
return v___x_2863_;
}
}
else
{
lean_object* v___x_2864_; 
lean_del_object(v___x_2850_);
lean_dec(v_a_2848_);
v___x_2864_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitArgs(v_m_2839_, v_s_2840_, v_exp_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
return v___x_2864_;
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
v_a_2866_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2847_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2847_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue___boxed(lean_object* v_type_2874_, lean_object* v_m_2875_, lean_object* v_s_2876_, lean_object* v_exp_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(v_type_2874_, v_m_2875_, v_s_2876_, v_exp_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
lean_dec_ref(v_exp_2877_);
lean_dec_ref(v_s_2876_);
lean_dec_ref(v_m_2875_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue(lean_object* v_type_2884_, lean_object* v_n_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2891_ = l_Lean_Expr_consumeMData(v_n_2885_);
v___x_2892_ = l_Lean_Expr_isRawNatLit(v___x_2891_);
lean_dec_ref(v___x_2891_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec_ref(v_type_2884_);
v___x_2893_ = lean_box(v___x_2892_);
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
return v___x_2894_;
}
else
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_Meta_whnfD(v_type_2884_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_3017_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_2898_ = v___x_2895_;
v_isShared_2899_ = v_isSharedCheck_3017_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_3017_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_Expr_getAppFn(v_a_2896_);
if (lean_obj_tag(v___x_2900_) == 4)
{
lean_object* v_declName_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v_declName_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_declName_2901_);
lean_dec_ref_known(v___x_2900_, 2);
v___x_2902_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_2903_ = lean_name_eq(v_declName_2901_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2904_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_2905_ = lean_name_eq(v_declName_2901_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2906_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_2907_ = lean_name_eq(v_declName_2901_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_2909_ = lean_name_eq(v_declName_2901_, v___x_2908_);
if (v___x_2909_ == 0)
{
lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_2911_ = lean_name_eq(v_declName_2901_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_2913_ = lean_name_eq(v_declName_2901_, v___x_2912_);
if (v___x_2913_ == 0)
{
lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_2915_ = lean_name_eq(v_declName_2901_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; uint8_t v___x_2917_; 
v___x_2916_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_2917_ = lean_name_eq(v_declName_2901_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_2919_ = lean_name_eq(v_declName_2901_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2920_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_2921_ = lean_name_eq(v_declName_2901_, v___x_2920_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_2923_ = lean_name_eq(v_declName_2901_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2924_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_2925_ = lean_name_eq(v_declName_2901_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; uint8_t v___x_2927_; 
v___x_2926_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_2927_ = lean_name_eq(v_declName_2901_, v___x_2926_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; uint8_t v___x_2929_; 
v___x_2928_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_2929_ = lean_name_eq(v_declName_2901_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2930_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_2931_ = lean_name_eq(v_declName_2901_, v___x_2930_);
lean_dec(v_declName_2901_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2934_; 
lean_dec(v_a_2896_);
v___x_2932_ = lean_box(v___x_2931_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2932_);
v___x_2934_ = v___x_2898_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
lean_del_object(v___x_2898_);
v___x_2936_ = l_Lean_Expr_appArg_x21(v_a_2896_);
lean_dec(v_a_2896_);
v___x_2937_ = l_Lean_Meta_whnfD(v___x_2936_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
v___x_2939_ = l_Lean_Meta_isNatValue(v_a_2938_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
lean_dec(v_a_2938_);
return v___x_2939_;
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
v_a_2940_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2937_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2937_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
}
else
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
lean_dec(v_declName_2901_);
lean_del_object(v___x_2898_);
v___x_2948_ = l_Lean_Expr_appArg_x21(v_a_2896_);
lean_dec(v_a_2896_);
v___x_2949_ = l_Lean_Meta_whnfD(v___x_2948_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = l_Lean_Meta_isNonZeroNatValue(v_a_2950_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
lean_dec(v_a_2950_);
return v___x_2951_;
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
v_a_2952_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2949_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2949_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
else
{
lean_object* v___x_2960_; lean_object* v___x_2962_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_2960_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2960_);
v___x_2962_ = v___x_2898_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
else
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_2964_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2964_);
v___x_2966_ = v___x_2898_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2970_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_2968_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2968_);
v___x_2970_ = v___x_2898_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_2972_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2972_);
v___x_2974_ = v___x_2898_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_2976_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2976_);
v___x_2978_ = v___x_2898_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
else
{
lean_object* v___x_2980_; lean_object* v___x_2982_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_2980_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2980_);
v___x_2982_ = v___x_2898_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2986_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_2984_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2984_);
v___x_2986_ = v___x_2898_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_2988_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2988_);
v___x_2990_ = v___x_2898_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
else
{
lean_object* v___x_2992_; lean_object* v___x_2994_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_2992_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2992_);
v___x_2994_ = v___x_2898_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2998_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_2996_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2996_);
v___x_2998_ = v___x_2898_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3002_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_3000_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_3000_);
v___x_3002_ = v___x_2898_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3006_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_3004_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_3004_);
v___x_3006_ = v___x_2898_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3010_; 
lean_dec(v_declName_2901_);
lean_dec(v_a_2896_);
v___x_3008_ = lean_box(v___x_2892_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_3008_);
v___x_3010_ = v___x_2898_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
else
{
uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3015_; 
lean_dec_ref(v___x_2900_);
lean_dec(v_a_2896_);
v___x_3012_ = 0;
v___x_3013_ = lean_box(v___x_3012_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_3013_);
v___x_3015_ = v___x_2898_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
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
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
v_a_3018_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_2895_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_2895_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue___boxed(lean_object* v_type_3026_, lean_object* v_n_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue(v_type_3026_, v_n_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec_ref(v_n_3027_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue(lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_3034_, v_a_3036_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3144_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3144_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3144_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = l_Lean_Expr_cleanupAnnotations(v_a_3045_);
lean_dec(v_a_3045_);
v___x_3050_ = l_Lean_Expr_isApp(v___x_3049_);
if (v___x_3050_ == 0)
{
lean_dec_ref(v___x_3049_);
lean_del_object(v___x_3047_);
goto v___jp_3040_;
}
else
{
lean_object* v___x_3051_; uint8_t v___x_3052_; 
v___x_3051_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3049_);
v___x_3052_ = l_Lean_Expr_isApp(v___x_3051_);
if (v___x_3052_ == 0)
{
lean_dec_ref(v___x_3051_);
lean_dec_ref(v___x_3049_);
lean_del_object(v___x_3047_);
goto v___jp_3040_;
}
else
{
lean_object* v___x_3053_; uint8_t v___x_3054_; 
v___x_3053_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3051_);
v___x_3054_ = l_Lean_Expr_isApp(v___x_3053_);
if (v___x_3054_ == 0)
{
lean_dec_ref(v___x_3053_);
lean_dec_ref(v___x_3051_);
lean_dec_ref(v___x_3049_);
lean_del_object(v___x_3047_);
goto v___jp_3040_;
}
else
{
lean_object* v_arg_3055_; lean_object* v_arg_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; 
v_arg_3055_ = lean_ctor_get(v___x_3051_, 1);
lean_inc_ref(v_arg_3055_);
lean_dec_ref(v___x_3051_);
v_arg_3056_ = lean_ctor_get(v___x_3053_, 1);
lean_inc_ref(v_arg_3056_);
v___x_3057_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3053_);
lean_dec_ref(v___x_3053_);
v___x_3058_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_3059_ = l_Lean_Expr_isConstOf(v___x_3057_, v___x_3058_);
if (v___x_3059_ == 0)
{
uint8_t v___x_3060_; 
lean_del_object(v___x_3047_);
v___x_3060_ = l_Lean_Expr_isApp(v___x_3057_);
if (v___x_3060_ == 0)
{
lean_dec_ref(v___x_3057_);
lean_dec_ref(v_arg_3056_);
lean_dec_ref(v_arg_3055_);
lean_dec_ref(v___x_3049_);
goto v___jp_3040_;
}
else
{
lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3057_);
lean_dec_ref(v___x_3057_);
v___x_3062_ = l_Lean_Expr_isApp(v___x_3061_);
if (v___x_3062_ == 0)
{
lean_dec_ref(v___x_3061_);
lean_dec_ref(v_arg_3056_);
lean_dec_ref(v_arg_3055_);
lean_dec_ref(v___x_3049_);
goto v___jp_3040_;
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3063_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3061_);
v___x_3064_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_3065_ = l_Lean_Expr_isConstOf(v___x_3063_, v___x_3064_);
lean_dec_ref(v___x_3063_);
if (v___x_3065_ == 0)
{
lean_dec_ref(v___x_3061_);
lean_dec_ref(v_arg_3056_);
lean_dec_ref(v_arg_3055_);
lean_dec_ref(v___x_3049_);
goto v___jp_3040_;
}
else
{
lean_object* v_arg_3066_; lean_object* v_arg_3067_; lean_object* v___x_3068_; 
v_arg_3066_ = lean_ctor_get(v___x_3049_, 1);
lean_inc_ref(v_arg_3066_);
lean_dec_ref(v___x_3049_);
v_arg_3067_ = lean_ctor_get(v___x_3061_, 1);
lean_inc_ref(v_arg_3067_);
lean_dec_ref(v___x_3061_);
v___x_3068_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(v_arg_3067_, v_arg_3056_, v_arg_3055_, v_arg_3066_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
lean_dec_ref(v_arg_3066_);
lean_dec_ref(v_arg_3055_);
lean_dec_ref(v_arg_3056_);
return v___x_3068_;
}
}
}
}
else
{
lean_object* v___x_3069_; uint8_t v___x_3070_; 
lean_dec_ref(v___x_3057_);
lean_dec_ref(v___x_3049_);
v___x_3069_ = l_Lean_Expr_consumeMData(v_arg_3055_);
lean_dec_ref(v_arg_3055_);
v___x_3070_ = l_Lean_Expr_isRawNatLit(v___x_3069_);
lean_dec_ref(v___x_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
lean_dec_ref(v_arg_3056_);
v___x_3071_ = lean_box(v___x_3070_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3071_);
v___x_3073_ = v___x_3047_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
else
{
lean_object* v___x_3075_; 
lean_del_object(v___x_3047_);
v___x_3075_ = l_Lean_Meta_whnfD(v_arg_3056_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3135_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3135_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3135_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lean_Expr_getAppFn(v_a_3076_);
lean_dec(v_a_3076_);
if (lean_obj_tag(v___x_3080_) == 4)
{
lean_object* v_declName_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
v_declName_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_declName_3081_);
lean_dec_ref_known(v___x_3080_, 2);
v___x_3082_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_3083_ = lean_name_eq(v_declName_3081_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_3085_ = lean_name_eq(v_declName_3081_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3086_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_3087_ = lean_name_eq(v_declName_3081_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3088_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_3089_ = lean_name_eq(v_declName_3081_, v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3090_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_3091_ = lean_name_eq(v_declName_3081_, v___x_3090_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3092_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_3093_ = lean_name_eq(v_declName_3081_, v___x_3092_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3094_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_3095_ = lean_name_eq(v_declName_3081_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3096_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_3097_ = lean_name_eq(v_declName_3081_, v___x_3096_);
lean_dec(v_declName_3081_);
v___x_3098_ = lean_box(v___x_3097_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3098_);
v___x_3100_ = v___x_3078_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
lean_dec(v_declName_3081_);
v___x_3102_ = lean_box(v___x_3059_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3102_);
v___x_3104_ = v___x_3078_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
lean_dec(v_declName_3081_);
v___x_3106_ = lean_box(v___x_3059_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3106_);
v___x_3108_ = v___x_3078_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3112_; 
lean_dec(v_declName_3081_);
v___x_3110_ = lean_box(v___x_3059_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3110_);
v___x_3112_ = v___x_3078_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3116_; 
lean_dec(v_declName_3081_);
v___x_3114_ = lean_box(v___x_3059_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3114_);
v___x_3116_ = v___x_3078_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
lean_dec(v_declName_3081_);
v___x_3118_ = lean_box(v___x_3059_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3118_);
v___x_3120_ = v___x_3078_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
else
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
lean_dec(v_declName_3081_);
v___x_3122_ = lean_box(v___x_3059_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3122_);
v___x_3124_ = v___x_3078_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
lean_dec(v_declName_3081_);
v___x_3126_ = lean_box(v___x_3059_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3126_);
v___x_3128_ = v___x_3078_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
else
{
uint8_t v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
lean_dec_ref(v___x_3080_);
v___x_3130_ = 0;
v___x_3131_ = lean_box(v___x_3130_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3131_);
v___x_3133_ = v___x_3078_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_a_3136_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3075_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3075_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
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
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
v_a_3145_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3044_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3044_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
v___jp_3040_:
{
uint8_t v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3041_ = 0;
v___x_3042_ = lean_box(v___x_3041_);
v___x_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
return v___x_3043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue___boxed(lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue(v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(lean_object* v_e_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___x_3170_ = l_Lean_Expr_cleanupAnnotations(v_e_3160_);
v___x_3171_ = l_Lean_Expr_isApp(v___x_3170_);
if (v___x_3171_ == 0)
{
lean_dec_ref(v___x_3170_);
goto v___jp_3166_;
}
else
{
lean_object* v___x_3172_; uint8_t v___x_3173_; 
v___x_3172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3170_);
lean_dec_ref(v___x_3170_);
v___x_3173_ = l_Lean_Expr_isApp(v___x_3172_);
if (v___x_3173_ == 0)
{
lean_dec_ref(v___x_3172_);
goto v___jp_3166_;
}
else
{
lean_object* v___x_3174_; uint8_t v___x_3175_; 
v___x_3174_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3172_);
v___x_3175_ = l_Lean_Expr_isApp(v___x_3174_);
if (v___x_3175_ == 0)
{
lean_dec_ref(v___x_3174_);
lean_dec_ref(v___x_3172_);
goto v___jp_3166_;
}
else
{
lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3176_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3174_);
v___x_3177_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_3178_ = l_Lean_Expr_isConstOf(v___x_3176_, v___x_3177_);
lean_dec_ref(v___x_3176_);
if (v___x_3178_ == 0)
{
lean_dec_ref(v___x_3174_);
lean_dec_ref(v___x_3172_);
goto v___jp_3166_;
}
else
{
lean_object* v_arg_3179_; lean_object* v___x_3180_; uint8_t v___x_3181_; 
v_arg_3179_ = lean_ctor_get(v___x_3172_, 1);
lean_inc_ref(v_arg_3179_);
lean_dec_ref(v___x_3172_);
v___x_3180_ = l_Lean_Expr_consumeMData(v_arg_3179_);
lean_dec_ref(v_arg_3179_);
v___x_3181_ = l_Lean_Expr_isRawNatLit(v___x_3180_);
lean_dec_ref(v___x_3180_);
if (v___x_3181_ == 0)
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec_ref(v___x_3174_);
v___x_3182_ = lean_box(v___x_3181_);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
else
{
lean_object* v_arg_3184_; lean_object* v___x_3185_; 
v_arg_3184_ = lean_ctor_get(v___x_3174_, 1);
lean_inc_ref(v_arg_3184_);
lean_dec_ref(v___x_3174_);
v___x_3185_ = l_Lean_Meta_whnfD(v_arg_3184_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3197_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3188_ = v___x_3185_;
v_isShared_3189_ = v_isSharedCheck_3197_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3185_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3197_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3195_; 
v___x_3190_ = l_Lean_Expr_getAppFn(v_a_3186_);
lean_dec(v_a_3186_);
v___x_3191_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__1));
v___x_3192_ = l_Lean_Expr_isConstOf(v___x_3190_, v___x_3191_);
lean_dec_ref(v___x_3190_);
v___x_3193_ = lean_box(v___x_3192_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3193_);
v___x_3195_ = v___x_3188_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
v_a_3198_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3185_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3185_);
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
}
}
}
v___jp_3166_:
{
uint8_t v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = 0;
v___x_3168_ = lean_box(v___x_3167_);
v___x_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
return v___x_3169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat___boxed(lean_object* v_e_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(v_e_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
lean_dec_ref(v_e_3206_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue(lean_object* v_a_3213_, lean_object* v_b_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_){
_start:
{
lean_object* v___y_3221_; lean_object* v___x_3226_; uint8_t v___x_3227_; 
v___x_3226_ = l_Lean_Expr_cleanupAnnotations(v_a_3213_);
v___x_3227_ = l_Lean_Expr_isApp(v___x_3226_);
if (v___x_3227_ == 0)
{
lean_dec_ref(v___x_3226_);
v___y_3221_ = v_a_3213_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3226_);
v___x_3229_ = l_Lean_Expr_isApp(v___x_3228_);
if (v___x_3229_ == 0)
{
lean_dec_ref(v___x_3228_);
lean_dec_ref(v___x_3226_);
v___y_3221_ = v_a_3213_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3230_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3228_);
lean_dec_ref(v___x_3228_);
v___x_3231_ = l_Lean_Expr_isApp(v___x_3230_);
if (v___x_3231_ == 0)
{
lean_dec_ref(v___x_3230_);
lean_dec_ref(v___x_3226_);
v___y_3221_ = v_a_3213_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v___x_3232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3230_);
lean_dec_ref(v___x_3230_);
v___x_3233_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_3234_ = l_Lean_Expr_isConstOf(v___x_3232_, v___x_3233_);
lean_dec_ref(v___x_3232_);
if (v___x_3234_ == 0)
{
lean_dec_ref(v___x_3226_);
v___y_3221_ = v_a_3213_;
goto v___jp_3220_;
}
else
{
lean_object* v_arg_3235_; 
lean_dec_ref(v_a_3213_);
v_arg_3235_ = lean_ctor_get(v___x_3226_, 1);
lean_inc_ref(v_arg_3235_);
lean_dec_ref(v___x_3226_);
v___y_3221_ = v_arg_3235_;
goto v___jp_3220_;
}
}
}
}
v___jp_3220_:
{
lean_object* v___x_3222_; 
v___x_3222_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(v___y_3221_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_);
lean_dec_ref(v___y_3221_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; uint8_t v___x_3224_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v___x_3224_ = lean_unbox(v_a_3223_);
if (v___x_3224_ == 0)
{
return v___x_3222_;
}
else
{
lean_object* v___x_3225_; 
lean_dec_ref_known(v___x_3222_, 1);
v___x_3225_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue_isRatOfNat(v_b_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_);
return v___x_3225_;
}
}
else
{
return v___x_3222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue___boxed(lean_object* v_a_3236_, lean_object* v_b_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue(v_a_3236_, v_b_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3238_);
lean_dec_ref(v_b_3237_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue(lean_object* v_e_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_){
_start:
{
lean_object* v_w_3251_; lean_object* v_v_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___x_3261_; lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3366_; 
v___x_3261_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_3244_, v_a_3246_);
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3264_ = v___x_3261_;
v_isShared_3265_ = v_isSharedCheck_3366_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3261_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3366_;
goto v_resetjp_3263_;
}
v___jp_3250_:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_Meta_isNatValue(v_w_3251_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec_ref(v_w_3251_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; uint8_t v___x_3259_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v___x_3259_ = lean_unbox(v_a_3258_);
if (v___x_3259_ == 0)
{
lean_dec_ref(v_v_3252_);
return v___x_3257_;
}
else
{
lean_object* v___x_3260_; 
lean_dec_ref_known(v___x_3257_, 1);
v___x_3260_ = l_Lean_Meta_isNatValue(v_v_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec_ref(v_v_3252_);
return v___x_3260_;
}
}
else
{
lean_dec_ref(v_v_3252_);
return v___x_3257_;
}
}
v_resetjp_3263_:
{
lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; 
if (lean_obj_tag(v_a_3262_) == 9)
{
lean_object* v_a_3355_; 
v_a_3355_ = lean_ctor_get(v_a_3262_, 0);
lean_inc_ref(v_a_3355_);
if (lean_obj_tag(v_a_3355_) == 1)
{
lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3364_; 
lean_dec_ref_known(v_a_3262_, 1);
lean_del_object(v___x_3264_);
v_isSharedCheck_3364_ = !lean_is_exclusive(v_a_3355_);
if (v_isSharedCheck_3364_ == 0)
{
lean_object* v_unused_3365_; 
v_unused_3365_ = lean_ctor_get(v_a_3355_, 0);
lean_dec(v_unused_3365_);
v___x_3357_ = v_a_3355_;
v_isShared_3358_ = v_isSharedCheck_3364_;
goto v_resetjp_3356_;
}
else
{
lean_dec(v_a_3355_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3364_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
uint8_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3359_ = 1;
v___x_3360_ = lean_box(v___x_3359_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set_tag(v___x_3357_, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3360_);
v___x_3362_ = v___x_3357_;
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
lean_dec_ref(v_a_3355_);
v___y_3267_ = v_a_3245_;
v___y_3268_ = v_a_3246_;
v___y_3269_ = v_a_3247_;
v___y_3270_ = v_a_3248_;
goto v___jp_3266_;
}
}
else
{
v___y_3267_ = v_a_3245_;
v___y_3268_ = v_a_3246_;
v___y_3269_ = v_a_3247_;
v___y_3270_ = v_a_3248_;
goto v___jp_3266_;
}
v___jp_3266_:
{
lean_object* v___x_3271_; uint8_t v___x_3272_; 
v___x_3271_ = l_Lean_Expr_consumeMData(v_a_3262_);
v___x_3272_ = l_Lean_Expr_isRawNatLit(v___x_3271_);
lean_dec_ref(v___x_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; 
lean_del_object(v___x_3264_);
v___x_3273_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_3262_, v___y_3268_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3342_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3276_ = v___x_3273_;
v_isShared_3277_ = v_isSharedCheck_3342_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3273_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3342_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3278_; uint8_t v___x_3279_; 
v___x_3278_ = l_Lean_Expr_cleanupAnnotations(v_a_3274_);
lean_dec(v_a_3274_);
v___x_3279_ = l_Lean_Expr_isApp(v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3282_; 
lean_dec_ref(v___x_3278_);
v___x_3280_ = lean_box(v___x_3272_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3280_);
v___x_3282_ = v___x_3276_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
else
{
lean_object* v_arg_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v_arg_3284_ = lean_ctor_get(v___x_3278_, 1);
lean_inc_ref(v_arg_3284_);
v___x_3285_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3278_);
lean_dec_ref(v___x_3278_);
v___x_3286_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_3287_ = l_Lean_Expr_isConstOf(v___x_3285_, v___x_3286_);
if (v___x_3287_ == 0)
{
uint8_t v___x_3288_; 
v___x_3288_ = l_Lean_Expr_isApp(v___x_3285_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_arg_3284_);
v___x_3289_ = lean_box(v___x_3272_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3289_);
v___x_3291_ = v___x_3276_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
else
{
lean_object* v_arg_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v_arg_3293_ = lean_ctor_get(v___x_3285_, 1);
lean_inc_ref(v_arg_3293_);
v___x_3294_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3285_);
lean_dec_ref(v___x_3285_);
v___x_3295_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_3296_ = l_Lean_Expr_isConstOf(v___x_3294_, v___x_3295_);
if (v___x_3296_ == 0)
{
uint8_t v___x_3297_; 
v___x_3297_ = l_Lean_Expr_isApp(v___x_3294_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3300_; 
lean_dec_ref(v___x_3294_);
lean_dec_ref(v_arg_3293_);
lean_dec_ref(v_arg_3284_);
v___x_3298_ = lean_box(v___x_3272_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3298_);
v___x_3300_ = v___x_3276_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
else
{
lean_object* v_arg_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v_arg_3302_ = lean_ctor_get(v___x_3294_, 1);
lean_inc_ref(v_arg_3302_);
v___x_3303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3294_);
lean_dec_ref(v___x_3294_);
v___x_3304_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__4));
v___x_3305_ = l_Lean_Expr_isConstOf(v___x_3303_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_3307_ = l_Lean_Expr_isConstOf(v___x_3303_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3308_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_3309_ = l_Lean_Expr_isConstOf(v___x_3303_, v___x_3308_);
if (v___x_3309_ == 0)
{
uint8_t v___x_3310_; 
v___x_3310_ = l_Lean_Expr_isApp(v___x_3303_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
lean_dec_ref(v___x_3303_);
lean_dec_ref(v_arg_3302_);
lean_dec_ref(v_arg_3293_);
lean_dec_ref(v_arg_3284_);
v___x_3311_ = lean_box(v___x_3272_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3311_);
v___x_3313_ = v___x_3276_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
else
{
lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3315_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3303_);
lean_dec_ref(v___x_3303_);
v___x_3316_ = l_Lean_Expr_isApp(v___x_3315_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3319_; 
lean_dec_ref(v___x_3315_);
lean_dec_ref(v_arg_3302_);
lean_dec_ref(v_arg_3293_);
lean_dec_ref(v_arg_3284_);
v___x_3317_ = lean_box(v___x_3272_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3317_);
v___x_3319_ = v___x_3276_;
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
lean_object* v___x_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; 
v___x_3321_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3315_);
v___x_3322_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatLit_x3f___closed__4));
v___x_3323_ = l_Lean_Expr_isConstOf(v___x_3321_, v___x_3322_);
if (v___x_3323_ == 0)
{
uint8_t v___x_3324_; 
lean_dec_ref(v___x_3315_);
lean_dec_ref(v_arg_3302_);
v___x_3324_ = l_Lean_Expr_isApp(v___x_3321_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; lean_object* v___x_3327_; 
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_arg_3293_);
lean_dec_ref(v_arg_3284_);
v___x_3325_ = lean_box(v___x_3272_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3325_);
v___x_3327_ = v___x_3276_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3329_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3321_);
lean_dec_ref(v___x_3321_);
v___x_3330_ = ((lean_object*)(l_Lean_Meta_getRatValue_x3f___closed__2));
v___x_3331_ = l_Lean_Expr_isConstOf(v___x_3329_, v___x_3330_);
lean_dec_ref(v___x_3329_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3334_; 
lean_dec_ref(v_arg_3293_);
lean_dec_ref(v_arg_3284_);
v___x_3332_ = lean_box(v___x_3272_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3332_);
v___x_3334_ = v___x_3276_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
else
{
lean_object* v___x_3336_; 
lean_del_object(v___x_3276_);
v___x_3336_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isRatDivLitValue(v_arg_3293_, v_arg_3284_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec_ref(v_arg_3284_);
return v___x_3336_;
}
}
}
else
{
lean_object* v_arg_3337_; lean_object* v___x_3338_; 
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3276_);
v_arg_3337_ = lean_ctor_get(v___x_3315_, 1);
lean_inc_ref(v_arg_3337_);
lean_dec_ref(v___x_3315_);
v___x_3338_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfScientificLitValue(v_arg_3337_, v_arg_3302_, v_arg_3293_, v_arg_3284_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec_ref(v_arg_3284_);
lean_dec_ref(v_arg_3293_);
lean_dec_ref(v_arg_3302_);
return v___x_3338_;
}
}
}
}
else
{
lean_object* v___x_3339_; 
lean_dec_ref(v___x_3303_);
lean_dec_ref(v_arg_3284_);
lean_del_object(v___x_3276_);
v___x_3339_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isOfNatLitValue(v_arg_3302_, v_arg_3293_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec_ref(v_arg_3293_);
return v___x_3339_;
}
}
else
{
lean_object* v___x_3340_; 
lean_dec_ref(v___x_3303_);
lean_dec_ref(v_arg_3302_);
lean_dec_ref(v_arg_3293_);
lean_del_object(v___x_3276_);
v___x_3340_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_isNegLitValue(v_arg_3284_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
return v___x_3340_;
}
}
else
{
lean_dec_ref(v___x_3303_);
lean_dec_ref(v_arg_3284_);
lean_del_object(v___x_3276_);
v_w_3251_ = v_arg_3302_;
v_v_3252_ = v_arg_3293_;
v___y_3253_ = v___y_3267_;
v___y_3254_ = v___y_3268_;
v___y_3255_ = v___y_3269_;
v___y_3256_ = v___y_3270_;
goto v___jp_3250_;
}
}
}
else
{
lean_dec_ref(v___x_3294_);
lean_del_object(v___x_3276_);
v_w_3251_ = v_arg_3293_;
v_v_3252_ = v_arg_3284_;
v___y_3253_ = v___y_3267_;
v___y_3254_ = v___y_3268_;
v___y_3255_ = v___y_3269_;
v___y_3256_ = v___y_3270_;
goto v___jp_3250_;
}
}
}
else
{
lean_object* v___x_3341_; 
lean_dec_ref(v___x_3285_);
lean_del_object(v___x_3276_);
v___x_3341_ = l_Lean_Meta_isNatValue(v_arg_3284_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec_ref(v_arg_3284_);
return v___x_3341_;
}
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
v_a_3343_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3273_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3273_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3353_; 
lean_dec(v_a_3262_);
v___x_3351_ = lean_box(v___x_3272_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 0, v___x_3351_);
v___x_3353_ = v___x_3264_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue___boxed(lean_object* v_e_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Lean_Meta_isLitValue(v_e_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
return v_res_3373_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__2(void){
_start:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3378_ = lean_box(0);
v___x_3379_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__1));
v___x_3380_ = l_Lean_mkConst(v___x_3379_, v___x_3378_);
return v___x_3380_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__5(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3385_ = lean_box(0);
v___x_3386_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__4));
v___x_3387_ = l_Lean_mkConst(v___x_3386_, v___x_3385_);
return v___x_3387_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__7(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = lean_box(0);
v___x_3392_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__6));
v___x_3393_ = l_Lean_mkConst(v___x_3392_, v___x_3391_);
return v___x_3393_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__10(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3398_ = lean_box(0);
v___x_3399_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__9));
v___x_3400_ = l_Lean_mkConst(v___x_3399_, v___x_3398_);
return v___x_3400_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__11(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = lean_unsigned_to_nat(1u);
v___x_3402_ = lean_nat_to_int(v___x_3401_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__15(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_3409_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__14));
v___x_3410_ = l_Lean_mkConst(v___x_3409_, v___x_3408_);
return v___x_3410_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__16(void){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3411_ = lean_box(0);
v___x_3412_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_3413_ = l_Lean_mkConst(v___x_3412_, v___x_3411_);
return v___x_3413_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__19(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3417_ = lean_box(0);
v___x_3418_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__18));
v___x_3419_ = l_Lean_mkConst(v___x_3418_, v___x_3417_);
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__22(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3423_ = lean_box(0);
v___x_3424_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__21));
v___x_3425_ = l_Lean_mkConst(v___x_3424_, v___x_3423_);
return v___x_3425_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__25(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3430_ = lean_box(0);
v___x_3431_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__24));
v___x_3432_ = l_Lean_mkConst(v___x_3431_, v___x_3430_);
return v___x_3432_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__28(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3437_ = lean_box(0);
v___x_3438_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__27));
v___x_3439_ = l_Lean_mkConst(v___x_3438_, v___x_3437_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor(lean_object* v_e_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v___x_3446_; lean_object* v_a_3447_; lean_object* v___x_3448_; 
v___x_3446_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_3440_, v_a_3442_);
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref(v___x_3446_);
v___x_3448_ = l_Lean_Meta_getNatValue_x3f(v_a_3447_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3538_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3538_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3538_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
if (lean_obj_tag(v_a_3449_) == 1)
{
lean_object* v_val_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; 
lean_dec(v_a_3447_);
v_val_3453_ = lean_ctor_get(v_a_3449_, 0);
lean_inc(v_val_3453_);
lean_dec_ref_known(v_a_3449_, 1);
v___x_3454_ = lean_unsigned_to_nat(0u);
v___x_3455_ = lean_nat_dec_eq(v_val_3453_, v___x_3454_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3456_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__2, &l_Lean_Meta_litToCtor___closed__2_once, _init_l_Lean_Meta_litToCtor___closed__2);
v___x_3457_ = lean_unsigned_to_nat(1u);
v___x_3458_ = lean_nat_sub(v_val_3453_, v___x_3457_);
lean_dec(v_val_3453_);
v___x_3459_ = l_Lean_mkNatLit(v___x_3458_);
v___x_3460_ = l_Lean_Expr_app___override(v___x_3456_, v___x_3459_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3460_);
v___x_3462_ = v___x_3451_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
else
{
lean_object* v___x_3464_; lean_object* v___x_3466_; 
lean_dec(v_val_3453_);
v___x_3464_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__5, &l_Lean_Meta_litToCtor___closed__5_once, _init_l_Lean_Meta_litToCtor___closed__5);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3464_);
v___x_3466_ = v___x_3451_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
else
{
lean_object* v___x_3468_; 
lean_del_object(v___x_3451_);
lean_dec(v_a_3449_);
lean_inc(v_a_3447_);
v___x_3468_ = l_Lean_Meta_getIntValue_x3f(v_a_3447_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3529_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3471_ = v___x_3468_;
v_isShared_3472_ = v_isSharedCheck_3529_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3529_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
if (lean_obj_tag(v_a_3469_) == 1)
{
lean_object* v_val_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
lean_dec(v_a_3447_);
v_val_3473_ = lean_ctor_get(v_a_3469_, 0);
lean_inc(v_val_3473_);
lean_dec_ref_known(v_a_3469_, 1);
v___x_3474_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_3475_ = lean_int_dec_lt(v_val_3473_, v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___x_3476_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__7, &l_Lean_Meta_litToCtor___closed__7_once, _init_l_Lean_Meta_litToCtor___closed__7);
v___x_3477_ = l_Int_toNat(v_val_3473_);
lean_dec(v_val_3473_);
v___x_3478_ = l_Lean_mkNatLit(v___x_3477_);
v___x_3479_ = l_Lean_Expr_app___override(v___x_3476_, v___x_3478_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3479_);
v___x_3481_ = v___x_3471_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3483_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__10, &l_Lean_Meta_litToCtor___closed__10_once, _init_l_Lean_Meta_litToCtor___closed__10);
v___x_3484_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__11, &l_Lean_Meta_litToCtor___closed__11_once, _init_l_Lean_Meta_litToCtor___closed__11);
v___x_3485_ = lean_int_add(v_val_3473_, v___x_3484_);
lean_dec(v_val_3473_);
v___x_3486_ = lean_int_neg(v___x_3485_);
lean_dec(v___x_3485_);
v___x_3487_ = l_Int_toNat(v___x_3486_);
lean_dec(v___x_3486_);
v___x_3488_ = l_Lean_mkNatLit(v___x_3487_);
v___x_3489_ = l_Lean_Expr_app___override(v___x_3483_, v___x_3488_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3489_);
v___x_3491_ = v___x_3471_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
else
{
lean_object* v___x_3493_; 
lean_del_object(v___x_3471_);
lean_dec(v_a_3469_);
lean_inc(v_a_3447_);
v___x_3493_ = l_Lean_Meta_getFinValue_x3f(v_a_3447_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3520_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3520_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3520_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
if (lean_obj_tag(v_a_3494_) == 1)
{
lean_object* v_val_3498_; lean_object* v_fst_3499_; lean_object* v_snd_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
lean_dec(v_a_3447_);
v_val_3498_ = lean_ctor_get(v_a_3494_, 0);
lean_inc(v_val_3498_);
lean_dec_ref_known(v_a_3494_, 1);
v_fst_3499_ = lean_ctor_get(v_val_3498_, 0);
lean_inc(v_fst_3499_);
v_snd_3500_ = lean_ctor_get(v_val_3498_, 1);
lean_inc(v_snd_3500_);
lean_dec(v_val_3498_);
v___x_3501_ = l_Lean_mkNatLit(v_snd_3500_);
v___x_3502_ = l_Lean_mkNatLit(v_fst_3499_);
v___x_3503_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__15, &l_Lean_Meta_litToCtor___closed__15_once, _init_l_Lean_Meta_litToCtor___closed__15);
v___x_3504_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__16, &l_Lean_Meta_litToCtor___closed__16_once, _init_l_Lean_Meta_litToCtor___closed__16);
v___x_3505_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__19, &l_Lean_Meta_litToCtor___closed__19_once, _init_l_Lean_Meta_litToCtor___closed__19);
lean_inc_ref_n(v___x_3502_, 2);
lean_inc_ref_n(v___x_3501_, 2);
v___x_3506_ = l_Lean_mkApp4(v___x_3503_, v___x_3504_, v___x_3505_, v___x_3501_, v___x_3502_);
v___x_3507_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__22, &l_Lean_Meta_litToCtor___closed__22_once, _init_l_Lean_Meta_litToCtor___closed__22);
v___x_3508_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__25, &l_Lean_Meta_litToCtor___closed__25_once, _init_l_Lean_Meta_litToCtor___closed__25);
v___x_3509_ = l_Lean_mkAppB(v___x_3508_, v___x_3501_, v___x_3502_);
v___x_3510_ = l_Lean_eagerReflBoolTrue;
v___x_3511_ = l_Lean_mkApp3(v___x_3507_, v___x_3506_, v___x_3509_, v___x_3510_);
v___x_3512_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__28, &l_Lean_Meta_litToCtor___closed__28_once, _init_l_Lean_Meta_litToCtor___closed__28);
v___x_3513_ = l_Lean_mkApp3(v___x_3512_, v___x_3502_, v___x_3501_, v___x_3511_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3513_);
v___x_3515_ = v___x_3496_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
else
{
lean_object* v___x_3518_; 
lean_dec(v_a_3494_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v_a_3447_);
v___x_3518_ = v___x_3496_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3447_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec(v_a_3447_);
v_a_3521_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3493_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3493_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec(v_a_3447_);
v_a_3530_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3468_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3468_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_a_3447_);
v_a_3539_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3448_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3448_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor___boxed(lean_object* v_e_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_Meta_litToCtor(v_e_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(lean_object* v_fst_3556_, lean_object* v_snd_3557_, lean_object* v_x_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3564_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0));
v___x_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3565_, 0, v_fst_3556_);
lean_ctor_set(v___x_3565_, 1, v_snd_3557_);
v___x_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_fst_3569_, lean_object* v_snd_3570_, lean_object* v_x_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3569_, v_snd_3570_, v_x_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(lean_object* v_f_3589_, lean_object* v_a_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v___y_3597_; lean_object* v_snd_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3705_; 
v_snd_3617_ = lean_ctor_get(v_a_3590_, 1);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_a_3590_);
if (v_isSharedCheck_3705_ == 0)
{
lean_object* v_unused_3706_; 
v_unused_3706_ = lean_ctor_get(v_a_3590_, 0);
lean_dec(v_unused_3706_);
v___x_3619_ = v_a_3590_;
v_isShared_3620_ = v_isSharedCheck_3705_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_snd_3617_);
lean_dec(v_a_3590_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3705_;
goto v_resetjp_3618_;
}
v___jp_3596_:
{
if (lean_obj_tag(v___y_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3608_; 
v_a_3598_ = lean_ctor_get(v___y_3597_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___y_3597_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3600_ = v___y_3597_;
v_isShared_3601_ = v_isSharedCheck_3608_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___y_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3608_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
if (lean_obj_tag(v_a_3598_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; 
lean_dec_ref(v_f_3589_);
v_a_3602_ = lean_ctor_get(v_a_3598_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v_a_3598_, 1);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v_a_3602_);
v___x_3604_ = v___x_3600_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
else
{
lean_object* v_a_3606_; 
lean_del_object(v___x_3600_);
v_a_3606_ = lean_ctor_get(v_a_3598_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v_a_3598_, 1);
v_a_3590_ = v_a_3606_;
goto _start;
}
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec_ref(v_f_3589_);
v_a_3609_ = lean_ctor_get(v___y_3597_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___y_3597_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___y_3597_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___y_3597_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
v_resetjp_3618_:
{
lean_object* v_fst_3621_; lean_object* v_snd_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3704_; 
v_fst_3621_ = lean_ctor_get(v_snd_3617_, 0);
v_snd_3622_ = lean_ctor_get(v_snd_3617_, 1);
v_isSharedCheck_3704_ = !lean_is_exclusive(v_snd_3617_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3624_ = v_snd_3617_;
v_isShared_3625_ = v_isSharedCheck_3704_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_snd_3622_);
lean_inc(v_fst_3621_);
lean_dec(v_snd_3617_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3704_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = lean_box(0);
lean_inc(v_fst_3621_);
v___x_3627_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_fst_3621_, v___y_3592_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3695_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3695_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3695_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; uint8_t v___x_3633_; 
v___x_3632_ = l_Lean_Expr_cleanupAnnotations(v_a_3628_);
lean_dec(v_a_3628_);
v___x_3633_ = l_Lean_Expr_isApp(v___x_3632_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
lean_dec_ref(v___x_3632_);
lean_del_object(v___x_3630_);
lean_del_object(v___x_3624_);
lean_del_object(v___x_3619_);
v___x_3634_ = lean_box(0);
v___x_3635_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3621_, v_snd_3622_, v___x_3634_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
v___y_3597_ = v___x_3635_;
goto v___jp_3596_;
}
else
{
lean_object* v___x_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3636_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3632_);
v___x_3637_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2));
v___x_3638_ = l_Lean_Expr_isConstOf(v___x_3636_, v___x_3637_);
if (v___x_3638_ == 0)
{
uint8_t v___x_3639_; 
lean_del_object(v___x_3630_);
v___x_3639_ = l_Lean_Expr_isApp(v___x_3636_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
lean_dec_ref(v___x_3636_);
lean_dec_ref(v___x_3632_);
lean_del_object(v___x_3624_);
lean_del_object(v___x_3619_);
v___x_3640_ = lean_box(0);
v___x_3641_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3621_, v_snd_3622_, v___x_3640_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
v___y_3597_ = v___x_3641_;
goto v___jp_3596_;
}
else
{
lean_object* v___x_3642_; uint8_t v___x_3643_; 
v___x_3642_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3636_);
v___x_3643_ = l_Lean_Expr_isApp(v___x_3642_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
lean_dec_ref(v___x_3642_);
lean_dec_ref(v___x_3636_);
lean_dec_ref(v___x_3632_);
lean_del_object(v___x_3624_);
lean_del_object(v___x_3619_);
v___x_3644_ = lean_box(0);
v___x_3645_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3621_, v_snd_3622_, v___x_3644_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
v___y_3597_ = v___x_3645_;
goto v___jp_3596_;
}
else
{
lean_object* v___x_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3646_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3642_);
lean_dec_ref(v___x_3642_);
v___x_3647_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4));
v___x_3648_ = l_Lean_Expr_isConstOf(v___x_3646_, v___x_3647_);
lean_dec_ref(v___x_3646_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
lean_dec_ref(v___x_3636_);
lean_dec_ref(v___x_3632_);
lean_del_object(v___x_3624_);
lean_del_object(v___x_3619_);
v___x_3649_ = lean_box(0);
v___x_3650_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3621_, v_snd_3622_, v___x_3649_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
v___y_3597_ = v___x_3650_;
goto v___jp_3596_;
}
else
{
lean_object* v_arg_3651_; lean_object* v_arg_3652_; lean_object* v___x_3653_; 
v_arg_3651_ = lean_ctor_get(v___x_3632_, 1);
lean_inc_ref(v_arg_3651_);
lean_dec_ref(v___x_3632_);
v_arg_3652_ = lean_ctor_get(v___x_3636_, 1);
lean_inc_ref(v_arg_3652_);
lean_dec_ref(v___x_3636_);
lean_inc_ref(v_f_3589_);
lean_inc(v___y_3594_);
lean_inc_ref(v___y_3593_);
lean_inc(v___y_3592_);
lean_inc_ref(v___y_3591_);
v___x_3653_ = lean_apply_6(v_f_3589_, v_arg_3652_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, lean_box(0));
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3677_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3656_ = v___x_3653_;
v_isShared_3657_ = v_isSharedCheck_3677_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3653_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3677_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
if (lean_obj_tag(v_a_3654_) == 1)
{
lean_object* v_val_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
lean_del_object(v___x_3656_);
lean_dec(v_fst_3621_);
v_val_3658_ = lean_ctor_get(v_a_3654_, 0);
lean_inc(v_val_3658_);
lean_dec_ref_known(v_a_3654_, 1);
v___x_3659_ = lean_array_push(v_snd_3622_, v_val_3658_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 1, v___x_3659_);
lean_ctor_set(v___x_3624_, 0, v_arg_3651_);
v___x_3661_ = v___x_3624_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_arg_3651_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3663_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3661_);
lean_ctor_set(v___x_3619_, 0, v___x_3626_);
v___x_3663_ = v___x_3619_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3626_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
v_a_3590_ = v___x_3663_;
goto _start;
}
}
}
else
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
lean_dec(v_a_3654_);
lean_dec_ref(v_arg_3651_);
lean_dec_ref(v_f_3589_);
v___x_3667_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5));
if (v_isShared_3625_ == 0)
{
v___x_3669_ = v___x_3624_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_fst_3621_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_snd_3622_);
v___x_3669_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3671_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3669_);
lean_ctor_set(v___x_3619_, 0, v___x_3667_);
v___x_3671_ = v___x_3619_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3673_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v___x_3671_);
v___x_3673_ = v___x_3656_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec_ref(v_arg_3651_);
lean_del_object(v___x_3624_);
lean_dec(v_snd_3622_);
lean_dec(v_fst_3621_);
lean_del_object(v___x_3619_);
lean_dec_ref(v_f_3589_);
v_a_3678_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3653_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3653_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3687_; 
lean_dec_ref(v___x_3636_);
lean_dec_ref(v___x_3632_);
lean_dec_ref(v_f_3589_);
if (v_isShared_3625_ == 0)
{
v___x_3687_ = v___x_3624_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_fst_3621_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_snd_3622_);
v___x_3687_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3689_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3687_);
lean_ctor_set(v___x_3619_, 0, v___x_3626_);
v___x_3689_ = v___x_3619_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3626_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3691_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3689_);
v___x_3691_ = v___x_3630_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_del_object(v___x_3624_);
lean_dec(v_snd_3622_);
lean_dec(v_fst_3621_);
lean_del_object(v___x_3619_);
lean_dec_ref(v_f_3589_);
v_a_3696_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3627_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3627_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___boxed(lean_object* v_f_3707_, lean_object* v_a_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_3707_, v_a_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg(lean_object* v_e_3717_, lean_object* v_f_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3761_; 
v___x_3724_ = l_Lean_Expr_consumeMData(v_e_3717_);
v___x_3725_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_3724_, v_a_3720_);
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3728_ = v___x_3725_;
v_isShared_3729_ = v_isSharedCheck_3761_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3725_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3761_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3730_ = ((lean_object*)(l_Lean_Meta_getListLitOf_x3f___redArg___closed__0));
v___x_3731_ = lean_box(0);
v___x_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3732_, 0, v_a_3726_);
lean_ctor_set(v___x_3732_, 1, v___x_3730_);
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_3718_, v___x_3733_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3752_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3752_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3752_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v_fst_3739_; 
v_fst_3739_ = lean_ctor_get(v_a_3735_, 0);
if (lean_obj_tag(v_fst_3739_) == 0)
{
lean_object* v_snd_3740_; lean_object* v_snd_3741_; lean_object* v___x_3743_; 
v_snd_3740_ = lean_ctor_get(v_a_3735_, 1);
lean_inc(v_snd_3740_);
lean_dec(v_a_3735_);
v_snd_3741_ = lean_ctor_get(v_snd_3740_, 1);
lean_inc(v_snd_3741_);
lean_dec(v_snd_3740_);
if (v_isShared_3729_ == 0)
{
lean_ctor_set_tag(v___x_3728_, 1);
lean_ctor_set(v___x_3728_, 0, v_snd_3741_);
v___x_3743_ = v___x_3728_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_snd_3741_);
v___x_3743_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
lean_object* v___x_3745_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v___x_3743_);
v___x_3745_ = v___x_3737_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
else
{
lean_object* v_val_3748_; lean_object* v___x_3750_; 
lean_inc_ref(v_fst_3739_);
lean_dec(v_a_3735_);
lean_del_object(v___x_3728_);
v_val_3748_ = lean_ctor_get(v_fst_3739_, 0);
lean_inc(v_val_3748_);
lean_dec_ref_known(v_fst_3739_, 1);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v_val_3748_);
v___x_3750_ = v___x_3737_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_val_3748_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_del_object(v___x_3728_);
v_a_3753_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3734_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3734_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___boxed(lean_object* v_e_3762_, lean_object* v_f_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_3762_, v_f_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec_ref(v_e_3762_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f(lean_object* v_00_u03b1_3770_, lean_object* v_e_3771_, lean_object* v_f_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_3771_, v_f_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___boxed(lean_object* v_00_u03b1_3779_, lean_object* v_e_3780_, lean_object* v_f_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lean_Meta_getListLitOf_x3f(v_00_u03b1_3779_, v_e_3780_, v_f_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_);
lean_dec(v_a_3785_);
lean_dec_ref(v_a_3784_);
lean_dec(v_a_3783_);
lean_dec_ref(v_a_3782_);
lean_dec_ref(v_e_3780_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(lean_object* v_00_u03b1_3788_, lean_object* v_f_3789_, lean_object* v_inst_3790_, lean_object* v_a_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_3789_, v_a_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___boxed(lean_object* v_00_u03b1_3798_, lean_object* v_f_3799_, lean_object* v_inst_3800_, lean_object* v_a_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(v_00_u03b1_3798_, v_f_3799_, v_inst_3800_, v_a_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0(lean_object* v_s_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3814_, 0, v_s_3808_);
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0___boxed(lean_object* v_s_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_Meta_getListLit_x3f___lam__0(v_s_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f(lean_object* v_e_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v___f_3830_; lean_object* v___x_3831_; 
v___f_3830_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_3831_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_3824_, v___f_3830_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___boxed(lean_object* v_e_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_Meta_getListLit_x3f(v_e_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
lean_dec_ref(v_e_3832_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg(lean_object* v_e_3843_, lean_object* v_f_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v_a_3855_; lean_object* v___x_3856_; 
v___x_3853_ = l_Lean_Expr_consumeMData(v_e_3843_);
v___x_3854_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_3853_, v_a_3846_);
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref(v___x_3854_);
v___x_3856_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_3855_, v_a_3846_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3856_, 1);
v___x_3858_ = l_Lean_Expr_cleanupAnnotations(v_a_3857_);
lean_dec(v_a_3857_);
v___x_3859_ = l_Lean_Expr_isApp(v___x_3858_);
if (v___x_3859_ == 0)
{
lean_dec_ref(v___x_3858_);
lean_dec_ref(v_f_3844_);
goto v___jp_3850_;
}
else
{
lean_object* v___x_3860_; uint8_t v___x_3861_; 
v___x_3860_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3858_);
v___x_3861_ = l_Lean_Expr_isApp(v___x_3860_);
if (v___x_3861_ == 0)
{
lean_dec_ref(v___x_3860_);
lean_dec_ref(v___x_3858_);
lean_dec_ref(v_f_3844_);
goto v___jp_3850_;
}
else
{
lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v___x_3862_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3860_);
lean_dec_ref(v___x_3860_);
v___x_3863_ = ((lean_object*)(l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1));
v___x_3864_ = l_Lean_Expr_isConstOf(v___x_3862_, v___x_3863_);
lean_dec_ref(v___x_3862_);
if (v___x_3864_ == 0)
{
lean_dec_ref(v___x_3858_);
lean_dec_ref(v_f_3844_);
goto v___jp_3850_;
}
else
{
lean_object* v_arg_3865_; lean_object* v___x_3866_; 
v_arg_3865_ = lean_ctor_get(v___x_3858_, 1);
lean_inc_ref(v_arg_3865_);
lean_dec_ref(v___x_3858_);
v___x_3866_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_arg_3865_, v_f_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
lean_dec_ref(v_arg_3865_);
return v___x_3866_;
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_dec_ref(v_f_3844_);
v_a_3867_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3856_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3856_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
v___jp_3850_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = lean_box(0);
v___x_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3851_);
return v___x_3852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___boxed(lean_object* v_e_3875_, lean_object* v_f_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_3875_, v_f_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
lean_dec(v_a_3878_);
lean_dec_ref(v_a_3877_);
lean_dec_ref(v_e_3875_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f(lean_object* v_00_u03b1_3883_, lean_object* v_e_3884_, lean_object* v_f_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_3884_, v_f_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___boxed(lean_object* v_00_u03b1_3892_, lean_object* v_e_3893_, lean_object* v_f_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_Meta_getArrayLitOf_x3f(v_00_u03b1_3892_, v_e_3893_, v_f_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_);
lean_dec(v_a_3898_);
lean_dec_ref(v_a_3897_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec_ref(v_e_3893_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object* v_e_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v___f_3907_; lean_object* v___x_3908_; 
v___f_3907_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_3908_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_3901_, v___f_3907_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f___boxed(lean_object* v_e_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Meta_getArrayLit_x3f(v_e_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec_ref(v_e_3909_);
return v_res_3915_;
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
