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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rat"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1_value;
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
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1))}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getLitValueModulus_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(65536) << 1) | 1))}};
static const lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getLitValueModulus_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_getLitValueModulus_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__2;
static lean_once_cell_t l_Lean_Meta_getLitValueModulus_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__3;
static lean_once_cell_t l_Lean_Meta_getLitValueModulus_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getLitValueModulus_x3f___closed__4;
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
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 69, 114, 85, 163, 177, 220, 67)}};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "OfScientific"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ofScientific"};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 219, 72, 84, 44, 38, 226, 47)}};
static const lean_ctor_object l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 32, 126, 239, 82, 155, 222, 105)}};
static const lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__4_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_21_, v_a_24_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_86_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_86_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_86_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_86_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_41_ = l_Lean_Expr_cleanupAnnotations(v_a_32_);
v___x_42_ = l_Lean_Expr_isApp(v___x_41_);
if (v___x_42_ == 0)
{
lean_dec_ref(v___x_41_);
goto v___jp_36_;
}
else
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = l_Lean_Expr_appFnCleanup___redArg(v___x_41_);
v___x_44_ = l_Lean_Expr_isApp(v___x_43_);
if (v___x_44_ == 0)
{
lean_dec_ref(v___x_43_);
goto v___jp_36_;
}
else
{
lean_object* v_arg_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v_arg_45_ = lean_ctor_get(v___x_43_, 1);
lean_inc_ref(v_arg_45_);
v___x_46_ = l_Lean_Expr_appFnCleanup___redArg(v___x_43_);
v___x_47_ = l_Lean_Expr_isApp(v___x_46_);
if (v___x_47_ == 0)
{
lean_dec_ref(v___x_46_);
lean_dec_ref(v_arg_45_);
goto v___jp_36_;
}
else
{
lean_object* v_arg_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_arg_48_ = lean_ctor_get(v___x_46_, 1);
lean_inc_ref(v_arg_48_);
v___x_49_ = l_Lean_Expr_appFnCleanup___redArg(v___x_46_);
v___x_50_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_51_ = l_Lean_Expr_isConstOf(v___x_49_, v___x_50_);
lean_dec_ref(v___x_49_);
if (v___x_51_ == 0)
{
lean_dec_ref(v_arg_48_);
lean_dec_ref(v_arg_45_);
goto v___jp_36_;
}
else
{
lean_object* v___x_52_; 
lean_del_object(v___x_34_);
v___x_52_ = l_Lean_Meta_whnfD(v_arg_48_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_77_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_77_ == 0)
{
v___x_55_ = v___x_52_;
v_isShared_56_ = v_isSharedCheck_77_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_52_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_77_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = l_Lean_Expr_getAppFn(v_a_53_);
v___x_58_ = l_Lean_Expr_isConstOf(v___x_57_, v_typeDeclName_22_);
lean_dec_ref(v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_61_; 
lean_dec(v_a_53_);
lean_dec_ref(v_arg_45_);
v___x_59_ = lean_box(0);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_59_);
v___x_61_ = v___x_55_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_59_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
else
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Expr_consumeMData(v_arg_45_);
lean_dec_ref(v_arg_45_);
if (lean_obj_tag(v___x_63_) == 9)
{
lean_object* v_a_64_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc_ref(v_a_64_);
lean_dec_ref_known(v___x_63_, 1);
if (lean_obj_tag(v_a_64_) == 0)
{
lean_object* v_val_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_76_; 
v_val_65_ = lean_ctor_get(v_a_64_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_76_ == 0)
{
v___x_67_ = v_a_64_;
v_isShared_68_ = v_isSharedCheck_76_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_val_65_);
lean_dec(v_a_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_76_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v_val_65_);
lean_ctor_set(v___x_69_, 1, v_a_53_);
if (v_isShared_68_ == 0)
{
lean_ctor_set_tag(v___x_67_, 1);
lean_ctor_set(v___x_67_, 0, v___x_69_);
v___x_71_ = v___x_67_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_75_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_73_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_71_);
v___x_73_ = v___x_55_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_dec_ref(v_a_64_);
lean_del_object(v___x_55_);
lean_dec(v_a_53_);
goto v___jp_28_;
}
}
else
{
lean_dec_ref(v___x_63_);
lean_del_object(v___x_55_);
lean_dec(v_a_53_);
goto v___jp_28_;
}
}
}
}
else
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
lean_dec_ref(v_arg_45_);
v_a_78_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_52_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_52_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
}
}
v___jp_36_:
{
lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_37_ = lean_box(0);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 0, v___x_37_);
v___x_39_ = v___x_34_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_37_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_a_87_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_31_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_31_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f___boxed(lean_object* v_e_95_, lean_object* v_typeDeclName_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Meta_getOfNatValue_x3f(v_e_95_, v_typeDeclName_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_typeDeclName_96_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getNatValue_x3f(lean_object* v_e_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_e_112_; lean_object* v___x_113_; 
v_e_112_ = l_Lean_Expr_consumeMData(v_e_106_);
v___x_113_ = l_Lean_Meta_getRawNatValue_x3f(v_e_112_);
if (lean_obj_tag(v___x_113_) == 1)
{
lean_object* v___x_114_; 
lean_dec_ref(v_e_112_);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; 
lean_dec(v___x_113_);
v___x_115_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_116_ = l_Lean_Meta_getOfNatValue_x3f(v_e_112_, v___x_115_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_137_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_137_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_137_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_137_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
if (lean_obj_tag(v_a_117_) == 1)
{
lean_object* v_val_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_132_; 
v_val_121_ = lean_ctor_get(v_a_117_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_a_117_);
if (v_isSharedCheck_132_ == 0)
{
v___x_123_ = v_a_117_;
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_val_121_);
lean_dec(v_a_117_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_fst_125_; lean_object* v___x_127_; 
v_fst_125_ = lean_ctor_get(v_val_121_, 0);
lean_inc(v_fst_125_);
lean_dec(v_val_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v_fst_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_fst_125_);
v___x_127_ = v_reuseFailAlloc_131_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_127_);
v___x_129_ = v___x_119_;
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
lean_object* v___x_133_; lean_object* v___x_135_; 
lean_dec(v_a_117_);
v___x_133_ = lean_box(0);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_133_);
v___x_135_ = v___x_119_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_116_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_116_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getNatValue_x3f___boxed(lean_object* v_e_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Meta_getNatValue_x3f(v_e_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec_ref(v_e_146_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_getIntValue_x3f_spec__0(lean_object* v_a_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_nat_to_int(v_a_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntValue_x3f(lean_object* v_e_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
lean_inc_ref(v_e_163_);
v___x_170_ = l_Lean_Meta_getOfNatValue_x3f(v_e_163_, v___x_169_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_249_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_249_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_249_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_249_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
if (lean_obj_tag(v_a_171_) == 1)
{
lean_object* v_val_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_187_; 
lean_dec_ref(v_e_163_);
v_val_175_ = lean_ctor_get(v_a_171_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v_a_171_);
if (v_isSharedCheck_187_ == 0)
{
v___x_177_ = v_a_171_;
v_isShared_178_ = v_isSharedCheck_187_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_val_175_);
lean_dec(v_a_171_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_187_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_fst_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v_fst_179_ = lean_ctor_get(v_val_175_, 0);
lean_inc(v_fst_179_);
lean_dec(v_val_175_);
v___x_180_ = lean_nat_to_int(v_fst_179_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_180_);
v___x_182_ = v___x_177_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_186_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_182_);
v___x_184_ = v___x_173_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_object* v___x_188_; 
lean_del_object(v___x_173_);
lean_dec(v_a_171_);
v___x_188_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_163_, v_a_165_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_240_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_240_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_240_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_240_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = l_Lean_Expr_cleanupAnnotations(v_a_189_);
v___x_199_ = l_Lean_Expr_isApp(v___x_198_);
if (v___x_199_ == 0)
{
lean_dec_ref(v___x_198_);
goto v___jp_193_;
}
else
{
lean_object* v_arg_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_arg_200_ = lean_ctor_get(v___x_198_, 1);
lean_inc_ref(v_arg_200_);
v___x_201_ = l_Lean_Expr_appFnCleanup___redArg(v___x_198_);
v___x_202_ = l_Lean_Expr_isApp(v___x_201_);
if (v___x_202_ == 0)
{
lean_dec_ref(v___x_201_);
lean_dec_ref(v_arg_200_);
goto v___jp_193_;
}
else
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = l_Lean_Expr_appFnCleanup___redArg(v___x_201_);
v___x_204_ = l_Lean_Expr_isApp(v___x_203_);
if (v___x_204_ == 0)
{
lean_dec_ref(v___x_203_);
lean_dec_ref(v_arg_200_);
goto v___jp_193_;
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_205_ = l_Lean_Expr_appFnCleanup___redArg(v___x_203_);
v___x_206_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_207_ = l_Lean_Expr_isConstOf(v___x_205_, v___x_206_);
lean_dec_ref(v___x_205_);
if (v___x_207_ == 0)
{
lean_dec_ref(v_arg_200_);
goto v___jp_193_;
}
else
{
lean_object* v___x_208_; 
lean_del_object(v___x_191_);
v___x_208_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_200_, v___x_169_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_231_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_231_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_231_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_231_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
if (lean_obj_tag(v_a_209_) == 1)
{
lean_object* v_val_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_226_; 
v_val_213_ = lean_ctor_get(v_a_209_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v_a_209_);
if (v_isSharedCheck_226_ == 0)
{
v___x_215_ = v_a_209_;
v_isShared_216_ = v_isSharedCheck_226_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_val_213_);
lean_dec(v_a_209_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_226_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_fst_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v_fst_217_ = lean_ctor_get(v_val_213_, 0);
lean_inc(v_fst_217_);
lean_dec(v_val_213_);
v___x_218_ = lean_nat_to_int(v_fst_217_);
v___x_219_ = lean_int_neg(v___x_218_);
lean_dec(v___x_218_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_219_);
v___x_221_ = v___x_215_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_225_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_221_);
v___x_223_ = v___x_211_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_229_; 
lean_dec(v_a_209_);
v___x_227_ = lean_box(0);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_227_);
v___x_229_ = v___x_211_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_a_232_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_208_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_208_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
}
}
v___jp_193_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_box(0);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_194_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
v_a_241_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_188_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_188_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec_ref(v_e_163_);
v_a_250_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_170_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_170_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getIntValue_x3f___boxed(lean_object* v_e_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Meta_getIntValue_x3f(v_e_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(lean_object* v_a_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_nat_to_int(v_a_265_);
v___x_267_ = l_Rat_ofInt(v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(lean_object* v_e_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1));
lean_inc_ref(v_e_271_);
v___x_278_ = l_Lean_Meta_getOfNatValue_x3f(v_e_271_, v___x_277_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_357_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_357_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_357_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_357_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
if (lean_obj_tag(v_a_279_) == 1)
{
lean_object* v_val_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_295_; 
lean_dec_ref(v_e_271_);
v_val_283_ = lean_ctor_get(v_a_279_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_a_279_);
if (v_isSharedCheck_295_ == 0)
{
v___x_285_ = v_a_279_;
v_isShared_286_ = v_isSharedCheck_295_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_val_283_);
lean_dec(v_a_279_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_295_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_fst_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v_fst_287_ = lean_ctor_get(v_val_283_, 0);
lean_inc(v_fst_287_);
lean_dec(v_val_283_);
v___x_288_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(v_fst_287_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_288_);
v___x_290_ = v___x_285_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_294_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_292_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_290_);
v___x_292_ = v___x_281_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_object* v___x_296_; 
lean_del_object(v___x_281_);
lean_dec(v_a_279_);
v___x_296_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_271_, v_a_273_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_348_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_348_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_348_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_348_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = l_Lean_Expr_cleanupAnnotations(v_a_297_);
v___x_307_ = l_Lean_Expr_isApp(v___x_306_);
if (v___x_307_ == 0)
{
lean_dec_ref(v___x_306_);
goto v___jp_301_;
}
else
{
lean_object* v_arg_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_arg_308_ = lean_ctor_get(v___x_306_, 1);
lean_inc_ref(v_arg_308_);
v___x_309_ = l_Lean_Expr_appFnCleanup___redArg(v___x_306_);
v___x_310_ = l_Lean_Expr_isApp(v___x_309_);
if (v___x_310_ == 0)
{
lean_dec_ref(v___x_309_);
lean_dec_ref(v_arg_308_);
goto v___jp_301_;
}
else
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = l_Lean_Expr_appFnCleanup___redArg(v___x_309_);
v___x_312_ = l_Lean_Expr_isApp(v___x_311_);
if (v___x_312_ == 0)
{
lean_dec_ref(v___x_311_);
lean_dec_ref(v_arg_308_);
goto v___jp_301_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = l_Lean_Expr_appFnCleanup___redArg(v___x_311_);
v___x_314_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_315_ = l_Lean_Expr_isConstOf(v___x_313_, v___x_314_);
lean_dec_ref(v___x_313_);
if (v___x_315_ == 0)
{
lean_dec_ref(v_arg_308_);
goto v___jp_301_;
}
else
{
lean_object* v___x_316_; 
lean_del_object(v___x_299_);
v___x_316_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_308_, v___x_277_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_339_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_339_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
if (lean_obj_tag(v_a_317_) == 1)
{
lean_object* v_val_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_334_; 
v_val_321_ = lean_ctor_get(v_a_317_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_a_317_);
if (v_isSharedCheck_334_ == 0)
{
v___x_323_ = v_a_317_;
v_isShared_324_ = v_isSharedCheck_334_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_val_321_);
lean_dec(v_a_317_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_334_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_fst_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v_fst_325_ = lean_ctor_get(v_val_321_, 0);
lean_inc(v_fst_325_);
lean_dec(v_val_321_);
v___x_326_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(v_fst_325_);
v___x_327_ = l_Rat_neg(v___x_326_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_327_);
v___x_329_ = v___x_323_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_333_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_331_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_329_);
v___x_331_ = v___x_319_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_337_; 
lean_dec(v_a_317_);
v___x_335_ = lean_box(0);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_335_);
v___x_337_ = v___x_319_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_a_340_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_316_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_316_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
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
}
}
v___jp_301_:
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = lean_box(0);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
v_a_349_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_296_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_296_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v_e_271_);
v_a_358_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_278_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_278_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___boxed(lean_object* v_e_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getRatValue_x3f(lean_object* v_e_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; 
lean_inc_ref(v_e_378_);
v___x_384_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_378_, v_a_380_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = l_Lean_Expr_cleanupAnnotations(v_a_385_);
v___x_387_ = l_Lean_Expr_isApp(v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec_ref(v___x_386_);
v___x_388_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_388_;
}
else
{
lean_object* v_arg_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v_arg_389_ = lean_ctor_get(v___x_386_, 1);
lean_inc_ref(v_arg_389_);
v___x_390_ = l_Lean_Expr_appFnCleanup___redArg(v___x_386_);
v___x_391_ = l_Lean_Expr_isApp(v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
lean_dec_ref(v___x_390_);
lean_dec_ref(v_arg_389_);
v___x_392_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_392_;
}
else
{
lean_object* v_arg_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_arg_393_ = lean_ctor_get(v___x_390_, 1);
lean_inc_ref(v_arg_393_);
v___x_394_ = l_Lean_Expr_appFnCleanup___redArg(v___x_390_);
v___x_395_ = l_Lean_Expr_isApp(v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
lean_dec_ref(v___x_394_);
lean_dec_ref(v_arg_393_);
lean_dec_ref(v_arg_389_);
v___x_396_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = l_Lean_Expr_appFnCleanup___redArg(v___x_394_);
v___x_398_ = l_Lean_Expr_isApp(v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec_ref(v___x_397_);
lean_dec_ref(v_arg_393_);
lean_dec_ref(v_arg_389_);
v___x_399_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_399_;
}
else
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = l_Lean_Expr_appFnCleanup___redArg(v___x_397_);
v___x_401_ = l_Lean_Expr_isApp(v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec_ref(v___x_400_);
lean_dec_ref(v_arg_393_);
lean_dec_ref(v_arg_389_);
v___x_402_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = l_Lean_Expr_appFnCleanup___redArg(v___x_400_);
v___x_404_ = l_Lean_Expr_isApp(v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_dec_ref(v___x_403_);
lean_dec_ref(v_arg_393_);
lean_dec_ref(v_arg_389_);
v___x_405_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_405_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_403_);
v___x_407_ = ((lean_object*)(l_Lean_Meta_getRatValue_x3f___closed__2));
v___x_408_ = l_Lean_Expr_isConstOf(v___x_406_, v___x_407_);
lean_dec_ref(v___x_406_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_dec_ref(v_arg_393_);
lean_dec_ref(v_arg_389_);
v___x_409_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; 
lean_dec_ref(v_e_378_);
v___x_410_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_arg_393_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_453_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_453_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_453_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_453_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
if (lean_obj_tag(v_a_411_) == 1)
{
lean_object* v_val_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_del_object(v___x_413_);
v_val_415_ = lean_ctor_get(v_a_411_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v_a_411_, 1);
v___x_416_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1));
v___x_417_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_389_, v___x_416_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_440_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_440_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_440_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_440_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
if (lean_obj_tag(v_a_418_) == 1)
{
lean_object* v_val_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_435_; 
v_val_422_ = lean_ctor_get(v_a_418_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_a_418_);
if (v_isSharedCheck_435_ == 0)
{
v___x_424_ = v_a_418_;
v_isShared_425_ = v_isSharedCheck_435_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_val_422_);
lean_dec(v_a_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_435_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_fst_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v_fst_426_ = lean_ctor_get(v_val_422_, 0);
lean_inc(v_fst_426_);
lean_dec(v_val_422_);
v___x_427_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(v_fst_426_);
v___x_428_ = l_Rat_div(v_val_415_, v___x_427_);
lean_dec(v_val_415_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_428_);
v___x_430_ = v___x_424_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_434_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_432_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_430_);
v___x_432_ = v___x_420_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_object* v___x_436_; lean_object* v___x_438_; 
lean_dec(v_a_418_);
lean_dec(v_val_415_);
v___x_436_ = lean_box(0);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_436_);
v___x_438_ = v___x_420_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec(v_val_415_);
v_a_441_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_417_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_417_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v___x_449_; lean_object* v___x_451_; 
lean_dec(v_a_411_);
lean_dec_ref(v_arg_389_);
v___x_449_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_449_);
v___x_451_ = v___x_413_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_dec_ref(v_arg_389_);
return v___x_410_;
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
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec_ref(v_e_378_);
v_a_454_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_384_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_384_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getRatValue_x3f___boxed(lean_object* v_e_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Meta_getRatValue_x3f(v_e_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f(lean_object* v_e_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_473_, v_a_475_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_526_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_526_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_526_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_526_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = l_Lean_Expr_cleanupAnnotations(v_a_480_);
v___x_490_ = l_Lean_Expr_isApp(v___x_489_);
if (v___x_490_ == 0)
{
lean_dec_ref(v___x_489_);
goto v___jp_484_;
}
else
{
lean_object* v_arg_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_arg_491_ = lean_ctor_get(v___x_489_, 1);
lean_inc_ref(v_arg_491_);
v___x_492_ = l_Lean_Expr_appFnCleanup___redArg(v___x_489_);
v___x_493_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_494_ = l_Lean_Expr_isConstOf(v___x_492_, v___x_493_);
lean_dec_ref(v___x_492_);
if (v___x_494_ == 0)
{
lean_dec_ref(v_arg_491_);
goto v___jp_484_;
}
else
{
lean_object* v___x_495_; 
lean_del_object(v___x_482_);
v___x_495_ = l_Lean_Meta_getNatValue_x3f(v_arg_491_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
lean_dec_ref(v_arg_491_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_517_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_517_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_517_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_517_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
if (lean_obj_tag(v_a_496_) == 1)
{
lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_512_; 
v_val_500_ = lean_ctor_get(v_a_496_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v_a_496_);
if (v_isSharedCheck_512_ == 0)
{
v___x_502_ = v_a_496_;
v_isShared_503_ = v_isSharedCheck_512_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_dec(v_a_496_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_512_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
uint32_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = l_Char_ofNat(v_val_500_);
lean_dec(v_val_500_);
v___x_505_ = lean_box_uint32(v___x_504_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_507_);
v___x_509_ = v___x_498_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v___x_513_; lean_object* v___x_515_; 
lean_dec(v_a_496_);
v___x_513_ = lean_box(0);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_513_);
v___x_515_ = v___x_498_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
v_a_518_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_495_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_495_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
v___jp_484_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = lean_box(0);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_485_);
v___x_487_ = v___x_482_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_a_527_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_479_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_479_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f___boxed(lean_object* v_e_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Meta_getCharValue_x3f(v_e_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStringValue_x3f(lean_object* v_e_542_){
_start:
{
if (lean_obj_tag(v_e_542_) == 9)
{
lean_object* v_a_543_; 
v_a_543_ = lean_ctor_get(v_e_542_, 0);
lean_inc_ref(v_a_543_);
lean_dec_ref_known(v_e_542_, 1);
if (lean_obj_tag(v_a_543_) == 1)
{
lean_object* v_val_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_val_544_ = lean_ctor_get(v_a_543_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v_a_543_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_val_544_);
lean_dec(v_a_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_val_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v___x_552_; 
lean_dec_ref(v_a_543_);
v___x_552_ = lean_box(0);
return v___x_552_;
}
}
else
{
lean_object* v___x_553_; 
lean_dec_ref(v_e_542_);
v___x_553_ = lean_box(0);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f(lean_object* v_e_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_564_ = l_Lean_Meta_getOfNatValue_x3f(v_e_557_, v___x_563_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_633_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_633_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_633_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_633_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
if (lean_obj_tag(v_a_565_) == 0)
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_box(0);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
else
{
lean_object* v_val_573_; lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_632_; 
lean_del_object(v___x_567_);
v_val_573_ = lean_ctor_get(v_a_565_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v_a_565_, 1);
v_fst_574_ = lean_ctor_get(v_val_573_, 0);
v_snd_575_ = lean_ctor_get(v_val_573_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_val_573_);
if (v_isSharedCheck_632_ == 0)
{
v___x_577_ = v_val_573_;
v_isShared_578_ = v_isSharedCheck_632_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_snd_575_);
lean_inc(v_fst_574_);
lean_dec(v_val_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_632_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = l_Lean_Expr_appArg_x21(v_snd_575_);
lean_dec(v_snd_575_);
v___x_580_ = l_Lean_Meta_whnfD(v___x_579_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = l_Lean_Meta_getNatValue_x3f(v_a_581_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec(v_a_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_615_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_615_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_615_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_615_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
if (lean_obj_tag(v_a_583_) == 0)
{
lean_object* v___x_587_; lean_object* v___x_589_; 
lean_del_object(v___x_577_);
lean_dec(v_fst_574_);
v___x_587_ = lean_box(0);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_587_);
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
lean_object* v_val_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_val_591_ = lean_ctor_get(v_a_583_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_a_583_);
if (v_isSharedCheck_614_ == 0)
{
v___x_593_ = v_a_583_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_val_591_);
lean_dec(v_a_583_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_zero_595_; uint8_t v_isZero_596_; 
v_zero_595_ = lean_unsigned_to_nat(0u);
v_isZero_596_ = lean_nat_dec_eq(v_val_591_, v_zero_595_);
if (v_isZero_596_ == 1)
{
lean_object* v___x_597_; lean_object* v___x_599_; 
lean_del_object(v___x_593_);
lean_dec(v_val_591_);
lean_del_object(v___x_577_);
lean_dec(v_fst_574_);
v___x_597_ = lean_box(0);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_597_);
v___x_599_ = v___x_585_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_object* v_one_601_; lean_object* v_n_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v_one_601_ = lean_unsigned_to_nat(1u);
v_n_602_ = lean_nat_sub(v_val_591_, v_one_601_);
lean_dec(v_val_591_);
v___x_603_ = lean_nat_add(v_n_602_, v_one_601_);
lean_dec(v_n_602_);
v___x_604_ = lean_nat_mod(v_fst_574_, v___x_603_);
lean_dec(v_fst_574_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v___x_604_);
lean_ctor_set(v___x_577_, 0, v___x_603_);
v___x_606_ = v___x_577_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_604_);
v___x_606_ = v_reuseFailAlloc_613_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_606_);
v___x_608_ = v___x_593_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_608_);
v___x_610_ = v___x_585_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
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
lean_del_object(v___x_577_);
lean_dec(v_fst_574_);
v_a_616_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_582_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_582_);
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
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_del_object(v___x_577_);
lean_dec(v_fst_574_);
v_a_624_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_580_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_580_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
v_a_634_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_564_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_564_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f___boxed(lean_object* v_e_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_Meta_getFinValue_x3f(v_e_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object* v_e_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_nExpr_666_; lean_object* v_vExpr_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___x_722_; 
lean_inc_ref(v_e_659_);
v___x_722_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_659_, v_a_661_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v___x_799_ = l_Lean_Expr_cleanupAnnotations(v_a_723_);
v___x_800_ = l_Lean_Expr_isApp(v___x_799_);
if (v___x_800_ == 0)
{
lean_dec_ref(v___x_799_);
v___y_725_ = v_a_660_;
v___y_726_ = v_a_661_;
v___y_727_ = v_a_662_;
v___y_728_ = v_a_663_;
goto v___jp_724_;
}
else
{
lean_object* v_arg_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_arg_801_ = lean_ctor_get(v___x_799_, 1);
lean_inc_ref(v_arg_801_);
v___x_802_ = l_Lean_Expr_appFnCleanup___redArg(v___x_799_);
v___x_803_ = l_Lean_Expr_isApp(v___x_802_);
if (v___x_803_ == 0)
{
lean_dec_ref(v___x_802_);
lean_dec_ref(v_arg_801_);
v___y_725_ = v_a_660_;
v___y_726_ = v_a_661_;
v___y_727_ = v_a_662_;
v___y_728_ = v_a_663_;
goto v___jp_724_;
}
else
{
lean_object* v_arg_804_; lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_arg_804_ = lean_ctor_get(v___x_802_, 1);
lean_inc_ref(v_arg_804_);
v___x_805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_802_);
v___x_806_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_807_ = l_Lean_Expr_isConstOf(v___x_805_, v___x_806_);
if (v___x_807_ == 0)
{
uint8_t v___x_808_; 
lean_dec_ref(v_arg_801_);
v___x_808_ = l_Lean_Expr_isApp(v___x_805_);
if (v___x_808_ == 0)
{
lean_dec_ref(v___x_805_);
lean_dec_ref(v_arg_804_);
v___y_725_ = v_a_660_;
v___y_726_ = v_a_661_;
v___y_727_ = v_a_662_;
v___y_728_ = v_a_663_;
goto v___jp_724_;
}
else
{
lean_object* v_arg_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_arg_809_ = lean_ctor_get(v___x_805_, 1);
lean_inc_ref(v_arg_809_);
v___x_810_ = l_Lean_Expr_appFnCleanup___redArg(v___x_805_);
v___x_811_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__4));
v___x_812_ = l_Lean_Expr_isConstOf(v___x_810_, v___x_811_);
lean_dec_ref(v___x_810_);
if (v___x_812_ == 0)
{
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_804_);
v___y_725_ = v_a_660_;
v___y_726_ = v_a_661_;
v___y_727_ = v_a_662_;
v___y_728_ = v_a_663_;
goto v___jp_724_;
}
else
{
lean_dec_ref(v_e_659_);
v_nExpr_666_ = v_arg_809_;
v_vExpr_667_ = v_arg_804_;
v___y_668_ = v_a_660_;
v___y_669_ = v_a_661_;
v___y_670_ = v_a_662_;
v___y_671_ = v_a_663_;
goto v___jp_665_;
}
}
}
else
{
lean_dec_ref(v___x_805_);
lean_dec_ref(v_e_659_);
v_nExpr_666_ = v_arg_804_;
v_vExpr_667_ = v_arg_801_;
v___y_668_ = v_a_660_;
v___y_669_ = v_a_661_;
v___y_670_ = v_a_662_;
v___y_671_ = v_a_663_;
goto v___jp_665_;
}
}
}
v___jp_724_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_730_ = l_Lean_Meta_getOfNatValue_x3f(v_e_659_, v___x_729_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_790_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_790_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_790_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_790_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
if (lean_obj_tag(v_a_731_) == 0)
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = lean_box(0);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v_val_739_; lean_object* v_fst_740_; lean_object* v_snd_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_789_; 
lean_del_object(v___x_733_);
v_val_739_ = lean_ctor_get(v_a_731_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v_a_731_, 1);
v_fst_740_ = lean_ctor_get(v_val_739_, 0);
v_snd_741_ = lean_ctor_get(v_val_739_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_val_739_);
if (v_isSharedCheck_789_ == 0)
{
v___x_743_ = v_val_739_;
v_isShared_744_ = v_isSharedCheck_789_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_snd_741_);
lean_inc(v_fst_740_);
lean_dec(v_val_739_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_789_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = l_Lean_Expr_appArg_x21(v_snd_741_);
lean_dec(v_snd_741_);
v___x_746_ = l_Lean_Meta_whnfD(v___x_745_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = l_Lean_Meta_getNatValue_x3f(v_a_747_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v_a_747_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_772_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_772_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_772_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_772_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
if (lean_obj_tag(v_a_749_) == 0)
{
lean_object* v___x_753_; lean_object* v___x_755_; 
lean_del_object(v___x_743_);
lean_dec(v_fst_740_);
v___x_753_ = lean_box(0);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_753_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
else
{
lean_object* v_val_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_771_; 
v_val_757_ = lean_ctor_get(v_a_749_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_a_749_);
if (v_isSharedCheck_771_ == 0)
{
v___x_759_ = v_a_749_;
v_isShared_760_ = v_isSharedCheck_771_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_val_757_);
lean_dec(v_a_749_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_771_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = l_BitVec_ofNat(v_val_757_, v_fst_740_);
lean_dec(v_fst_740_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_761_);
lean_ctor_set(v___x_743_, 0, v_val_757_);
v___x_763_ = v___x_743_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_val_757_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_761_);
v___x_763_ = v_reuseFailAlloc_770_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_765_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_763_);
v___x_765_ = v___x_759_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_765_);
v___x_767_ = v___x_751_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_del_object(v___x_743_);
lean_dec(v_fst_740_);
v_a_773_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_748_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_748_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_del_object(v___x_743_);
lean_dec(v_fst_740_);
v_a_781_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_746_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_746_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_a_791_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_730_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_730_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v_e_659_);
v_a_813_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_722_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_722_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
v___jp_665_:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Meta_getNatValue_x3f(v_nExpr_666_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec_ref(v_nExpr_666_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_713_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_713_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_713_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_713_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
if (lean_obj_tag(v_a_673_) == 0)
{
lean_object* v___x_677_; lean_object* v___x_679_; 
lean_dec_ref(v_vExpr_667_);
v___x_677_ = lean_box(0);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
else
{
lean_object* v_val_681_; lean_object* v___x_682_; 
lean_del_object(v___x_675_);
v_val_681_ = lean_ctor_get(v_a_673_, 0);
lean_inc(v_val_681_);
lean_dec_ref_known(v_a_673_, 1);
v___x_682_ = l_Lean_Meta_getNatValue_x3f(v_vExpr_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec_ref(v_vExpr_667_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_704_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_704_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_704_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_704_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
if (lean_obj_tag(v_a_683_) == 0)
{
lean_object* v___x_687_; lean_object* v___x_689_; 
lean_dec(v_val_681_);
v___x_687_ = lean_box(0);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
else
{
lean_object* v_val_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_703_; 
v_val_691_ = lean_ctor_get(v_a_683_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v_a_683_);
if (v_isSharedCheck_703_ == 0)
{
v___x_693_ = v_a_683_;
v_isShared_694_ = v_isSharedCheck_703_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_val_691_);
lean_dec(v_a_683_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_703_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_695_ = l_BitVec_ofNat(v_val_681_, v_val_691_);
lean_dec(v_val_691_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_val_681_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_696_);
v___x_698_ = v___x_693_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_698_);
v___x_700_ = v___x_685_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
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
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_val_681_);
v_a_705_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_682_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_682_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_vExpr_667_);
v_a_714_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_672_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_672_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f___boxed(lean_object* v_e_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_Meta_getBitVecValue_x3f(v_e_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
return v_res_827_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__2(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_cstr_to_nat("4294967296");
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__3(void){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = lean_cstr_to_nat("18446744073709551616");
return v___x_834_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__4(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__3, &l_Lean_Meta_getLitValueModulus_x3f___closed__3_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__3);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLitValueModulus_x3f(lean_object* v_00_u03b1_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03b1_861_, v_a_863_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_937_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_937_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_937_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_937_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_889_ = l_Lean_Expr_cleanupAnnotations(v_a_880_);
v___x_890_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_891_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_893_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_895_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_897_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_899_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; uint8_t v___x_901_; 
lean_del_object(v___x_882_);
v___x_900_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_901_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_903_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_905_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_904_);
if (v___x_905_ == 0)
{
uint8_t v___x_906_; 
v___x_906_ = l_Lean_Expr_isApp(v___x_889_);
if (v___x_906_ == 0)
{
lean_dec_ref(v___x_889_);
goto v___jp_867_;
}
else
{
lean_object* v_arg_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_arg_907_ = lean_ctor_get(v___x_889_, 1);
lean_inc_ref(v_arg_907_);
v___x_908_ = l_Lean_Expr_appFnCleanup___redArg(v___x_889_);
v___x_909_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_910_ = l_Lean_Expr_isConstOf(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_912_ = l_Lean_Expr_isConstOf(v___x_908_, v___x_911_);
lean_dec_ref(v___x_908_);
if (v___x_912_ == 0)
{
lean_dec_ref(v_arg_907_);
goto v___jp_867_;
}
else
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_Meta_getNatValue_x3f(v_arg_907_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec_ref(v_arg_907_);
return v___x_913_;
}
}
else
{
lean_object* v___x_914_; 
lean_dec_ref(v___x_908_);
v___x_914_ = l_Lean_Meta_getNatValue_x3f(v_arg_907_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec_ref(v_arg_907_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_936_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_936_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_936_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_936_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
if (lean_obj_tag(v_a_915_) == 1)
{
lean_object* v_val_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_931_; 
v_val_919_ = lean_ctor_get(v_a_915_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v_a_915_);
if (v_isSharedCheck_931_ == 0)
{
v___x_921_ = v_a_915_;
v_isShared_922_ = v_isSharedCheck_931_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_val_919_);
lean_dec(v_a_915_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_931_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_923_ = lean_unsigned_to_nat(2u);
v___x_924_ = lean_nat_pow(v___x_923_, v_val_919_);
lean_dec(v_val_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_924_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_928_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_926_);
v___x_928_ = v___x_917_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
else
{
lean_object* v___x_932_; lean_object* v___x_934_; 
lean_dec(v_a_915_);
v___x_932_ = lean_box(0);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_932_);
v___x_934_ = v___x_917_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
return v___x_914_;
}
}
}
}
else
{
lean_dec_ref(v___x_889_);
goto v___jp_870_;
}
}
else
{
lean_dec_ref(v___x_889_);
goto v___jp_873_;
}
}
else
{
lean_dec_ref(v___x_889_);
goto v___jp_876_;
}
}
else
{
lean_dec_ref(v___x_889_);
goto v___jp_884_;
}
}
else
{
lean_dec_ref(v___x_889_);
lean_del_object(v___x_882_);
goto v___jp_870_;
}
}
else
{
lean_dec_ref(v___x_889_);
lean_del_object(v___x_882_);
goto v___jp_873_;
}
}
else
{
lean_dec_ref(v___x_889_);
lean_del_object(v___x_882_);
goto v___jp_876_;
}
}
else
{
lean_dec_ref(v___x_889_);
goto v___jp_884_;
}
v___jp_884_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__4, &l_Lean_Meta_getLitValueModulus_x3f___closed__4_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__4);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_885_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
v_a_938_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_879_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_879_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
v___jp_867_:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_box(0);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
v___jp_870_:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__0));
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
v___jp_873_:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__1));
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
v___jp_876_:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__2, &l_Lean_Meta_getLitValueModulus_x3f___closed__2_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__2);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLitValueModulus_x3f___boxed(lean_object* v_00_u03b1_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Meta_getLitValueModulus_x3f(v_00_u03b1_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object* v_e_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_960_ = l_Lean_Meta_getOfNatValue_x3f(v_e_953_, v___x_959_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_983_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_983_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_983_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_983_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
if (lean_obj_tag(v_a_961_) == 0)
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = lean_box(0);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_965_);
v___x_967_ = v___x_963_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
else
{
lean_object* v_val_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_982_; 
v_val_969_ = lean_ctor_get(v_a_961_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v_a_961_);
if (v_isSharedCheck_982_ == 0)
{
v___x_971_ = v_a_961_;
v_isShared_972_ = v_isSharedCheck_982_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_val_969_);
lean_dec(v_a_961_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_982_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_fst_973_; uint8_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v_fst_973_ = lean_ctor_get(v_val_969_, 0);
lean_inc(v_fst_973_);
lean_dec(v_val_969_);
v___x_974_ = lean_uint8_of_nat(v_fst_973_);
lean_dec(v_fst_973_);
v___x_975_ = lean_box(v___x_974_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_975_);
v___x_977_ = v___x_971_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_979_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_977_);
v___x_979_ = v___x_963_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
v_a_984_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_960_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_960_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f___boxed(lean_object* v_e_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Meta_getUInt8Value_x3f(v_e_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object* v_e_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_1006_ = l_Lean_Meta_getOfNatValue_x3f(v_e_999_, v___x_1005_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1029_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1029_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1029_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
if (lean_obj_tag(v_a_1007_) == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = lean_box(0);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1011_);
v___x_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
else
{
lean_object* v_val_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1028_; 
v_val_1015_ = lean_ctor_get(v_a_1007_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_a_1007_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1017_ = v_a_1007_;
v_isShared_1018_ = v_isSharedCheck_1028_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_val_1015_);
lean_dec(v_a_1007_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1028_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_fst_1019_; uint16_t v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v_fst_1019_ = lean_ctor_get(v_val_1015_, 0);
lean_inc(v_fst_1019_);
lean_dec(v_val_1015_);
v___x_1020_ = lean_uint16_of_nat(v_fst_1019_);
lean_dec(v_fst_1019_);
v___x_1021_ = lean_box(v___x_1020_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1021_);
v___x_1023_ = v___x_1017_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1025_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1023_);
v___x_1025_ = v___x_1009_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
v_a_1030_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1006_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1006_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f___boxed(lean_object* v_e_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Meta_getUInt16Value_x3f(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object* v_e_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_1052_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1045_, v___x_1051_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1075_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1075_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1075_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
if (lean_obj_tag(v_a_1053_) == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_box(0);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
else
{
lean_object* v_val_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1074_; 
v_val_1061_ = lean_ctor_get(v_a_1053_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_a_1053_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1063_ = v_a_1053_;
v_isShared_1064_ = v_isSharedCheck_1074_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_val_1061_);
lean_dec(v_a_1053_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1074_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v_fst_1065_; uint32_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v_fst_1065_ = lean_ctor_get(v_val_1061_, 0);
lean_inc(v_fst_1065_);
lean_dec(v_val_1061_);
v___x_1066_ = lean_uint32_of_nat(v_fst_1065_);
lean_dec(v_fst_1065_);
v___x_1067_ = lean_box_uint32(v___x_1066_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1067_);
v___x_1069_ = v___x_1063_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1069_);
v___x_1071_ = v___x_1055_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1052_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1052_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f___boxed(lean_object* v_e_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_Meta_getUInt32Value_x3f(v_e_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object* v_e_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_1098_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1091_, v___x_1097_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1121_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1121_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1121_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
if (lean_obj_tag(v_a_1099_) == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1103_ = lean_box(0);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1103_);
v___x_1105_ = v___x_1101_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
else
{
lean_object* v_val_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1120_; 
v_val_1107_ = lean_ctor_get(v_a_1099_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_a_1099_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1109_ = v_a_1099_;
v_isShared_1110_ = v_isSharedCheck_1120_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_val_1107_);
lean_dec(v_a_1099_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1120_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_fst_1111_; uint64_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v_fst_1111_ = lean_ctor_get(v_val_1107_, 0);
lean_inc(v_fst_1111_);
lean_dec(v_val_1107_);
v___x_1112_ = lean_uint64_of_nat(v_fst_1111_);
lean_dec(v_fst_1111_);
v___x_1113_ = lean_box_uint64(v___x_1112_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1113_);
v___x_1115_ = v___x_1109_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1117_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1115_);
v___x_1117_ = v___x_1101_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
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
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_a_1122_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1098_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1098_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f___boxed(lean_object* v_e_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Meta_getUInt64Value_x3f(v_e_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(lean_object* v_e_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Expr_consumeMData(v_e_1140_);
if (lean_obj_tag(v___x_1141_) == 4)
{
lean_object* v_declName_1142_; 
v_declName_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_declName_1142_);
lean_dec_ref_known(v___x_1141_, 2);
if (lean_obj_tag(v_declName_1142_) == 1)
{
lean_object* v_pre_1143_; 
v_pre_1143_ = lean_ctor_get(v_declName_1142_, 0);
lean_inc(v_pre_1143_);
if (lean_obj_tag(v_pre_1143_) == 1)
{
lean_object* v_pre_1144_; 
v_pre_1144_ = lean_ctor_get(v_pre_1143_, 0);
if (lean_obj_tag(v_pre_1144_) == 0)
{
lean_object* v_str_1145_; lean_object* v_str_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_str_1145_ = lean_ctor_get(v_declName_1142_, 1);
lean_inc_ref(v_str_1145_);
lean_dec_ref_known(v_declName_1142_, 2);
v_str_1146_ = lean_ctor_get(v_pre_1143_, 1);
lean_inc_ref(v_str_1146_);
lean_dec_ref_known(v_pre_1143_, 2);
v___x_1147_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0));
v___x_1148_ = lean_string_dec_eq(v_str_1146_, v___x_1147_);
lean_dec_ref(v_str_1146_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
lean_dec_ref(v_str_1145_);
v___x_1149_ = lean_box(0);
return v___x_1149_;
}
else
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1));
v___x_1151_ = lean_string_dec_eq(v_str_1145_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2));
v___x_1153_ = lean_string_dec_eq(v_str_1145_, v___x_1152_);
lean_dec_ref(v_str_1145_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_box(0);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_box(v___x_1151_);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec_ref(v_str_1145_);
v___x_1157_ = lean_box(v___x_1151_);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
}
else
{
lean_object* v___x_1159_; 
lean_dec_ref_known(v_pre_1143_, 2);
lean_dec_ref_known(v_declName_1142_, 2);
v___x_1159_ = lean_box(0);
return v___x_1159_;
}
}
else
{
lean_object* v___x_1160_; 
lean_dec_ref_known(v_declName_1142_, 2);
lean_dec(v_pre_1143_);
v___x_1160_ = lean_box(0);
return v___x_1160_;
}
}
else
{
lean_object* v___x_1161_; 
lean_dec(v_declName_1142_);
v___x_1161_ = lean_box(0);
return v___x_1161_;
}
}
else
{
lean_object* v___x_1162_; 
lean_dec_ref(v___x_1141_);
v___x_1162_ = lean_box(0);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___boxed(lean_object* v_e_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_e_1163_);
lean_dec_ref(v_e_1163_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(lean_object* v_e_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v___x_1179_; 
lean_inc_ref(v_e_1173_);
v___x_1179_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1173_, v_a_1175_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___x_1179_, 1);
v___x_1219_ = l_Lean_Expr_cleanupAnnotations(v_a_1180_);
v___x_1220_ = l_Lean_Expr_isApp(v___x_1219_);
if (v___x_1220_ == 0)
{
lean_dec_ref(v___x_1219_);
v___y_1182_ = v_a_1174_;
v___y_1183_ = v_a_1175_;
v___y_1184_ = v_a_1176_;
v___y_1185_ = v_a_1177_;
goto v___jp_1181_;
}
else
{
lean_object* v_arg_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v_arg_1221_ = lean_ctor_get(v___x_1219_, 1);
lean_inc_ref(v_arg_1221_);
v___x_1222_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1219_);
v___x_1223_ = l_Lean_Expr_isApp(v___x_1222_);
if (v___x_1223_ == 0)
{
lean_dec_ref(v___x_1222_);
lean_dec_ref(v_arg_1221_);
v___y_1182_ = v_a_1174_;
v___y_1183_ = v_a_1175_;
v___y_1184_ = v_a_1176_;
v___y_1185_ = v_a_1177_;
goto v___jp_1181_;
}
else
{
lean_object* v_arg_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v_arg_1224_ = lean_ctor_get(v___x_1222_, 1);
lean_inc_ref(v_arg_1224_);
v___x_1225_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1222_);
v___x_1226_ = l_Lean_Expr_isApp(v___x_1225_);
if (v___x_1226_ == 0)
{
lean_dec_ref(v___x_1225_);
lean_dec_ref(v_arg_1224_);
lean_dec_ref(v_arg_1221_);
v___y_1182_ = v_a_1174_;
v___y_1183_ = v_a_1175_;
v___y_1184_ = v_a_1176_;
v___y_1185_ = v_a_1177_;
goto v___jp_1181_;
}
else
{
lean_object* v_arg_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v_arg_1227_ = lean_ctor_get(v___x_1225_, 1);
lean_inc_ref(v_arg_1227_);
v___x_1228_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1225_);
v___x_1229_ = l_Lean_Expr_isApp(v___x_1228_);
if (v___x_1229_ == 0)
{
lean_dec_ref(v___x_1228_);
lean_dec_ref(v_arg_1227_);
lean_dec_ref(v_arg_1224_);
lean_dec_ref(v_arg_1221_);
v___y_1182_ = v_a_1174_;
v___y_1183_ = v_a_1175_;
v___y_1184_ = v_a_1176_;
v___y_1185_ = v_a_1177_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1228_);
v___x_1231_ = l_Lean_Expr_isApp(v___x_1230_);
if (v___x_1231_ == 0)
{
lean_dec_ref(v___x_1230_);
lean_dec_ref(v_arg_1227_);
lean_dec_ref(v_arg_1224_);
lean_dec_ref(v_arg_1221_);
v___y_1182_ = v_a_1174_;
v___y_1183_ = v_a_1175_;
v___y_1184_ = v_a_1176_;
v___y_1185_ = v_a_1177_;
goto v___jp_1181_;
}
else
{
lean_object* v_arg_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_arg_1232_ = lean_ctor_get(v___x_1230_, 1);
lean_inc_ref(v_arg_1232_);
v___x_1233_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1230_);
v___x_1234_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__4));
v___x_1235_ = l_Lean_Expr_isConstOf(v___x_1233_, v___x_1234_);
lean_dec_ref(v___x_1233_);
if (v___x_1235_ == 0)
{
lean_dec_ref(v_arg_1232_);
lean_dec_ref(v_arg_1227_);
lean_dec_ref(v_arg_1224_);
lean_dec_ref(v_arg_1221_);
v___y_1182_ = v_a_1174_;
v___y_1183_ = v_a_1175_;
v___y_1184_ = v_a_1176_;
v___y_1185_ = v_a_1177_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1236_; 
lean_dec_ref(v_e_1173_);
v___x_1236_ = l_Lean_Meta_whnfD(v_arg_1232_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1304_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1304_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1304_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1242_ = l_Lean_Expr_isConstOf(v_a_1237_, v___x_1241_);
lean_dec(v_a_1237_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
lean_dec_ref(v_arg_1227_);
lean_dec_ref(v_arg_1224_);
lean_dec_ref(v_arg_1221_);
v___x_1243_ = lean_box(0);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1243_);
v___x_1245_ = v___x_1239_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
else
{
lean_object* v___x_1247_; 
v___x_1247_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_1224_);
lean_dec_ref(v_arg_1224_);
if (lean_obj_tag(v___x_1247_) == 1)
{
lean_object* v_val_1248_; lean_object* v___x_1249_; 
lean_del_object(v___x_1239_);
v_val_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_val_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1249_ = l_Lean_Meta_getNatValue_x3f(v_arg_1227_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec_ref(v_arg_1227_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1291_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1291_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1291_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
if (lean_obj_tag(v_a_1250_) == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
lean_dec(v_val_1248_);
lean_dec_ref(v_arg_1221_);
v___x_1254_ = lean_box(0);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1254_);
v___x_1256_ = v___x_1252_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
else
{
lean_object* v_val_1258_; lean_object* v___x_1259_; 
lean_del_object(v___x_1252_);
v_val_1258_ = lean_ctor_get(v_a_1250_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v_a_1250_, 1);
v___x_1259_ = l_Lean_Meta_getNatValue_x3f(v_arg_1221_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec_ref(v_arg_1221_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1282_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1282_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1282_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
if (lean_obj_tag(v_a_1260_) == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
lean_dec(v_val_1258_);
lean_dec(v_val_1248_);
v___x_1264_ = lean_box(0);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1264_);
v___x_1266_ = v___x_1262_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
else
{
lean_object* v_val_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1281_; 
v_val_1268_ = lean_ctor_get(v_a_1260_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_a_1260_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1270_ = v_a_1260_;
v_isShared_1271_ = v_isSharedCheck_1281_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_val_1268_);
lean_dec(v_a_1260_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1281_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
uint8_t v___x_1272_; double v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1272_ = lean_unbox(v_val_1248_);
lean_dec(v_val_1248_);
v___x_1273_ = l_Float_ofScientific(v_val_1258_, v___x_1272_, v_val_1268_);
v___x_1274_ = lean_box_float(v___x_1273_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1274_);
v___x_1276_ = v___x_1270_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1276_);
v___x_1278_ = v___x_1262_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_val_1258_);
lean_dec(v_val_1248_);
v_a_1283_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1259_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1259_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_val_1248_);
lean_dec_ref(v_arg_1221_);
v_a_1292_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1249_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1249_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_dec(v___x_1247_);
lean_dec_ref(v_arg_1227_);
lean_dec_ref(v_arg_1221_);
v___x_1300_ = lean_box(0);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1300_);
v___x_1302_ = v___x_1239_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec_ref(v_arg_1227_);
lean_dec_ref(v_arg_1224_);
lean_dec_ref(v_arg_1221_);
v_a_1305_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1236_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1236_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
}
}
}
}
v___jp_1181_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1187_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1173_, v___x_1186_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1210_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1210_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1210_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
if (lean_obj_tag(v_a_1188_) == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_box(0);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1192_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
else
{
lean_object* v_val_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1209_; 
v_val_1196_ = lean_ctor_get(v_a_1188_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_a_1188_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1198_ = v_a_1188_;
v_isShared_1199_ = v_isSharedCheck_1209_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_val_1196_);
lean_dec(v_a_1188_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1209_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v_fst_1200_; double v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v_fst_1200_ = lean_ctor_get(v_val_1196_, 0);
lean_inc(v_fst_1200_);
lean_dec(v_val_1196_);
v___x_1201_ = lean_float_of_nat(v_fst_1200_);
v___x_1202_ = lean_box_float(v___x_1201_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1202_);
v___x_1204_ = v___x_1198_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1204_);
v___x_1206_ = v___x_1190_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
v_a_1211_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1187_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1187_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v_e_1173_);
v_a_1313_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1179_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1179_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___boxed(lean_object* v_e_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f(lean_object* v_e_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v___x_1334_; 
lean_inc_ref(v_e_1328_);
v___x_1334_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
if (lean_obj_tag(v_a_1335_) == 1)
{
lean_dec_ref_known(v_a_1335_, 1);
lean_dec_ref(v_e_1328_);
return v___x_1334_;
}
else
{
lean_object* v___x_1336_; 
lean_dec_ref_known(v___x_1334_, 1);
lean_dec(v_a_1335_);
v___x_1336_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1328_, v_a_1330_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1380_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1380_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1380_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = l_Lean_Expr_cleanupAnnotations(v_a_1337_);
v___x_1347_ = l_Lean_Expr_isApp(v___x_1346_);
if (v___x_1347_ == 0)
{
lean_dec_ref(v___x_1346_);
goto v___jp_1341_;
}
else
{
lean_object* v_arg_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v_arg_1348_ = lean_ctor_get(v___x_1346_, 1);
lean_inc_ref(v_arg_1348_);
v___x_1349_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1346_);
v___x_1350_ = l_Lean_Expr_isApp(v___x_1349_);
if (v___x_1350_ == 0)
{
lean_dec_ref(v___x_1349_);
lean_dec_ref(v_arg_1348_);
goto v___jp_1341_;
}
else
{
lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1349_);
v___x_1352_ = l_Lean_Expr_isApp(v___x_1351_);
if (v___x_1352_ == 0)
{
lean_dec_ref(v___x_1351_);
lean_dec_ref(v_arg_1348_);
goto v___jp_1341_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1353_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1351_);
v___x_1354_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1355_ = l_Lean_Expr_isConstOf(v___x_1353_, v___x_1354_);
lean_dec_ref(v___x_1353_);
if (v___x_1355_ == 0)
{
lean_dec_ref(v_arg_1348_);
goto v___jp_1341_;
}
else
{
lean_object* v___x_1356_; 
lean_del_object(v___x_1339_);
v___x_1356_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_arg_1348_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1379_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1379_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1379_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
if (lean_obj_tag(v_a_1357_) == 1)
{
lean_object* v_val_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1374_; 
v_val_1361_ = lean_ctor_get(v_a_1357_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_a_1357_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1363_ = v_a_1357_;
v_isShared_1364_ = v_isSharedCheck_1374_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_val_1361_);
lean_dec(v_a_1357_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1374_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
double v___x_1365_; double v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1365_ = lean_unbox_float(v_val_1361_);
lean_dec(v_val_1361_);
v___x_1366_ = lean_float_negate(v___x_1365_);
v___x_1367_ = lean_box_float(v___x_1366_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1367_);
v___x_1369_ = v___x_1363_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1371_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1369_);
v___x_1371_ = v___x_1359_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_dec(v_a_1357_);
v___x_1375_ = lean_box(0);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1375_);
v___x_1377_ = v___x_1359_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
return v___x_1356_;
}
}
}
}
}
v___jp_1341_:
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1342_ = lean_box(0);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1342_);
v___x_1344_ = v___x_1339_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1336_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1336_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1328_);
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f___boxed(lean_object* v_e_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Meta_getFloatValue_x3f(v_e_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(lean_object* v_e_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v___x_1405_; 
lean_inc_ref(v_e_1399_);
v___x_1405_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1399_, v_a_1401_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v___x_1445_ = l_Lean_Expr_cleanupAnnotations(v_a_1406_);
v___x_1446_ = l_Lean_Expr_isApp(v___x_1445_);
if (v___x_1446_ == 0)
{
lean_dec_ref(v___x_1445_);
v___y_1408_ = v_a_1400_;
v___y_1409_ = v_a_1401_;
v___y_1410_ = v_a_1402_;
v___y_1411_ = v_a_1403_;
goto v___jp_1407_;
}
else
{
lean_object* v_arg_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v_arg_1447_ = lean_ctor_get(v___x_1445_, 1);
lean_inc_ref(v_arg_1447_);
v___x_1448_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1445_);
v___x_1449_ = l_Lean_Expr_isApp(v___x_1448_);
if (v___x_1449_ == 0)
{
lean_dec_ref(v___x_1448_);
lean_dec_ref(v_arg_1447_);
v___y_1408_ = v_a_1400_;
v___y_1409_ = v_a_1401_;
v___y_1410_ = v_a_1402_;
v___y_1411_ = v_a_1403_;
goto v___jp_1407_;
}
else
{
lean_object* v_arg_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_arg_1450_ = lean_ctor_get(v___x_1448_, 1);
lean_inc_ref(v_arg_1450_);
v___x_1451_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1448_);
v___x_1452_ = l_Lean_Expr_isApp(v___x_1451_);
if (v___x_1452_ == 0)
{
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_arg_1450_);
lean_dec_ref(v_arg_1447_);
v___y_1408_ = v_a_1400_;
v___y_1409_ = v_a_1401_;
v___y_1410_ = v_a_1402_;
v___y_1411_ = v_a_1403_;
goto v___jp_1407_;
}
else
{
lean_object* v_arg_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v_arg_1453_ = lean_ctor_get(v___x_1451_, 1);
lean_inc_ref(v_arg_1453_);
v___x_1454_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1451_);
v___x_1455_ = l_Lean_Expr_isApp(v___x_1454_);
if (v___x_1455_ == 0)
{
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_arg_1453_);
lean_dec_ref(v_arg_1450_);
lean_dec_ref(v_arg_1447_);
v___y_1408_ = v_a_1400_;
v___y_1409_ = v_a_1401_;
v___y_1410_ = v_a_1402_;
v___y_1411_ = v_a_1403_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1454_);
v___x_1457_ = l_Lean_Expr_isApp(v___x_1456_);
if (v___x_1457_ == 0)
{
lean_dec_ref(v___x_1456_);
lean_dec_ref(v_arg_1453_);
lean_dec_ref(v_arg_1450_);
lean_dec_ref(v_arg_1447_);
v___y_1408_ = v_a_1400_;
v___y_1409_ = v_a_1401_;
v___y_1410_ = v_a_1402_;
v___y_1411_ = v_a_1403_;
goto v___jp_1407_;
}
else
{
lean_object* v_arg_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_arg_1458_ = lean_ctor_get(v___x_1456_, 1);
lean_inc_ref(v_arg_1458_);
v___x_1459_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1456_);
v___x_1460_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__4));
v___x_1461_ = l_Lean_Expr_isConstOf(v___x_1459_, v___x_1460_);
lean_dec_ref(v___x_1459_);
if (v___x_1461_ == 0)
{
lean_dec_ref(v_arg_1458_);
lean_dec_ref(v_arg_1453_);
lean_dec_ref(v_arg_1450_);
lean_dec_ref(v_arg_1447_);
v___y_1408_ = v_a_1400_;
v___y_1409_ = v_a_1401_;
v___y_1410_ = v_a_1402_;
v___y_1411_ = v_a_1403_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1462_; 
lean_dec_ref(v_e_1399_);
v___x_1462_ = l_Lean_Meta_whnfD(v_arg_1458_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1530_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1530_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1530_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_1468_ = l_Lean_Expr_isConstOf(v_a_1463_, v___x_1467_);
lean_dec(v_a_1463_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
lean_dec_ref(v_arg_1453_);
lean_dec_ref(v_arg_1450_);
lean_dec_ref(v_arg_1447_);
v___x_1469_ = lean_box(0);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1469_);
v___x_1471_ = v___x_1465_;
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
lean_object* v___x_1473_; 
v___x_1473_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_1450_);
lean_dec_ref(v_arg_1450_);
if (lean_obj_tag(v___x_1473_) == 1)
{
lean_object* v_val_1474_; lean_object* v___x_1475_; 
lean_del_object(v___x_1465_);
v_val_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_val_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v___x_1475_ = l_Lean_Meta_getNatValue_x3f(v_arg_1453_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec_ref(v_arg_1453_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1517_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1517_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1517_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
if (lean_obj_tag(v_a_1476_) == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
lean_dec(v_val_1474_);
lean_dec_ref(v_arg_1447_);
v___x_1480_ = lean_box(0);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1480_);
v___x_1482_ = v___x_1478_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
else
{
lean_object* v_val_1484_; lean_object* v___x_1485_; 
lean_del_object(v___x_1478_);
v_val_1484_ = lean_ctor_get(v_a_1476_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v_a_1476_, 1);
v___x_1485_ = l_Lean_Meta_getNatValue_x3f(v_arg_1447_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec_ref(v_arg_1447_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1508_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1508_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1508_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
if (lean_obj_tag(v_a_1486_) == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_dec(v_val_1484_);
lean_dec(v_val_1474_);
v___x_1490_ = lean_box(0);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
else
{
lean_object* v_val_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1507_; 
v_val_1494_ = lean_ctor_get(v_a_1486_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_a_1486_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1496_ = v_a_1486_;
v_isShared_1497_ = v_isSharedCheck_1507_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_val_1494_);
lean_dec(v_a_1486_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1507_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
uint8_t v___x_1498_; float v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1498_ = lean_unbox(v_val_1474_);
lean_dec(v_val_1474_);
v___x_1499_ = l_Float32_ofScientific(v_val_1484_, v___x_1498_, v_val_1494_);
v___x_1500_ = lean_box_float32(v___x_1499_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1500_);
v___x_1502_ = v___x_1496_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1502_);
v___x_1504_ = v___x_1488_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v_val_1484_);
lean_dec(v_val_1474_);
v_a_1509_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1485_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1485_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec(v_val_1474_);
lean_dec_ref(v_arg_1447_);
v_a_1518_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1475_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1475_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
lean_dec(v___x_1473_);
lean_dec_ref(v_arg_1453_);
lean_dec_ref(v_arg_1447_);
v___x_1526_ = lean_box(0);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1526_);
v___x_1528_ = v___x_1465_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec_ref(v_arg_1453_);
lean_dec_ref(v_arg_1450_);
lean_dec_ref(v_arg_1447_);
v_a_1531_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1462_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1462_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
}
}
}
}
v___jp_1407_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_1413_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1399_, v___x_1412_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1436_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1436_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1436_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
if (lean_obj_tag(v_a_1414_) == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = lean_box(0);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
else
{
lean_object* v_val_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1435_; 
v_val_1422_ = lean_ctor_get(v_a_1414_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_a_1414_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1424_ = v_a_1414_;
v_isShared_1425_ = v_isSharedCheck_1435_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_val_1422_);
lean_dec(v_a_1414_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1435_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v_fst_1426_; float v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v_fst_1426_ = lean_ctor_get(v_val_1422_, 0);
lean_inc(v_fst_1426_);
lean_dec(v_val_1422_);
v___x_1427_ = lean_float32_of_nat(v_fst_1426_);
v___x_1428_ = lean_box_float32(v___x_1427_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1428_);
v___x_1430_ = v___x_1424_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1432_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1430_);
v___x_1432_ = v___x_1416_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
v_a_1437_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1413_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1413_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref(v_e_1399_);
v_a_1539_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1405_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1405_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___boxed(lean_object* v_e_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f(lean_object* v_e_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v___x_1560_; 
lean_inc_ref(v_e_1554_);
v___x_1560_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
if (lean_obj_tag(v_a_1561_) == 1)
{
lean_dec_ref_known(v_a_1561_, 1);
lean_dec_ref(v_e_1554_);
return v___x_1560_;
}
else
{
lean_object* v___x_1562_; 
lean_dec_ref_known(v___x_1560_, 1);
lean_dec(v_a_1561_);
v___x_1562_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1554_, v_a_1556_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1606_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1606_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1606_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = l_Lean_Expr_cleanupAnnotations(v_a_1563_);
v___x_1573_ = l_Lean_Expr_isApp(v___x_1572_);
if (v___x_1573_ == 0)
{
lean_dec_ref(v___x_1572_);
goto v___jp_1567_;
}
else
{
lean_object* v_arg_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_arg_1574_ = lean_ctor_get(v___x_1572_, 1);
lean_inc_ref(v_arg_1574_);
v___x_1575_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1572_);
v___x_1576_ = l_Lean_Expr_isApp(v___x_1575_);
if (v___x_1576_ == 0)
{
lean_dec_ref(v___x_1575_);
lean_dec_ref(v_arg_1574_);
goto v___jp_1567_;
}
else
{
lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1575_);
v___x_1578_ = l_Lean_Expr_isApp(v___x_1577_);
if (v___x_1578_ == 0)
{
lean_dec_ref(v___x_1577_);
lean_dec_ref(v_arg_1574_);
goto v___jp_1567_;
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1579_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1577_);
v___x_1580_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1581_ = l_Lean_Expr_isConstOf(v___x_1579_, v___x_1580_);
lean_dec_ref(v___x_1579_);
if (v___x_1581_ == 0)
{
lean_dec_ref(v_arg_1574_);
goto v___jp_1567_;
}
else
{
lean_object* v___x_1582_; 
lean_del_object(v___x_1565_);
v___x_1582_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_arg_1574_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1605_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1605_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1605_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
if (lean_obj_tag(v_a_1583_) == 1)
{
lean_object* v_val_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1600_; 
v_val_1587_ = lean_ctor_get(v_a_1583_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_a_1583_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1589_ = v_a_1583_;
v_isShared_1590_ = v_isSharedCheck_1600_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_val_1587_);
lean_dec(v_a_1583_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1600_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
float v___x_1591_; float v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1591_ = lean_unbox_float32(v_val_1587_);
lean_dec(v_val_1587_);
v___x_1592_ = lean_float32_negate(v___x_1591_);
v___x_1593_ = lean_box_float32(v___x_1592_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1593_);
v___x_1595_ = v___x_1589_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1595_);
v___x_1597_ = v___x_1585_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
lean_dec(v_a_1583_);
v___x_1601_ = lean_box(0);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1601_);
v___x_1603_ = v___x_1585_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
return v___x_1582_;
}
}
}
}
}
v___jp_1567_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = lean_box(0);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1568_);
v___x_1570_ = v___x_1565_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_a_1607_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1562_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1562_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1554_);
return v___x_1560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f___boxed(lean_object* v_e_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Meta_getFloat32Value_x3f(v_e_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(lean_object* v_e_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v___x_1625_; 
v___x_1625_ = l_Lean_Expr_hasMVar(v_e_1622_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v_e_1622_);
return v___x_1626_;
}
else
{
lean_object* v___x_1627_; lean_object* v_mctx_1628_; lean_object* v___x_1629_; lean_object* v_fst_1630_; lean_object* v_snd_1631_; lean_object* v___x_1632_; lean_object* v_cache_1633_; lean_object* v_zetaDeltaFVarIds_1634_; lean_object* v_postponed_1635_; lean_object* v_diag_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1645_; 
v___x_1627_ = lean_st_ref_get(v___y_1623_);
v_mctx_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc_ref(v_mctx_1628_);
lean_dec(v___x_1627_);
v___x_1629_ = l_Lean_instantiateMVarsCore(v_mctx_1628_, v_e_1622_);
v_fst_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_fst_1630_);
v_snd_1631_ = lean_ctor_get(v___x_1629_, 1);
lean_inc(v_snd_1631_);
lean_dec_ref(v___x_1629_);
v___x_1632_ = lean_st_ref_take(v___y_1623_);
v_cache_1633_ = lean_ctor_get(v___x_1632_, 1);
v_zetaDeltaFVarIds_1634_ = lean_ctor_get(v___x_1632_, 2);
v_postponed_1635_ = lean_ctor_get(v___x_1632_, 3);
v_diag_1636_ = lean_ctor_get(v___x_1632_, 4);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v___x_1632_, 0);
lean_dec(v_unused_1646_);
v___x_1638_ = v___x_1632_;
v_isShared_1639_ = v_isSharedCheck_1645_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_diag_1636_);
lean_inc(v_postponed_1635_);
lean_inc(v_zetaDeltaFVarIds_1634_);
lean_inc(v_cache_1633_);
lean_dec(v___x_1632_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1645_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v_snd_1631_);
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_snd_1631_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_cache_1633_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_zetaDeltaFVarIds_1634_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_postponed_1635_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_diag_1636_);
v___x_1641_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_st_ref_put(v___y_1623_, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v_fst_1630_);
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg___boxed(lean_object* v_e_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1647_, v___y_1648_);
lean_dec(v___y_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(lean_object* v_e_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1651_, v___y_1653_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___boxed(lean_object* v_e_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(v_e_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1664_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__0(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = lean_nat_to_int(v___x_1665_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__1(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_unsigned_to_nat(0u);
v___x_1668_ = l_Lean_Level_ofNat(v___x_1667_);
return v___x_1668_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__2(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__1, &l_Lean_Meta_normLitValue___closed__1_once, _init_l_Lean_Meta_normLitValue___closed__1);
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1669_);
return v___x_1671_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__3(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_1673_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1674_ = l_Lean_Expr_const___override(v___x_1673_, v___x_1672_);
return v___x_1674_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__4(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = lean_box(0);
v___x_1676_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_1677_ = l_Lean_Expr_const___override(v___x_1676_, v___x_1675_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__7(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_box(0);
v___x_1683_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__6));
v___x_1684_ = l_Lean_Expr_const___override(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__8(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_1686_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_1687_ = l_Lean_Expr_const___override(v___x_1686_, v___x_1685_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__9(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_box(0);
v___x_1689_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_1690_ = l_Lean_mkConst(v___x_1689_, v___x_1688_);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__12(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_box(0);
v___x_1696_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__11));
v___x_1697_ = l_Lean_Expr_const___override(v___x_1696_, v___x_1695_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__15(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_box(0);
v___x_1703_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__14));
v___x_1704_ = l_Lean_Expr_const___override(v___x_1703_, v___x_1702_);
return v___x_1704_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__16(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = lean_box(0);
v___x_1706_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_1707_ = l_Lean_Expr_const___override(v___x_1706_, v___x_1705_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__17(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_box(0);
v___x_1709_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_1710_ = l_Lean_mkConst(v___x_1709_, v___x_1708_);
return v___x_1710_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__18(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = lean_box(0);
v___x_1712_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_1713_ = l_Lean_mkConst(v___x_1712_, v___x_1711_);
return v___x_1713_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__20(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = lean_box(0);
v___x_1718_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__19));
v___x_1719_ = l_Lean_Expr_const___override(v___x_1718_, v___x_1717_);
return v___x_1719_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__21(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = lean_box(0);
v___x_1721_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_1722_ = l_Lean_mkConst(v___x_1721_, v___x_1720_);
return v___x_1722_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__23(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__22));
v___x_1728_ = l_Lean_Expr_const___override(v___x_1727_, v___x_1726_);
return v___x_1728_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__24(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_box(0);
v___x_1730_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_1731_ = l_Lean_mkConst(v___x_1730_, v___x_1729_);
return v___x_1731_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__26(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = lean_box(0);
v___x_1736_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__25));
v___x_1737_ = l_Lean_Expr_const___override(v___x_1736_, v___x_1735_);
return v___x_1737_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__27(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_box(0);
v___x_1739_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_1740_ = l_Lean_mkConst(v___x_1739_, v___x_1738_);
return v___x_1740_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__29(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_box(0);
v___x_1745_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__28));
v___x_1746_ = l_Lean_Expr_const___override(v___x_1745_, v___x_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue(lean_object* v_e_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; lean_object* v_a_1754_; lean_object* v___x_1755_; 
v___x_1753_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1747_, v_a_1749_);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = l_Lean_Meta_getNatValue_x3f(v_a_1754_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1990_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1990_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1990_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
if (lean_obj_tag(v_a_1756_) == 1)
{
lean_object* v_val_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
lean_dec(v_a_1754_);
v_val_1760_ = lean_ctor_get(v_a_1756_, 0);
lean_inc(v_val_1760_);
lean_dec_ref_known(v_a_1756_, 1);
v___x_1761_ = l_Lean_mkNatLit(v_val_1760_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1761_);
v___x_1763_ = v___x_1758_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
else
{
lean_object* v___x_1765_; 
lean_del_object(v___x_1758_);
lean_dec(v_a_1756_);
lean_inc(v_a_1754_);
v___x_1765_ = l_Lean_Meta_getIntValue_x3f(v_a_1754_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1981_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1981_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1981_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
if (lean_obj_tag(v_a_1766_) == 1)
{
lean_object* v_val_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
lean_dec(v_a_1754_);
v_val_1770_ = lean_ctor_get(v_a_1766_, 0);
lean_inc(v_val_1770_);
lean_dec_ref_known(v_a_1766_, 1);
v___x_1771_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_1772_ = lean_int_dec_le(v___x_1771_, v_val_1770_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1773_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_1774_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__4, &l_Lean_Meta_normLitValue___closed__4_once, _init_l_Lean_Meta_normLitValue___closed__4);
v___x_1775_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__7, &l_Lean_Meta_normLitValue___closed__7_once, _init_l_Lean_Meta_normLitValue___closed__7);
v___x_1776_ = lean_int_neg(v_val_1770_);
lean_dec(v_val_1770_);
v___x_1777_ = l_Int_toNat(v___x_1776_);
lean_dec(v___x_1776_);
v___x_1778_ = l_Lean_instToExprInt_mkNat(v___x_1777_);
v___x_1779_ = l_Lean_mkApp3(v___x_1773_, v___x_1774_, v___x_1775_, v___x_1778_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1779_);
v___x_1781_ = v___x_1768_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1783_ = l_Int_toNat(v_val_1770_);
lean_dec(v_val_1770_);
v___x_1784_ = l_Lean_instToExprInt_mkNat(v___x_1783_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1784_);
v___x_1786_ = v___x_1768_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_object* v___x_1788_; 
lean_del_object(v___x_1768_);
lean_dec(v_a_1766_);
lean_inc(v_a_1754_);
v___x_1788_ = l_Lean_Meta_getFinValue_x3f(v_a_1754_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1972_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1972_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1972_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
if (lean_obj_tag(v_a_1789_) == 1)
{
lean_object* v_val_1793_; lean_object* v_fst_1794_; lean_object* v_snd_1795_; lean_object* v_r_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
lean_dec(v_a_1754_);
v_val_1793_ = lean_ctor_get(v_a_1789_, 0);
lean_inc(v_val_1793_);
lean_dec_ref_known(v_a_1789_, 1);
v_fst_1794_ = lean_ctor_get(v_val_1793_, 0);
lean_inc_n(v_fst_1794_, 2);
v_snd_1795_ = lean_ctor_get(v_val_1793_, 1);
lean_inc(v_snd_1795_);
lean_dec(v_val_1793_);
v_r_1796_ = l_Lean_mkRawNatLit(v_snd_1795_);
v___x_1797_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1798_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__9, &l_Lean_Meta_normLitValue___closed__9_once, _init_l_Lean_Meta_normLitValue___closed__9);
v___x_1799_ = l_Lean_mkNatLit(v_fst_1794_);
lean_inc_ref(v___x_1799_);
v___x_1800_ = l_Lean_Expr_app___override(v___x_1798_, v___x_1799_);
v___x_1801_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__12, &l_Lean_Meta_normLitValue___closed__12_once, _init_l_Lean_Meta_normLitValue___closed__12);
v___x_1802_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__15, &l_Lean_Meta_normLitValue___closed__15_once, _init_l_Lean_Meta_normLitValue___closed__15);
v___x_1803_ = lean_unsigned_to_nat(1u);
v___x_1804_ = lean_nat_sub(v_fst_1794_, v___x_1803_);
lean_dec(v_fst_1794_);
v___x_1805_ = l_Lean_mkNatLit(v___x_1804_);
v___x_1806_ = l_Lean_Expr_app___override(v___x_1802_, v___x_1805_);
lean_inc_ref(v_r_1796_);
v___x_1807_ = l_Lean_mkApp3(v___x_1801_, v___x_1799_, v___x_1806_, v_r_1796_);
v___x_1808_ = l_Lean_mkApp3(v___x_1797_, v___x_1800_, v_r_1796_, v___x_1807_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1808_);
v___x_1810_ = v___x_1791_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
else
{
lean_object* v___x_1812_; 
lean_del_object(v___x_1791_);
lean_dec(v_a_1789_);
lean_inc(v_a_1754_);
v___x_1812_ = l_Lean_Meta_getBitVecValue_x3f(v_a_1754_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1963_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1963_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1963_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
if (lean_obj_tag(v_a_1813_) == 1)
{
lean_object* v_val_1817_; lean_object* v_fst_1818_; lean_object* v_snd_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
lean_dec(v_a_1754_);
v_val_1817_ = lean_ctor_get(v_a_1813_, 0);
lean_inc(v_val_1817_);
lean_dec_ref_known(v_a_1813_, 1);
v_fst_1818_ = lean_ctor_get(v_val_1817_, 0);
lean_inc(v_fst_1818_);
v_snd_1819_ = lean_ctor_get(v_val_1817_, 1);
lean_inc(v_snd_1819_);
lean_dec(v_val_1817_);
v___x_1820_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__16, &l_Lean_Meta_normLitValue___closed__16_once, _init_l_Lean_Meta_normLitValue___closed__16);
v___x_1821_ = l_Lean_mkNatLit(v_fst_1818_);
v___x_1822_ = l_Lean_mkNatLit(v_snd_1819_);
v___x_1823_ = l_Lean_mkAppB(v___x_1820_, v___x_1821_, v___x_1822_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1823_);
v___x_1825_ = v___x_1815_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
else
{
lean_object* v___x_1827_; 
lean_dec(v_a_1813_);
lean_inc(v_a_1754_);
v___x_1827_ = l_Lean_Meta_getStringValue_x3f(v_a_1754_);
if (lean_obj_tag(v___x_1827_) == 1)
{
lean_object* v_val_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
lean_dec(v_a_1754_);
v_val_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_val_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1829_ = l_Lean_mkStrLit(v_val_1828_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1829_);
v___x_1831_ = v___x_1815_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
else
{
lean_object* v___x_1833_; 
lean_dec(v___x_1827_);
lean_del_object(v___x_1815_);
lean_inc(v_a_1754_);
v___x_1833_ = l_Lean_Meta_getCharValue_x3f(v_a_1754_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1954_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1954_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1954_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
if (lean_obj_tag(v_a_1834_) == 1)
{
lean_object* v_val_1838_; lean_object* v___x_1839_; uint32_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
lean_dec(v_a_1754_);
v_val_1838_ = lean_ctor_get(v_a_1834_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v_a_1834_, 1);
v___x_1839_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__17, &l_Lean_Meta_normLitValue___closed__17_once, _init_l_Lean_Meta_normLitValue___closed__17);
v___x_1840_ = lean_unbox_uint32(v_val_1838_);
lean_dec(v_val_1838_);
v___x_1841_ = lean_uint32_to_nat(v___x_1840_);
v___x_1842_ = l_Lean_mkRawNatLit(v___x_1841_);
v___x_1843_ = l_Lean_Expr_app___override(v___x_1839_, v___x_1842_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1843_);
v___x_1845_ = v___x_1836_;
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
else
{
lean_object* v___x_1847_; 
lean_del_object(v___x_1836_);
lean_dec(v_a_1834_);
lean_inc(v_a_1754_);
v___x_1847_ = l_Lean_Meta_getUInt8Value_x3f(v_a_1754_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1945_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1945_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1945_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
if (lean_obj_tag(v_a_1848_) == 1)
{
lean_object* v_val_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; lean_object* v_r_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
lean_dec(v_a_1754_);
v_val_1852_ = lean_ctor_get(v_a_1848_, 0);
lean_inc(v_val_1852_);
lean_dec_ref_known(v_a_1848_, 1);
v___x_1853_ = lean_unbox(v_val_1852_);
lean_dec(v_val_1852_);
v___x_1854_ = lean_uint8_to_nat(v___x_1853_);
v_r_1855_ = l_Lean_mkRawNatLit(v___x_1854_);
v___x_1856_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1857_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__18, &l_Lean_Meta_normLitValue___closed__18_once, _init_l_Lean_Meta_normLitValue___closed__18);
v___x_1858_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__20, &l_Lean_Meta_normLitValue___closed__20_once, _init_l_Lean_Meta_normLitValue___closed__20);
lean_inc_ref(v_r_1855_);
v___x_1859_ = l_Lean_Expr_app___override(v___x_1858_, v_r_1855_);
v___x_1860_ = l_Lean_mkApp3(v___x_1856_, v___x_1857_, v_r_1855_, v___x_1859_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1860_);
v___x_1862_ = v___x_1850_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
else
{
lean_object* v___x_1864_; 
lean_del_object(v___x_1850_);
lean_dec(v_a_1848_);
lean_inc(v_a_1754_);
v___x_1864_ = l_Lean_Meta_getUInt16Value_x3f(v_a_1754_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1936_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1936_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1936_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
if (lean_obj_tag(v_a_1865_) == 1)
{
lean_object* v_val_1869_; uint16_t v___x_1870_; lean_object* v___x_1871_; lean_object* v_r_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
lean_dec(v_a_1754_);
v_val_1869_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v_a_1865_, 1);
v___x_1870_ = lean_unbox(v_val_1869_);
lean_dec(v_val_1869_);
v___x_1871_ = lean_uint16_to_nat(v___x_1870_);
v_r_1872_ = l_Lean_mkRawNatLit(v___x_1871_);
v___x_1873_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1874_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__21, &l_Lean_Meta_normLitValue___closed__21_once, _init_l_Lean_Meta_normLitValue___closed__21);
v___x_1875_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__23, &l_Lean_Meta_normLitValue___closed__23_once, _init_l_Lean_Meta_normLitValue___closed__23);
lean_inc_ref(v_r_1872_);
v___x_1876_ = l_Lean_Expr_app___override(v___x_1875_, v_r_1872_);
v___x_1877_ = l_Lean_mkApp3(v___x_1873_, v___x_1874_, v_r_1872_, v___x_1876_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1877_);
v___x_1879_ = v___x_1867_;
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
lean_object* v___x_1881_; 
lean_del_object(v___x_1867_);
lean_dec(v_a_1865_);
lean_inc(v_a_1754_);
v___x_1881_ = l_Lean_Meta_getUInt32Value_x3f(v_a_1754_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1927_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1927_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1927_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
if (lean_obj_tag(v_a_1882_) == 1)
{
lean_object* v_val_1886_; uint32_t v___x_1887_; lean_object* v___x_1888_; lean_object* v_r_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
lean_dec(v_a_1754_);
v_val_1886_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_val_1886_);
lean_dec_ref_known(v_a_1882_, 1);
v___x_1887_ = lean_unbox_uint32(v_val_1886_);
lean_dec(v_val_1886_);
v___x_1888_ = lean_uint32_to_nat(v___x_1887_);
v_r_1889_ = l_Lean_mkRawNatLit(v___x_1888_);
v___x_1890_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1891_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__24, &l_Lean_Meta_normLitValue___closed__24_once, _init_l_Lean_Meta_normLitValue___closed__24);
v___x_1892_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__26, &l_Lean_Meta_normLitValue___closed__26_once, _init_l_Lean_Meta_normLitValue___closed__26);
lean_inc_ref(v_r_1889_);
v___x_1893_ = l_Lean_Expr_app___override(v___x_1892_, v_r_1889_);
v___x_1894_ = l_Lean_mkApp3(v___x_1890_, v___x_1891_, v_r_1889_, v___x_1893_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1894_);
v___x_1896_ = v___x_1884_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
else
{
lean_object* v___x_1898_; 
lean_del_object(v___x_1884_);
lean_dec(v_a_1882_);
lean_inc(v_a_1754_);
v___x_1898_ = l_Lean_Meta_getUInt64Value_x3f(v_a_1754_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1918_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1918_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1918_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
if (lean_obj_tag(v_a_1899_) == 1)
{
lean_object* v_val_1903_; uint64_t v___x_1904_; lean_object* v___x_1905_; lean_object* v_r_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
lean_dec(v_a_1754_);
v_val_1903_ = lean_ctor_get(v_a_1899_, 0);
lean_inc(v_val_1903_);
lean_dec_ref_known(v_a_1899_, 1);
v___x_1904_ = lean_unbox_uint64(v_val_1903_);
lean_dec(v_val_1903_);
v___x_1905_ = lean_uint64_to_nat(v___x_1904_);
v_r_1906_ = l_Lean_mkRawNatLit(v___x_1905_);
v___x_1907_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1908_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__27, &l_Lean_Meta_normLitValue___closed__27_once, _init_l_Lean_Meta_normLitValue___closed__27);
v___x_1909_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__29, &l_Lean_Meta_normLitValue___closed__29_once, _init_l_Lean_Meta_normLitValue___closed__29);
lean_inc_ref(v_r_1906_);
v___x_1910_ = l_Lean_Expr_app___override(v___x_1909_, v_r_1906_);
v___x_1911_ = l_Lean_mkApp3(v___x_1907_, v___x_1908_, v_r_1906_, v___x_1910_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1911_);
v___x_1913_ = v___x_1901_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
else
{
lean_object* v___x_1916_; 
lean_dec(v_a_1899_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v_a_1754_);
v___x_1916_ = v___x_1901_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1754_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v_a_1754_);
v_a_1919_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1898_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1898_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_a_1754_);
v_a_1928_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1881_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1881_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec(v_a_1754_);
v_a_1937_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1864_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1864_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec(v_a_1754_);
v_a_1946_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1847_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1847_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_a_1754_);
v_a_1955_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1833_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1833_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec(v_a_1754_);
v_a_1964_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1812_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1812_);
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
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec(v_a_1754_);
v_a_1973_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1788_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1788_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec(v_a_1754_);
v_a_1982_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1765_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1765_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec(v_a_1754_);
v_a_1991_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1755_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1755_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue___boxed(lean_object* v_e_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Meta_normLitValue(v_e_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue(lean_object* v_e_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v___x_2012_; lean_object* v_a_2013_; lean_object* v___x_2014_; 
v___x_2012_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2006_, v_a_2008_);
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref(v___x_2012_);
v___x_2014_ = l_Lean_Meta_getNatValue_x3f(v_a_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2215_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2215_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2215_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
if (lean_obj_tag(v_a_2015_) == 0)
{
lean_object* v___x_2019_; 
lean_del_object(v___x_2017_);
lean_inc(v_a_2013_);
v___x_2019_ = l_Lean_Meta_getIntValue_x3f(v_a_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2201_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2201_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2201_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
uint8_t v___x_2024_; 
v___x_2024_ = 1;
if (lean_obj_tag(v_a_2020_) == 0)
{
lean_object* v___x_2025_; 
lean_del_object(v___x_2022_);
lean_inc(v_a_2013_);
v___x_2025_ = l_Lean_Meta_getFinValue_x3f(v_a_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2188_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2188_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2188_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
if (lean_obj_tag(v_a_2026_) == 0)
{
lean_object* v___x_2030_; 
lean_del_object(v___x_2028_);
lean_inc(v_a_2013_);
v___x_2030_ = l_Lean_Meta_getBitVecValue_x3f(v_a_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2175_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2175_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2175_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
if (lean_obj_tag(v_a_2031_) == 0)
{
lean_object* v___x_2035_; 
lean_inc(v_a_2013_);
v___x_2035_ = l_Lean_Meta_getStringValue_x3f(v_a_2013_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v___x_2036_; 
lean_del_object(v___x_2033_);
lean_inc(v_a_2013_);
v___x_2036_ = l_Lean_Meta_getCharValue_x3f(v_a_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2158_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2158_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2158_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
if (lean_obj_tag(v_a_2037_) == 0)
{
lean_object* v___x_2041_; 
lean_del_object(v___x_2039_);
lean_inc(v_a_2013_);
v___x_2041_ = l_Lean_Meta_getUInt8Value_x3f(v_a_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2145_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2145_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2145_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
if (lean_obj_tag(v_a_2042_) == 0)
{
lean_object* v___x_2046_; 
lean_del_object(v___x_2044_);
lean_inc(v_a_2013_);
v___x_2046_ = l_Lean_Meta_getUInt16Value_x3f(v_a_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2132_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2132_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2132_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
if (lean_obj_tag(v_a_2047_) == 0)
{
lean_object* v___x_2051_; 
lean_del_object(v___x_2049_);
lean_inc(v_a_2013_);
v___x_2051_ = l_Lean_Meta_getUInt32Value_x3f(v_a_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2119_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2119_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2119_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
if (lean_obj_tag(v_a_2052_) == 0)
{
lean_object* v___x_2056_; 
lean_del_object(v___x_2054_);
lean_inc(v_a_2013_);
v___x_2056_ = l_Lean_Meta_getUInt64Value_x3f(v_a_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2106_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2106_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2106_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
if (lean_obj_tag(v_a_2057_) == 0)
{
lean_object* v___x_2061_; 
lean_del_object(v___x_2059_);
lean_inc(v_a_2013_);
v___x_2061_ = l_Lean_Meta_getFloatValue_x3f(v_a_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2093_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2093_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2093_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
if (lean_obj_tag(v_a_2062_) == 0)
{
lean_object* v___x_2066_; 
lean_del_object(v___x_2064_);
v___x_2066_ = l_Lean_Meta_getFloat32Value_x3f(v_a_2013_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2080_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2080_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2080_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
if (lean_obj_tag(v_a_2067_) == 0)
{
uint8_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2071_ = 0;
v___x_2072_ = lean_box(v___x_2071_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2072_);
v___x_2074_ = v___x_2069_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_dec_ref_known(v_a_2067_, 1);
v___x_2076_ = lean_box(v___x_2024_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2076_);
v___x_2078_ = v___x_2069_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_a_2081_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2066_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2066_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
lean_dec_ref_known(v_a_2062_, 1);
lean_dec(v_a_2013_);
v___x_2089_ = lean_box(v___x_2024_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2089_);
v___x_2091_ = v___x_2064_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v_a_2013_);
v_a_2094_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2061_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2061_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
lean_dec_ref_known(v_a_2057_, 1);
lean_dec(v_a_2013_);
v___x_2102_ = lean_box(v___x_2024_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2102_);
v___x_2104_ = v___x_2059_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v_a_2013_);
v_a_2107_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2056_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2056_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
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
lean_object* v___x_2115_; lean_object* v___x_2117_; 
lean_dec_ref_known(v_a_2052_, 1);
lean_dec(v_a_2013_);
v___x_2115_ = lean_box(v___x_2024_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2115_);
v___x_2117_ = v___x_2054_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_a_2013_);
v_a_2120_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2051_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2051_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
lean_dec_ref_known(v_a_2047_, 1);
lean_dec(v_a_2013_);
v___x_2128_ = lean_box(v___x_2024_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2128_);
v___x_2130_ = v___x_2049_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_a_2013_);
v_a_2133_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2046_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2046_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
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
else
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
lean_dec_ref_known(v_a_2042_, 1);
lean_dec(v_a_2013_);
v___x_2141_ = lean_box(v___x_2024_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2141_);
v___x_2143_ = v___x_2044_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_a_2013_);
v_a_2146_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2041_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2041_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
lean_dec_ref_known(v_a_2037_, 1);
lean_dec(v_a_2013_);
v___x_2154_ = lean_box(v___x_2024_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2154_);
v___x_2156_ = v___x_2039_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_a_2013_);
v_a_2159_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2036_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2036_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
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
else
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
lean_dec_ref_known(v___x_2035_, 1);
lean_dec(v_a_2013_);
v___x_2167_ = lean_box(v___x_2024_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2167_);
v___x_2169_ = v___x_2033_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
lean_dec_ref_known(v_a_2031_, 1);
lean_dec(v_a_2013_);
v___x_2171_ = lean_box(v___x_2024_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2171_);
v___x_2173_ = v___x_2033_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_a_2013_);
v_a_2176_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2030_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2030_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
lean_dec_ref_known(v_a_2026_, 1);
lean_dec(v_a_2013_);
v___x_2184_ = lean_box(v___x_2024_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2184_);
v___x_2186_ = v___x_2028_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_a_2013_);
v_a_2189_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2025_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2025_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
lean_dec_ref_known(v_a_2020_, 1);
lean_dec(v_a_2013_);
v___x_2197_ = lean_box(v___x_2024_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2197_);
v___x_2199_ = v___x_2022_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_a_2013_);
v_a_2202_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2019_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2019_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
lean_dec_ref_known(v_a_2015_, 1);
lean_dec(v_a_2013_);
v___x_2210_ = 1;
v___x_2211_ = lean_box(v___x_2210_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2211_);
v___x_2213_ = v___x_2017_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_a_2013_);
v_a_2216_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2014_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2014_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue___boxed(lean_object* v_e_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Meta_isLitValue(v_e_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
return v_res_2230_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__2(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = lean_box(0);
v___x_2236_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__1));
v___x_2237_ = l_Lean_mkConst(v___x_2236_, v___x_2235_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__5(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = lean_box(0);
v___x_2243_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__4));
v___x_2244_ = l_Lean_mkConst(v___x_2243_, v___x_2242_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__7(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_box(0);
v___x_2249_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__6));
v___x_2250_ = l_Lean_mkConst(v___x_2249_, v___x_2248_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__10(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__9));
v___x_2257_ = l_Lean_mkConst(v___x_2256_, v___x_2255_);
return v___x_2257_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__11(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_unsigned_to_nat(1u);
v___x_2259_ = lean_nat_to_int(v___x_2258_);
return v___x_2259_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__15(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2265_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_2266_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__14));
v___x_2267_ = l_Lean_mkConst(v___x_2266_, v___x_2265_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__16(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = lean_box(0);
v___x_2269_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_2270_ = l_Lean_mkConst(v___x_2269_, v___x_2268_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__19(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_box(0);
v___x_2275_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__18));
v___x_2276_ = l_Lean_mkConst(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__22(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_box(0);
v___x_2281_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__21));
v___x_2282_ = l_Lean_mkConst(v___x_2281_, v___x_2280_);
return v___x_2282_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__25(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_box(0);
v___x_2288_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__24));
v___x_2289_ = l_Lean_mkConst(v___x_2288_, v___x_2287_);
return v___x_2289_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__28(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_box(0);
v___x_2295_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__27));
v___x_2296_ = l_Lean_mkConst(v___x_2295_, v___x_2294_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor(lean_object* v_e_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2303_; lean_object* v_a_2304_; lean_object* v___x_2305_; 
v___x_2303_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2297_, v_a_2299_);
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref(v___x_2303_);
v___x_2305_ = l_Lean_Meta_getNatValue_x3f(v_a_2304_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2395_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2395_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2395_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
if (lean_obj_tag(v_a_2306_) == 1)
{
lean_object* v_val_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
lean_dec(v_a_2304_);
v_val_2310_ = lean_ctor_get(v_a_2306_, 0);
lean_inc(v_val_2310_);
lean_dec_ref_known(v_a_2306_, 1);
v___x_2311_ = lean_unsigned_to_nat(0u);
v___x_2312_ = lean_nat_dec_eq(v_val_2310_, v___x_2311_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2313_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__2, &l_Lean_Meta_litToCtor___closed__2_once, _init_l_Lean_Meta_litToCtor___closed__2);
v___x_2314_ = lean_unsigned_to_nat(1u);
v___x_2315_ = lean_nat_sub(v_val_2310_, v___x_2314_);
lean_dec(v_val_2310_);
v___x_2316_ = l_Lean_mkNatLit(v___x_2315_);
v___x_2317_ = l_Lean_Expr_app___override(v___x_2313_, v___x_2316_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2317_);
v___x_2319_ = v___x_2308_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
else
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
lean_dec(v_val_2310_);
v___x_2321_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__5, &l_Lean_Meta_litToCtor___closed__5_once, _init_l_Lean_Meta_litToCtor___closed__5);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2321_);
v___x_2323_ = v___x_2308_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
else
{
lean_object* v___x_2325_; 
lean_del_object(v___x_2308_);
lean_dec(v_a_2306_);
lean_inc(v_a_2304_);
v___x_2325_ = l_Lean_Meta_getIntValue_x3f(v_a_2304_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2386_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2386_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2386_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
if (lean_obj_tag(v_a_2326_) == 1)
{
lean_object* v_val_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
lean_dec(v_a_2304_);
v_val_2330_ = lean_ctor_get(v_a_2326_, 0);
lean_inc(v_val_2330_);
lean_dec_ref_known(v_a_2326_, 1);
v___x_2331_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_2332_ = lean_int_dec_lt(v_val_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2333_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__7, &l_Lean_Meta_litToCtor___closed__7_once, _init_l_Lean_Meta_litToCtor___closed__7);
v___x_2334_ = l_Int_toNat(v_val_2330_);
lean_dec(v_val_2330_);
v___x_2335_ = l_Lean_mkNatLit(v___x_2334_);
v___x_2336_ = l_Lean_Expr_app___override(v___x_2333_, v___x_2335_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2336_);
v___x_2338_ = v___x_2328_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
else
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2340_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__10, &l_Lean_Meta_litToCtor___closed__10_once, _init_l_Lean_Meta_litToCtor___closed__10);
v___x_2341_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__11, &l_Lean_Meta_litToCtor___closed__11_once, _init_l_Lean_Meta_litToCtor___closed__11);
v___x_2342_ = lean_int_add(v_val_2330_, v___x_2341_);
lean_dec(v_val_2330_);
v___x_2343_ = lean_int_neg(v___x_2342_);
lean_dec(v___x_2342_);
v___x_2344_ = l_Int_toNat(v___x_2343_);
lean_dec(v___x_2343_);
v___x_2345_ = l_Lean_mkNatLit(v___x_2344_);
v___x_2346_ = l_Lean_Expr_app___override(v___x_2340_, v___x_2345_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2346_);
v___x_2348_ = v___x_2328_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
else
{
lean_object* v___x_2350_; 
lean_del_object(v___x_2328_);
lean_dec(v_a_2326_);
lean_inc(v_a_2304_);
v___x_2350_ = l_Lean_Meta_getFinValue_x3f(v_a_2304_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2377_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2377_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2377_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
if (lean_obj_tag(v_a_2351_) == 1)
{
lean_object* v_val_2355_; lean_object* v_fst_2356_; lean_object* v_snd_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; 
lean_dec(v_a_2304_);
v_val_2355_ = lean_ctor_get(v_a_2351_, 0);
lean_inc(v_val_2355_);
lean_dec_ref_known(v_a_2351_, 1);
v_fst_2356_ = lean_ctor_get(v_val_2355_, 0);
lean_inc(v_fst_2356_);
v_snd_2357_ = lean_ctor_get(v_val_2355_, 1);
lean_inc(v_snd_2357_);
lean_dec(v_val_2355_);
v___x_2358_ = l_Lean_mkNatLit(v_snd_2357_);
v___x_2359_ = l_Lean_mkNatLit(v_fst_2356_);
v___x_2360_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__15, &l_Lean_Meta_litToCtor___closed__15_once, _init_l_Lean_Meta_litToCtor___closed__15);
v___x_2361_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__16, &l_Lean_Meta_litToCtor___closed__16_once, _init_l_Lean_Meta_litToCtor___closed__16);
v___x_2362_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__19, &l_Lean_Meta_litToCtor___closed__19_once, _init_l_Lean_Meta_litToCtor___closed__19);
lean_inc_ref_n(v___x_2359_, 2);
lean_inc_ref_n(v___x_2358_, 2);
v___x_2363_ = l_Lean_mkApp4(v___x_2360_, v___x_2361_, v___x_2362_, v___x_2358_, v___x_2359_);
v___x_2364_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__22, &l_Lean_Meta_litToCtor___closed__22_once, _init_l_Lean_Meta_litToCtor___closed__22);
v___x_2365_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__25, &l_Lean_Meta_litToCtor___closed__25_once, _init_l_Lean_Meta_litToCtor___closed__25);
v___x_2366_ = l_Lean_mkAppB(v___x_2365_, v___x_2358_, v___x_2359_);
v___x_2367_ = l_Lean_eagerReflBoolTrue;
v___x_2368_ = l_Lean_mkApp3(v___x_2364_, v___x_2363_, v___x_2366_, v___x_2367_);
v___x_2369_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__28, &l_Lean_Meta_litToCtor___closed__28_once, _init_l_Lean_Meta_litToCtor___closed__28);
v___x_2370_ = l_Lean_mkApp3(v___x_2369_, v___x_2359_, v___x_2358_, v___x_2368_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2370_);
v___x_2372_ = v___x_2353_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
else
{
lean_object* v___x_2375_; 
lean_dec(v_a_2351_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v_a_2304_);
v___x_2375_ = v___x_2353_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2304_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v_a_2304_);
v_a_2378_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2350_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2350_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_a_2304_);
v_a_2387_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2325_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2325_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_a_2304_);
v_a_2396_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2305_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2305_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor___boxed(lean_object* v_e_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Meta_litToCtor(v_e_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(lean_object* v_fst_2413_, lean_object* v_snd_2414_, lean_object* v_x_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2421_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0));
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_fst_2413_);
lean_ctor_set(v___x_2422_, 1, v_snd_2414_);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2426_, lean_object* v_snd_2427_, lean_object* v_x_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2426_, v_snd_2427_, v_x_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(lean_object* v_f_2446_, lean_object* v_a_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___y_2454_; lean_object* v_snd_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2562_; 
v_snd_2474_ = lean_ctor_get(v_a_2447_, 1);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_a_2447_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v_a_2447_, 0);
lean_dec(v_unused_2563_);
v___x_2476_ = v_a_2447_;
v_isShared_2477_ = v_isSharedCheck_2562_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_snd_2474_);
lean_dec(v_a_2447_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2562_;
goto v_resetjp_2475_;
}
v___jp_2453_:
{
if (lean_obj_tag(v___y_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2465_; 
v_a_2455_ = lean_ctor_get(v___y_2454_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___y_2454_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2457_ = v___y_2454_;
v_isShared_2458_ = v_isSharedCheck_2465_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___y_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2465_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
if (lean_obj_tag(v_a_2455_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; 
lean_dec_ref(v_f_2446_);
v_a_2459_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v_a_2455_, 1);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v_a_2459_);
v___x_2461_ = v___x_2457_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
else
{
lean_object* v_a_2463_; 
lean_del_object(v___x_2457_);
v_a_2463_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v_a_2455_, 1);
v_a_2447_ = v_a_2463_;
goto _start;
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v_f_2446_);
v_a_2466_ = lean_ctor_get(v___y_2454_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___y_2454_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___y_2454_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___y_2454_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
v_resetjp_2475_:
{
lean_object* v_fst_2478_; lean_object* v_snd_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2561_; 
v_fst_2478_ = lean_ctor_get(v_snd_2474_, 0);
v_snd_2479_ = lean_ctor_get(v_snd_2474_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_snd_2474_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2481_ = v_snd_2474_;
v_isShared_2482_ = v_isSharedCheck_2561_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_snd_2479_);
lean_inc(v_fst_2478_);
lean_dec(v_snd_2474_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2561_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; 
lean_inc(v_fst_2478_);
v___x_2483_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_fst_2478_, v___y_2449_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2552_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2552_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2552_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2488_ = l_Lean_Expr_cleanupAnnotations(v_a_2484_);
v___x_2489_ = l_Lean_Expr_isApp(v___x_2488_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_dec_ref(v___x_2488_);
lean_del_object(v___x_2486_);
lean_del_object(v___x_2481_);
lean_del_object(v___x_2476_);
v___x_2490_ = lean_box(0);
v___x_2491_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2478_, v_snd_2479_, v___x_2490_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
v___y_2454_ = v___x_2491_;
goto v___jp_2453_;
}
else
{
lean_object* v_arg_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v_arg_2492_ = lean_ctor_get(v___x_2488_, 1);
lean_inc_ref(v_arg_2492_);
v___x_2493_ = lean_box(0);
v___x_2494_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2488_);
v___x_2495_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2));
v___x_2496_ = l_Lean_Expr_isConstOf(v___x_2494_, v___x_2495_);
if (v___x_2496_ == 0)
{
uint8_t v___x_2497_; 
lean_del_object(v___x_2486_);
v___x_2497_ = l_Lean_Expr_isApp(v___x_2494_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec_ref(v___x_2494_);
lean_dec_ref(v_arg_2492_);
lean_del_object(v___x_2481_);
lean_del_object(v___x_2476_);
v___x_2498_ = lean_box(0);
v___x_2499_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2478_, v_snd_2479_, v___x_2498_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
v___y_2454_ = v___x_2499_;
goto v___jp_2453_;
}
else
{
lean_object* v_arg_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v_arg_2500_ = lean_ctor_get(v___x_2494_, 1);
lean_inc_ref(v_arg_2500_);
v___x_2501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2494_);
v___x_2502_ = l_Lean_Expr_isApp(v___x_2501_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec_ref(v___x_2501_);
lean_dec_ref(v_arg_2500_);
lean_dec_ref(v_arg_2492_);
lean_del_object(v___x_2481_);
lean_del_object(v___x_2476_);
v___x_2503_ = lean_box(0);
v___x_2504_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2478_, v_snd_2479_, v___x_2503_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
v___y_2454_ = v___x_2504_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v___x_2505_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2501_);
v___x_2506_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4));
v___x_2507_ = l_Lean_Expr_isConstOf(v___x_2505_, v___x_2506_);
lean_dec_ref(v___x_2505_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_dec_ref(v_arg_2500_);
lean_dec_ref(v_arg_2492_);
lean_del_object(v___x_2481_);
lean_del_object(v___x_2476_);
v___x_2508_ = lean_box(0);
v___x_2509_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2478_, v_snd_2479_, v___x_2508_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
v___y_2454_ = v___x_2509_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2510_; 
lean_inc_ref(v_f_2446_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
v___x_2510_ = lean_apply_6(v_f_2446_, v_arg_2500_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, lean_box(0));
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2534_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2534_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2534_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
if (lean_obj_tag(v_a_2511_) == 1)
{
lean_object* v_val_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
lean_del_object(v___x_2513_);
lean_dec(v_fst_2478_);
v_val_2515_ = lean_ctor_get(v_a_2511_, 0);
lean_inc(v_val_2515_);
lean_dec_ref_known(v_a_2511_, 1);
v___x_2516_ = lean_array_push(v_snd_2479_, v_val_2515_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 1, v___x_2516_);
lean_ctor_set(v___x_2481_, 0, v_arg_2492_);
v___x_2518_ = v___x_2481_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_arg_2492_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 1, v___x_2518_);
lean_ctor_set(v___x_2476_, 0, v___x_2493_);
v___x_2520_ = v___x_2476_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
v_a_2447_ = v___x_2520_;
goto _start;
}
}
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2526_; 
lean_dec(v_a_2511_);
lean_dec_ref(v_arg_2492_);
lean_dec_ref(v_f_2446_);
v___x_2524_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5));
if (v_isShared_2482_ == 0)
{
v___x_2526_ = v___x_2481_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_fst_2478_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_snd_2479_);
v___x_2526_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2528_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 1, v___x_2526_);
lean_ctor_set(v___x_2476_, 0, v___x_2524_);
v___x_2528_ = v___x_2476_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2530_; 
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2528_);
v___x_2530_ = v___x_2513_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v_arg_2492_);
lean_del_object(v___x_2481_);
lean_dec(v_snd_2479_);
lean_dec(v_fst_2478_);
lean_del_object(v___x_2476_);
lean_dec_ref(v_f_2446_);
v_a_2535_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2510_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2510_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2544_; 
lean_dec_ref(v___x_2494_);
lean_dec_ref(v_arg_2492_);
lean_dec_ref(v_f_2446_);
if (v_isShared_2482_ == 0)
{
v___x_2544_ = v___x_2481_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_fst_2478_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_snd_2479_);
v___x_2544_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2546_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 1, v___x_2544_);
lean_ctor_set(v___x_2476_, 0, v___x_2493_);
v___x_2546_ = v___x_2476_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2548_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2546_);
v___x_2548_ = v___x_2486_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_del_object(v___x_2481_);
lean_dec(v_snd_2479_);
lean_dec(v_fst_2478_);
lean_del_object(v___x_2476_);
lean_dec_ref(v_f_2446_);
v_a_2553_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2483_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2483_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___boxed(lean_object* v_f_2564_, lean_object* v_a_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_2564_, v_a_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg(lean_object* v_e_2574_, lean_object* v_f_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2618_; 
v___x_2581_ = l_Lean_Expr_consumeMData(v_e_2574_);
v___x_2582_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_2581_, v_a_2577_);
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2618_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2618_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2587_ = ((lean_object*)(l_Lean_Meta_getListLitOf_x3f___redArg___closed__0));
v___x_2588_ = lean_box(0);
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v_a_2583_);
lean_ctor_set(v___x_2589_, 1, v___x_2587_);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_2575_, v___x_2590_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2609_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2609_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2609_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_fst_2596_; 
v_fst_2596_ = lean_ctor_get(v_a_2592_, 0);
if (lean_obj_tag(v_fst_2596_) == 0)
{
lean_object* v_snd_2597_; lean_object* v_snd_2598_; lean_object* v___x_2600_; 
v_snd_2597_ = lean_ctor_get(v_a_2592_, 1);
lean_inc(v_snd_2597_);
lean_dec(v_a_2592_);
v_snd_2598_ = lean_ctor_get(v_snd_2597_, 1);
lean_inc(v_snd_2598_);
lean_dec(v_snd_2597_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 0, v_snd_2598_);
v___x_2600_ = v___x_2585_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_snd_2598_);
v___x_2600_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2602_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2600_);
v___x_2602_ = v___x_2594_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
else
{
lean_object* v_val_2605_; lean_object* v___x_2607_; 
lean_inc_ref(v_fst_2596_);
lean_dec(v_a_2592_);
lean_del_object(v___x_2585_);
v_val_2605_ = lean_ctor_get(v_fst_2596_, 0);
lean_inc(v_val_2605_);
lean_dec_ref_known(v_fst_2596_, 1);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v_val_2605_);
v___x_2607_ = v___x_2594_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_val_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_del_object(v___x_2585_);
v_a_2610_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2591_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2591_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___boxed(lean_object* v_e_2619_, lean_object* v_f_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_2619_, v_f_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec_ref(v_e_2619_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f(lean_object* v_00_u03b1_2627_, lean_object* v_e_2628_, lean_object* v_f_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_2628_, v_f_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___boxed(lean_object* v_00_u03b1_2636_, lean_object* v_e_2637_, lean_object* v_f_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_Meta_getListLitOf_x3f(v_00_u03b1_2636_, v_e_2637_, v_f_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec_ref(v_e_2637_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(lean_object* v_00_u03b1_2645_, lean_object* v_f_2646_, lean_object* v_inst_2647_, lean_object* v_a_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_2646_, v_a_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___boxed(lean_object* v_00_u03b1_2655_, lean_object* v_f_2656_, lean_object* v_inst_2657_, lean_object* v_a_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(v_00_u03b1_2655_, v_f_2656_, v_inst_2657_, v_a_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0(lean_object* v_s_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2671_, 0, v_s_2665_);
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0___boxed(lean_object* v_s_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_Meta_getListLit_x3f___lam__0(v_s_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f(lean_object* v_e_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v___f_2687_; lean_object* v___x_2688_; 
v___f_2687_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_2688_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_2681_, v___f_2687_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___boxed(lean_object* v_e_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Meta_getListLit_x3f(v_e_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec_ref(v_e_2689_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg(lean_object* v_e_2700_, lean_object* v_f_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v_a_2709_; lean_object* v___x_2710_; 
v___x_2707_ = l_Lean_Expr_consumeMData(v_e_2700_);
v___x_2708_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_2707_, v_a_2703_);
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2709_);
lean_dec_ref(v___x_2708_);
v___x_2710_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2709_, v_a_2703_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2729_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2729_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2729_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = l_Lean_Expr_cleanupAnnotations(v_a_2711_);
v___x_2721_ = l_Lean_Expr_isApp(v___x_2720_);
if (v___x_2721_ == 0)
{
lean_dec_ref(v___x_2720_);
lean_dec_ref(v_f_2701_);
goto v___jp_2715_;
}
else
{
lean_object* v_arg_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v_arg_2722_ = lean_ctor_get(v___x_2720_, 1);
lean_inc_ref(v_arg_2722_);
v___x_2723_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2720_);
v___x_2724_ = l_Lean_Expr_isApp(v___x_2723_);
if (v___x_2724_ == 0)
{
lean_dec_ref(v___x_2723_);
lean_dec_ref(v_arg_2722_);
lean_dec_ref(v_f_2701_);
goto v___jp_2715_;
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2725_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2723_);
v___x_2726_ = ((lean_object*)(l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1));
v___x_2727_ = l_Lean_Expr_isConstOf(v___x_2725_, v___x_2726_);
lean_dec_ref(v___x_2725_);
if (v___x_2727_ == 0)
{
lean_dec_ref(v_arg_2722_);
lean_dec_ref(v_f_2701_);
goto v___jp_2715_;
}
else
{
lean_object* v___x_2728_; 
lean_del_object(v___x_2713_);
v___x_2728_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_arg_2722_, v_f_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
lean_dec_ref(v_arg_2722_);
return v___x_2728_;
}
}
}
v___jp_2715_:
{
lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2716_ = lean_box(0);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2716_);
v___x_2718_ = v___x_2713_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec_ref(v_f_2701_);
v_a_2730_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2710_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2710_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___boxed(lean_object* v_e_2738_, lean_object* v_f_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2738_, v_f_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec_ref(v_e_2738_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f(lean_object* v_00_u03b1_2746_, lean_object* v_e_2747_, lean_object* v_f_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2747_, v_f_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_e_2756_, lean_object* v_f_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Meta_getArrayLitOf_x3f(v_00_u03b1_2755_, v_e_2756_, v_f_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
lean_dec_ref(v_e_2756_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object* v_e_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v___f_2770_; lean_object* v___x_2771_; 
v___f_2770_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_2771_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2764_, v___f_2770_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f___boxed(lean_object* v_e_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_Meta_getArrayLit_x3f(v_e_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec_ref(v_e_2772_);
return v_res_2778_;
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
