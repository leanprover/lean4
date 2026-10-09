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
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_getOfNatValue_x3f(lean_object* v_e_21_, lean_object* v_typeDeclName_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_){
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
v___x_39_ = l_Lean_Expr_isApp(v___x_38_);
if (v___x_39_ == 0)
{
lean_dec_ref(v___x_38_);
goto v___jp_28_;
}
else
{
lean_object* v_arg_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v_arg_40_ = lean_ctor_get(v___x_38_, 1);
lean_inc_ref(v_arg_40_);
v___x_41_ = l_Lean_Expr_appFnCleanup___redArg(v___x_38_);
v___x_42_ = l_Lean_Expr_isApp(v___x_41_);
if (v___x_42_ == 0)
{
lean_dec_ref(v___x_41_);
lean_dec_ref(v_arg_40_);
goto v___jp_28_;
}
else
{
lean_object* v_arg_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v_arg_43_ = lean_ctor_get(v___x_41_, 1);
lean_inc_ref(v_arg_43_);
v___x_44_ = l_Lean_Expr_appFnCleanup___redArg(v___x_41_);
v___x_45_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_46_ = l_Lean_Expr_isConstOf(v___x_44_, v___x_45_);
lean_dec_ref(v___x_44_);
if (v___x_46_ == 0)
{
lean_dec_ref(v_arg_43_);
lean_dec_ref(v_arg_40_);
goto v___jp_28_;
}
else
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_whnfD(v_arg_43_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
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
lean_dec_ref(v_arg_40_);
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
v___x_58_ = l_Lean_Expr_consumeMData(v_arg_40_);
lean_dec_ref(v_arg_40_);
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
lean_dec_ref(v_arg_40_);
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
LEAN_EXPORT void l_Lean_Meta_getOfNatValue_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_21_ = stack[0].m_obj;
lean_object* v_typeDeclName_22_ = stack[1].m_obj;
lean_object* v_a_23_ = stack[2].m_obj;
lean_object* v_a_24_ = stack[3].m_obj;
lean_object* v_a_25_ = stack[4].m_obj;
lean_object* v_a_26_ = stack[5].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Lean_Meta_getOfNatValue_x3f(v_e_21_, v_typeDeclName_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f___boxed(lean_object* v_e_90_, lean_object* v_typeDeclName_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Meta_getOfNatValue_x3f(v_e_90_, v_typeDeclName_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_typeDeclName_91_);
return v_res_97_;
}
}
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object* v_e_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_e_107_; lean_object* v___x_108_; 
v_e_107_ = l_Lean_Expr_consumeMData(v_e_101_);
v___x_108_ = l_Lean_Meta_getRawNatValue_x3f(v_e_107_);
if (lean_obj_tag(v___x_108_) == 1)
{
lean_object* v___x_109_; 
lean_dec_ref(v_e_107_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec(v___x_108_);
v___x_110_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_111_ = l_Lean_Meta_getOfNatValue_x3f(v_e_107_, v___x_110_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_132_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_132_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_132_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_132_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
if (lean_obj_tag(v_a_112_) == 1)
{
lean_object* v_val_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_127_; 
v_val_116_ = lean_ctor_get(v_a_112_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v_a_112_);
if (v_isSharedCheck_127_ == 0)
{
v___x_118_ = v_a_112_;
v_isShared_119_ = v_isSharedCheck_127_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_val_116_);
lean_dec(v_a_112_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_127_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_fst_120_; lean_object* v___x_122_; 
v_fst_120_ = lean_ctor_get(v_val_116_, 0);
lean_inc(v_fst_120_);
lean_dec(v_val_116_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v_fst_120_);
v___x_122_ = v___x_118_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_fst_120_);
v___x_122_ = v_reuseFailAlloc_126_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_124_; 
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_122_);
v___x_124_ = v___x_114_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
else
{
lean_object* v___x_128_; lean_object* v___x_130_; 
lean_dec(v_a_112_);
v___x_128_ = lean_box(0);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_128_);
v___x_130_ = v___x_114_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
v_a_133_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_111_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_111_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getNatValue_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_101_ = stack[0].m_obj;
lean_object* v_a_102_ = stack[1].m_obj;
lean_object* v_a_103_ = stack[2].m_obj;
lean_object* v_a_104_ = stack[3].m_obj;
lean_object* v_a_105_ = stack[4].m_obj;
lean_object* v_res_141_;
v_res_141_ = l_Lean_Meta_getNatValue_x3f(v_e_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
stack->m_obj
 = v_res_141_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getNatValue_x3f___boxed(lean_object* v_e_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Meta_getNatValue_x3f(v_e_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec_ref(v_e_142_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_getIntValue_x3f_spec__0(lean_object* v_a_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_nat_to_int(v_a_149_);
return v___x_150_;
}
}
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object* v_e_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
lean_inc_ref(v_e_159_);
v___x_169_ = l_Lean_Meta_getOfNatValue_x3f(v_e_159_, v___x_168_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_239_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_239_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_239_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_239_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
if (lean_obj_tag(v_a_170_) == 1)
{
lean_object* v_val_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_186_; 
lean_dec_ref(v_e_159_);
v_val_174_ = lean_ctor_get(v_a_170_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v_a_170_);
if (v_isSharedCheck_186_ == 0)
{
v___x_176_ = v_a_170_;
v_isShared_177_ = v_isSharedCheck_186_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_val_174_);
lean_dec(v_a_170_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_186_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_fst_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v_fst_178_ = lean_ctor_get(v_val_174_, 0);
lean_inc(v_fst_178_);
lean_dec(v_val_174_);
v___x_179_ = lean_nat_to_int(v_fst_178_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_179_);
v___x_181_ = v___x_176_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_185_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_181_);
v___x_183_ = v___x_172_;
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
}
}
else
{
lean_object* v___x_187_; 
lean_del_object(v___x_172_);
lean_dec(v_a_170_);
v___x_187_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_159_, v_a_161_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_187_, 1);
v___x_189_ = l_Lean_Expr_cleanupAnnotations(v_a_188_);
v___x_190_ = l_Lean_Expr_isApp(v___x_189_);
if (v___x_190_ == 0)
{
lean_dec_ref(v___x_189_);
goto v___jp_165_;
}
else
{
lean_object* v_arg_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_arg_191_ = lean_ctor_get(v___x_189_, 1);
lean_inc_ref(v_arg_191_);
v___x_192_ = l_Lean_Expr_appFnCleanup___redArg(v___x_189_);
v___x_193_ = l_Lean_Expr_isApp(v___x_192_);
if (v___x_193_ == 0)
{
lean_dec_ref(v___x_192_);
lean_dec_ref(v_arg_191_);
goto v___jp_165_;
}
else
{
lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_194_ = l_Lean_Expr_appFnCleanup___redArg(v___x_192_);
v___x_195_ = l_Lean_Expr_isApp(v___x_194_);
if (v___x_195_ == 0)
{
lean_dec_ref(v___x_194_);
lean_dec_ref(v_arg_191_);
goto v___jp_165_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_196_ = l_Lean_Expr_appFnCleanup___redArg(v___x_194_);
v___x_197_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_198_ = l_Lean_Expr_isConstOf(v___x_196_, v___x_197_);
lean_dec_ref(v___x_196_);
if (v___x_198_ == 0)
{
lean_dec_ref(v_arg_191_);
goto v___jp_165_;
}
else
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_191_, v___x_168_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_222_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_222_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_222_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_222_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
if (lean_obj_tag(v_a_200_) == 1)
{
lean_object* v_val_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_217_; 
v_val_204_ = lean_ctor_get(v_a_200_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v_a_200_);
if (v_isSharedCheck_217_ == 0)
{
v___x_206_ = v_a_200_;
v_isShared_207_ = v_isSharedCheck_217_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_val_204_);
lean_dec(v_a_200_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_217_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_fst_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v_fst_208_ = lean_ctor_get(v_val_204_, 0);
lean_inc(v_fst_208_);
lean_dec(v_val_204_);
v___x_209_ = lean_nat_to_int(v_fst_208_);
v___x_210_ = lean_int_neg(v___x_209_);
lean_dec(v___x_209_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_210_);
v___x_212_ = v___x_206_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_212_);
v___x_214_ = v___x_202_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
else
{
lean_object* v___x_218_; lean_object* v___x_220_; 
lean_dec(v_a_200_);
v___x_218_ = lean_box(0);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_218_);
v___x_220_ = v___x_202_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
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
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
v_a_223_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_199_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_199_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
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
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
v_a_231_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_187_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_187_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
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
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v_e_159_);
v_a_240_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_169_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_169_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
v___jp_165_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getIntValue_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_159_ = stack[0].m_obj;
lean_object* v_a_160_ = stack[1].m_obj;
lean_object* v_a_161_ = stack[2].m_obj;
lean_object* v_a_162_ = stack[3].m_obj;
lean_object* v_a_163_ = stack[4].m_obj;
lean_object* v_res_248_;
v_res_248_ = l_Lean_Meta_getIntValue_x3f(v_e_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntValue_x3f___boxed(lean_object* v_e_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Meta_getIntValue_x3f(v_e_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(lean_object* v_a_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_nat_to_int(v_a_256_);
v___x_258_ = l_Rat_ofInt(v___x_257_);
return v___x_258_;
}
}
lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(lean_object* v_e_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1));
lean_inc_ref(v_e_262_);
v___x_272_ = l_Lean_Meta_getOfNatValue_x3f(v_e_262_, v___x_271_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_342_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_342_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_342_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_342_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
if (lean_obj_tag(v_a_273_) == 1)
{
lean_object* v_val_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_289_; 
lean_dec_ref(v_e_262_);
v_val_277_ = lean_ctor_get(v_a_273_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v_a_273_);
if (v_isSharedCheck_289_ == 0)
{
v___x_279_ = v_a_273_;
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_val_277_);
lean_dec(v_a_273_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v_fst_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v_fst_281_ = lean_ctor_get(v_val_277_, 0);
lean_inc(v_fst_281_);
lean_dec(v_val_277_);
v___x_282_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(v_fst_281_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_282_);
v___x_284_ = v___x_279_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_288_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_286_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_284_);
v___x_286_ = v___x_275_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
else
{
lean_object* v___x_290_; 
lean_del_object(v___x_275_);
lean_dec(v_a_273_);
v___x_290_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_262_, v_a_264_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
v___x_292_ = l_Lean_Expr_cleanupAnnotations(v_a_291_);
v___x_293_ = l_Lean_Expr_isApp(v___x_292_);
if (v___x_293_ == 0)
{
lean_dec_ref(v___x_292_);
goto v___jp_268_;
}
else
{
lean_object* v_arg_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_arg_294_ = lean_ctor_get(v___x_292_, 1);
lean_inc_ref(v_arg_294_);
v___x_295_ = l_Lean_Expr_appFnCleanup___redArg(v___x_292_);
v___x_296_ = l_Lean_Expr_isApp(v___x_295_);
if (v___x_296_ == 0)
{
lean_dec_ref(v___x_295_);
lean_dec_ref(v_arg_294_);
goto v___jp_268_;
}
else
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_295_);
v___x_298_ = l_Lean_Expr_isApp(v___x_297_);
if (v___x_298_ == 0)
{
lean_dec_ref(v___x_297_);
lean_dec_ref(v_arg_294_);
goto v___jp_268_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_297_);
v___x_300_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_301_ = l_Lean_Expr_isConstOf(v___x_299_, v___x_300_);
lean_dec_ref(v___x_299_);
if (v___x_301_ == 0)
{
lean_dec_ref(v_arg_294_);
goto v___jp_268_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_294_, v___x_271_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_325_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_325_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_325_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_325_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
if (lean_obj_tag(v_a_303_) == 1)
{
lean_object* v_val_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_320_; 
v_val_307_ = lean_ctor_get(v_a_303_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_a_303_);
if (v_isSharedCheck_320_ == 0)
{
v___x_309_ = v_a_303_;
v_isShared_310_ = v_isSharedCheck_320_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_val_307_);
lean_dec(v_a_303_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_320_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v_fst_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v_fst_311_ = lean_ctor_get(v_val_307_, 0);
lean_inc(v_fst_311_);
lean_dec(v_val_307_);
v___x_312_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(v_fst_311_);
v___x_313_ = l_Rat_neg(v___x_312_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_313_);
v___x_315_ = v___x_309_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_319_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_317_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_315_);
v___x_317_ = v___x_305_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_323_; 
lean_dec(v_a_303_);
v___x_321_ = lean_box(0);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_321_);
v___x_323_ = v___x_305_;
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
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_a_326_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_302_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_302_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
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
}
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_a_334_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_290_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_290_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec_ref(v_e_262_);
v_a_343_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_272_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_272_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
v___jp_268_:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_box(0);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_262_ = stack[0].m_obj;
lean_object* v_a_263_ = stack[1].m_obj;
lean_object* v_a_264_ = stack[2].m_obj;
lean_object* v_a_265_ = stack[3].m_obj;
lean_object* v_a_266_ = stack[4].m_obj;
lean_object* v_res_351_;
v_res_351_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
stack->m_obj
 = v_res_351_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___boxed(lean_object* v_e_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
return v_res_358_;
}
}
lean_object* l_Lean_Meta_getRatValue_x3f(lean_object* v_e_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_370_; 
lean_inc_ref(v_e_364_);
v___x_370_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_364_, v_a_366_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v___x_372_ = l_Lean_Expr_cleanupAnnotations(v_a_371_);
v___x_373_ = l_Lean_Expr_isApp(v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec_ref(v___x_372_);
v___x_374_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_374_;
}
else
{
lean_object* v_arg_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_arg_375_ = lean_ctor_get(v___x_372_, 1);
lean_inc_ref(v_arg_375_);
v___x_376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_372_);
v___x_377_ = l_Lean_Expr_isApp(v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_dec_ref(v___x_376_);
lean_dec_ref(v_arg_375_);
v___x_378_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_378_;
}
else
{
lean_object* v_arg_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v_arg_379_ = lean_ctor_get(v___x_376_, 1);
lean_inc_ref(v_arg_379_);
v___x_380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_376_);
v___x_381_ = l_Lean_Expr_isApp(v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
lean_dec_ref(v___x_380_);
lean_dec_ref(v_arg_379_);
lean_dec_ref(v_arg_375_);
v___x_382_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_380_);
v___x_384_ = l_Lean_Expr_isApp(v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
lean_dec_ref(v___x_383_);
lean_dec_ref(v_arg_379_);
lean_dec_ref(v_arg_375_);
v___x_385_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = l_Lean_Expr_appFnCleanup___redArg(v___x_383_);
v___x_387_ = l_Lean_Expr_isApp(v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec_ref(v___x_386_);
lean_dec_ref(v_arg_379_);
lean_dec_ref(v_arg_375_);
v___x_388_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = l_Lean_Expr_appFnCleanup___redArg(v___x_386_);
v___x_390_ = l_Lean_Expr_isApp(v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_dec_ref(v___x_389_);
lean_dec_ref(v_arg_379_);
lean_dec_ref(v_arg_375_);
v___x_391_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_392_ = l_Lean_Expr_appFnCleanup___redArg(v___x_389_);
v___x_393_ = ((lean_object*)(l_Lean_Meta_getRatValue_x3f___closed__2));
v___x_394_ = l_Lean_Expr_isConstOf(v___x_392_, v___x_393_);
lean_dec_ref(v___x_392_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
lean_dec_ref(v_arg_379_);
lean_dec_ref(v_arg_375_);
v___x_395_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; 
lean_dec_ref(v_e_364_);
v___x_396_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_arg_379_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_439_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_439_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_439_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_439_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
if (lean_obj_tag(v_a_397_) == 1)
{
lean_object* v_val_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_del_object(v___x_399_);
v_val_401_ = lean_ctor_get(v_a_397_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v_a_397_, 1);
v___x_402_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1));
v___x_403_ = l_Lean_Meta_getOfNatValue_x3f(v_arg_375_, v___x_402_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_426_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_426_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_426_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_426_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
if (lean_obj_tag(v_a_404_) == 1)
{
lean_object* v_val_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_421_; 
v_val_408_ = lean_ctor_get(v_a_404_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_a_404_);
if (v_isSharedCheck_421_ == 0)
{
v___x_410_ = v_a_404_;
v_isShared_411_ = v_isSharedCheck_421_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_val_408_);
lean_dec(v_a_404_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_421_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_fst_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v_fst_412_ = lean_ctor_get(v_val_408_, 0);
lean_inc(v_fst_412_);
lean_dec(v_val_408_);
v___x_413_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(v_fst_412_);
v___x_414_ = l_Rat_div(v_val_401_, v___x_413_);
lean_dec(v_val_401_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_414_);
v___x_416_ = v___x_410_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_420_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_416_);
v___x_418_ = v___x_406_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_424_; 
lean_dec(v_a_404_);
lean_dec(v_val_401_);
v___x_422_ = lean_box(0);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_422_);
v___x_424_ = v___x_406_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v_val_401_);
v_a_427_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_403_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_403_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
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
lean_object* v___x_435_; lean_object* v___x_437_; 
lean_dec(v_a_397_);
lean_dec_ref(v_arg_375_);
v___x_435_ = lean_box(0);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_435_);
v___x_437_ = v___x_399_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
else
{
lean_dec_ref(v_arg_375_);
return v___x_396_;
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
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref(v_e_364_);
v_a_440_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_370_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_370_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getRatValue_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_364_ = stack[0].m_obj;
lean_object* v_a_365_ = stack[1].m_obj;
lean_object* v_a_366_ = stack[2].m_obj;
lean_object* v_a_367_ = stack[3].m_obj;
lean_object* v_a_368_ = stack[4].m_obj;
lean_object* v_res_448_;
v_res_448_ = l_Lean_Meta_getRatValue_x3f(v_e_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getRatValue_x3f___boxed(lean_object* v_e_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Meta_getRatValue_x3f(v_e_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
return v_res_455_;
}
}
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object* v_e_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_460_, v_a_462_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = l_Lean_Expr_cleanupAnnotations(v_a_470_);
v___x_472_ = l_Lean_Expr_isApp(v___x_471_);
if (v___x_472_ == 0)
{
lean_dec_ref(v___x_471_);
goto v___jp_466_;
}
else
{
lean_object* v_arg_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_arg_473_ = lean_ctor_get(v___x_471_, 1);
lean_inc_ref(v_arg_473_);
v___x_474_ = l_Lean_Expr_appFnCleanup___redArg(v___x_471_);
v___x_475_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_476_ = l_Lean_Expr_isConstOf(v___x_474_, v___x_475_);
lean_dec_ref(v___x_474_);
if (v___x_476_ == 0)
{
lean_dec_ref(v_arg_473_);
goto v___jp_466_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_Meta_getNatValue_x3f(v_arg_473_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec_ref(v_arg_473_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_499_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_499_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_499_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_499_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
if (lean_obj_tag(v_a_478_) == 1)
{
lean_object* v_val_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_494_; 
v_val_482_ = lean_ctor_get(v_a_478_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v_a_478_);
if (v_isSharedCheck_494_ == 0)
{
v___x_484_ = v_a_478_;
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_val_482_);
lean_dec(v_a_478_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint32_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_486_ = l_Char_ofNat(v_val_482_);
lean_dec(v_val_482_);
v___x_487_ = lean_box_uint32(v___x_486_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_487_);
v___x_489_ = v___x_484_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_489_);
v___x_491_ = v___x_480_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v___x_495_; lean_object* v___x_497_; 
lean_dec(v_a_478_);
v___x_495_ = lean_box(0);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_495_);
v___x_497_ = v___x_480_;
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
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
v_a_500_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_477_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_477_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
v_a_508_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_469_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_469_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
v___jp_466_:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_box(0);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getCharValue_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_460_ = stack[0].m_obj;
lean_object* v_a_461_ = stack[1].m_obj;
lean_object* v_a_462_ = stack[2].m_obj;
lean_object* v_a_463_ = stack[3].m_obj;
lean_object* v_a_464_ = stack[4].m_obj;
lean_object* v_res_516_;
v_res_516_ = l_Lean_Meta_getCharValue_x3f(v_e_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
stack->m_obj
 = v_res_516_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f___boxed(lean_object* v_e_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Meta_getCharValue_x3f(v_e_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStringValue_x3f(lean_object* v_e_524_){
_start:
{
if (lean_obj_tag(v_e_524_) == 9)
{
lean_object* v_a_525_; 
v_a_525_ = lean_ctor_get(v_e_524_, 0);
lean_inc_ref(v_a_525_);
lean_dec_ref_known(v_e_524_, 1);
if (lean_obj_tag(v_a_525_) == 1)
{
lean_object* v_val_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
v_val_526_ = lean_ctor_get(v_a_525_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_a_525_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v_a_525_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_val_526_);
lean_dec(v_a_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_val_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
lean_object* v___x_534_; 
lean_dec_ref(v_a_525_);
v___x_534_ = lean_box(0);
return v___x_534_;
}
}
else
{
lean_object* v___x_535_; 
lean_dec_ref(v_e_524_);
v___x_535_ = lean_box(0);
return v___x_535_;
}
}
}
lean_object* l_Lean_Meta_getFinValue_x3f(lean_object* v_e_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_546_ = l_Lean_Meta_getOfNatValue_x3f(v_e_539_, v___x_545_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_615_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_615_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_615_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_615_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
if (lean_obj_tag(v_a_547_) == 0)
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_box(0);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
lean_object* v_val_555_; lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_614_; 
lean_del_object(v___x_549_);
v_val_555_ = lean_ctor_get(v_a_547_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v_a_547_, 1);
v_fst_556_ = lean_ctor_get(v_val_555_, 0);
v_snd_557_ = lean_ctor_get(v_val_555_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_val_555_);
if (v_isSharedCheck_614_ == 0)
{
v___x_559_ = v_val_555_;
v_isShared_560_ = v_isSharedCheck_614_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_snd_557_);
lean_inc(v_fst_556_);
lean_dec(v_val_555_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_614_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = l_Lean_Expr_appArg_x21(v_snd_557_);
lean_dec(v_snd_557_);
v___x_562_ = l_Lean_Meta_whnfD(v___x_561_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_564_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
v___x_564_ = l_Lean_Meta_getNatValue_x3f(v_a_563_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
lean_dec(v_a_563_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_597_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_597_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_597_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_597_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
if (lean_obj_tag(v_a_565_) == 0)
{
lean_object* v___x_569_; lean_object* v___x_571_; 
lean_del_object(v___x_559_);
lean_dec(v_fst_556_);
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
lean_object* v_val_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_596_; 
v_val_573_ = lean_ctor_get(v_a_565_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v_a_565_);
if (v_isSharedCheck_596_ == 0)
{
v___x_575_ = v_a_565_;
v_isShared_576_ = v_isSharedCheck_596_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_val_573_);
lean_dec(v_a_565_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_596_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_zero_577_; uint8_t v_isZero_578_; 
v_zero_577_ = lean_unsigned_to_nat(0u);
v_isZero_578_ = lean_nat_dec_eq(v_val_573_, v_zero_577_);
if (v_isZero_578_ == 1)
{
lean_object* v___x_579_; lean_object* v___x_581_; 
lean_del_object(v___x_575_);
lean_dec(v_val_573_);
lean_del_object(v___x_559_);
lean_dec(v_fst_556_);
v___x_579_ = lean_box(0);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_579_);
v___x_581_ = v___x_567_;
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
else
{
lean_object* v_one_583_; lean_object* v_n_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v_one_583_ = lean_unsigned_to_nat(1u);
v_n_584_ = lean_nat_sub(v_val_573_, v_one_583_);
lean_dec(v_val_573_);
v___x_585_ = lean_nat_add(v_n_584_, v_one_583_);
lean_dec(v_n_584_);
v___x_586_ = lean_nat_mod(v_fst_556_, v___x_585_);
lean_dec(v_fst_556_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v___x_586_);
lean_ctor_set(v___x_559_, 0, v___x_585_);
v___x_588_ = v___x_559_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_586_);
v___x_588_ = v_reuseFailAlloc_595_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_590_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_588_);
v___x_590_ = v___x_575_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_590_);
v___x_592_ = v___x_567_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
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
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_del_object(v___x_559_);
lean_dec(v_fst_556_);
v_a_598_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_564_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_564_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_del_object(v___x_559_);
lean_dec(v_fst_556_);
v_a_606_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_562_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_562_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
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
v_a_616_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_546_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_546_);
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
}
LEAN_EXPORT void l_Lean_Meta_getFinValue_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_539_ = stack[0].m_obj;
lean_object* v_a_540_ = stack[1].m_obj;
lean_object* v_a_541_ = stack[2].m_obj;
lean_object* v_a_542_ = stack[3].m_obj;
lean_object* v_a_543_ = stack[4].m_obj;
lean_object* v_res_624_;
v_res_624_ = l_Lean_Meta_getFinValue_x3f(v_e_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
stack->m_obj
 = v_res_624_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f___boxed(lean_object* v_e_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_Meta_getFinValue_x3f(v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
return v_res_631_;
}
}
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object* v_e_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v_nExpr_724_; lean_object* v_vExpr_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___x_780_; 
lean_inc_ref(v_e_642_);
v___x_780_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_642_, v_a_644_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
v___x_782_ = l_Lean_Expr_cleanupAnnotations(v_a_781_);
v___x_783_ = l_Lean_Expr_isApp(v___x_782_);
if (v___x_783_ == 0)
{
lean_dec_ref(v___x_782_);
v___y_649_ = v_a_643_;
v___y_650_ = v_a_644_;
v___y_651_ = v_a_645_;
v___y_652_ = v_a_646_;
goto v___jp_648_;
}
else
{
lean_object* v_arg_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_arg_784_ = lean_ctor_get(v___x_782_, 1);
lean_inc_ref(v_arg_784_);
v___x_785_ = l_Lean_Expr_appFnCleanup___redArg(v___x_782_);
v___x_786_ = l_Lean_Expr_isApp(v___x_785_);
if (v___x_786_ == 0)
{
lean_dec_ref(v___x_785_);
lean_dec_ref(v_arg_784_);
v___y_649_ = v_a_643_;
v___y_650_ = v_a_644_;
v___y_651_ = v_a_645_;
v___y_652_ = v_a_646_;
goto v___jp_648_;
}
else
{
lean_object* v_arg_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_arg_787_ = lean_ctor_get(v___x_785_, 1);
lean_inc_ref(v_arg_787_);
v___x_788_ = l_Lean_Expr_appFnCleanup___redArg(v___x_785_);
v___x_789_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_790_ = l_Lean_Expr_isConstOf(v___x_788_, v___x_789_);
if (v___x_790_ == 0)
{
uint8_t v___x_791_; 
lean_dec_ref(v_arg_784_);
v___x_791_ = l_Lean_Expr_isApp(v___x_788_);
if (v___x_791_ == 0)
{
lean_dec_ref(v___x_788_);
lean_dec_ref(v_arg_787_);
v___y_649_ = v_a_643_;
v___y_650_ = v_a_644_;
v___y_651_ = v_a_645_;
v___y_652_ = v_a_646_;
goto v___jp_648_;
}
else
{
lean_object* v_arg_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_arg_792_ = lean_ctor_get(v___x_788_, 1);
lean_inc_ref(v_arg_792_);
v___x_793_ = l_Lean_Expr_appFnCleanup___redArg(v___x_788_);
v___x_794_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__4));
v___x_795_ = l_Lean_Expr_isConstOf(v___x_793_, v___x_794_);
lean_dec_ref(v___x_793_);
if (v___x_795_ == 0)
{
lean_dec_ref(v_arg_792_);
lean_dec_ref(v_arg_787_);
v___y_649_ = v_a_643_;
v___y_650_ = v_a_644_;
v___y_651_ = v_a_645_;
v___y_652_ = v_a_646_;
goto v___jp_648_;
}
else
{
lean_dec_ref(v_e_642_);
v_nExpr_724_ = v_arg_792_;
v_vExpr_725_ = v_arg_787_;
v___y_726_ = v_a_643_;
v___y_727_ = v_a_644_;
v___y_728_ = v_a_645_;
v___y_729_ = v_a_646_;
goto v___jp_723_;
}
}
}
else
{
lean_dec_ref(v___x_788_);
lean_dec_ref(v_e_642_);
v_nExpr_724_ = v_arg_787_;
v_vExpr_725_ = v_arg_784_;
v___y_726_ = v_a_643_;
v___y_727_ = v_a_644_;
v___y_728_ = v_a_645_;
v___y_729_ = v_a_646_;
goto v___jp_723_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_e_642_);
v_a_796_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_780_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_780_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
v___jp_648_:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_654_ = l_Lean_Meta_getOfNatValue_x3f(v_e_642_, v___x_653_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_714_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_714_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_714_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_714_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
if (lean_obj_tag(v_a_655_) == 0)
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_box(0);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v_val_663_; lean_object* v_fst_664_; lean_object* v_snd_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_713_; 
lean_del_object(v___x_657_);
v_val_663_ = lean_ctor_get(v_a_655_, 0);
lean_inc(v_val_663_);
lean_dec_ref_known(v_a_655_, 1);
v_fst_664_ = lean_ctor_get(v_val_663_, 0);
v_snd_665_ = lean_ctor_get(v_val_663_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_val_663_);
if (v_isSharedCheck_713_ == 0)
{
v___x_667_ = v_val_663_;
v_isShared_668_ = v_isSharedCheck_713_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_snd_665_);
lean_inc(v_fst_664_);
lean_dec(v_val_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_713_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = l_Lean_Expr_appArg_x21(v_snd_665_);
lean_dec(v_snd_665_);
v___x_670_ = l_Lean_Meta_whnfD(v___x_669_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = l_Lean_Meta_getNatValue_x3f(v_a_671_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v_a_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_696_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_696_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_696_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_696_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
if (lean_obj_tag(v_a_673_) == 0)
{
lean_object* v___x_677_; lean_object* v___x_679_; 
lean_del_object(v___x_667_);
lean_dec(v_fst_664_);
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
lean_object* v_val_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_695_; 
v_val_681_ = lean_ctor_get(v_a_673_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_695_ == 0)
{
v___x_683_ = v_a_673_;
v_isShared_684_ = v_isSharedCheck_695_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_val_681_);
lean_dec(v_a_673_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_695_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = l_BitVec_ofNat(v_val_681_, v_fst_664_);
lean_dec(v_fst_664_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_685_);
lean_ctor_set(v___x_667_, 0, v_val_681_);
v___x_687_ = v___x_667_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_val_681_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_685_);
v___x_687_ = v_reuseFailAlloc_694_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_687_);
v___x_689_ = v___x_683_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_693_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_689_);
v___x_691_ = v___x_675_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_del_object(v___x_667_);
lean_dec(v_fst_664_);
v_a_697_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_672_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_672_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_del_object(v___x_667_);
lean_dec(v_fst_664_);
v_a_705_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_670_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_670_);
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
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_a_715_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_654_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_654_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
v___jp_723_:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Meta_getNatValue_x3f(v_nExpr_724_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec_ref(v_nExpr_724_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_771_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_771_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_771_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_771_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
if (lean_obj_tag(v_a_731_) == 0)
{
lean_object* v___x_735_; lean_object* v___x_737_; 
lean_dec_ref(v_vExpr_725_);
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
lean_object* v_val_739_; lean_object* v___x_740_; 
lean_del_object(v___x_733_);
v_val_739_ = lean_ctor_get(v_a_731_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v_a_731_, 1);
v___x_740_ = l_Lean_Meta_getNatValue_x3f(v_vExpr_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec_ref(v_vExpr_725_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_762_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_762_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_762_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_762_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
if (lean_obj_tag(v_a_741_) == 0)
{
lean_object* v___x_745_; lean_object* v___x_747_; 
lean_dec(v_val_739_);
v___x_745_ = lean_box(0);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_745_);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
else
{
lean_object* v_val_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_761_; 
v_val_749_ = lean_ctor_get(v_a_741_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_a_741_);
if (v_isSharedCheck_761_ == 0)
{
v___x_751_ = v_a_741_;
v_isShared_752_ = v_isSharedCheck_761_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_val_749_);
lean_dec(v_a_741_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_761_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_753_ = l_BitVec_ofNat(v_val_739_, v_val_749_);
lean_dec(v_val_749_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_val_739_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_754_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_760_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_756_);
v___x_758_ = v___x_743_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_val_739_);
v_a_763_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_740_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_740_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v_vExpr_725_);
v_a_772_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_730_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_730_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getBitVecValue_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_642_ = stack[0].m_obj;
lean_object* v_a_643_ = stack[1].m_obj;
lean_object* v_a_644_ = stack[2].m_obj;
lean_object* v_a_645_ = stack[3].m_obj;
lean_object* v_a_646_ = stack[4].m_obj;
lean_object* v_res_804_;
v_res_804_ = l_Lean_Meta_getBitVecValue_x3f(v_e_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
stack->m_obj
 = v_res_804_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f___boxed(lean_object* v_e_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_Meta_getBitVecValue_x3f(v_e_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_811_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__0(void){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_cstr_to_nat("18446744073709551616");
return v___x_812_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__1(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__0, &l_Lean_Meta_getLitValueModulus_x3f___closed__0_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__0);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Meta_getLitValueModulus_x3f___closed__2(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_cstr_to_nat("4294967296");
v___x_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
lean_object* l_Lean_Meta_getLitValueModulus_x3f(lean_object* v_00_u03b1_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03b1_845_, v_a_847_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = l_Lean_Expr_cleanupAnnotations(v_a_867_);
v___x_869_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__6));
v___x_870_ = l_Lean_Expr_isConstOf(v___x_868_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__8));
v___x_872_ = l_Lean_Expr_isConstOf(v___x_868_, v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__10));
v___x_874_ = l_Lean_Expr_isConstOf(v___x_868_, v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__12));
v___x_876_ = l_Lean_Expr_isConstOf(v___x_868_, v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_878_ = l_Lean_Expr_isConstOf(v___x_868_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_880_ = l_Lean_Expr_isConstOf(v___x_868_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_882_ = l_Lean_Expr_isConstOf(v___x_868_, v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_884_ = l_Lean_Expr_isConstOf(v___x_868_, v___x_883_);
if (v___x_884_ == 0)
{
uint8_t v___x_885_; 
v___x_885_ = l_Lean_Expr_isApp(v___x_868_);
if (v___x_885_ == 0)
{
lean_dec_ref(v___x_868_);
goto v___jp_863_;
}
else
{
lean_object* v_arg_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v_arg_886_ = lean_ctor_get(v___x_868_, 1);
lean_inc_ref(v_arg_886_);
v___x_887_ = l_Lean_Expr_appFnCleanup___redArg(v___x_868_);
v___x_888_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__1));
v___x_889_ = l_Lean_Expr_isConstOf(v___x_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_890_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_891_ = l_Lean_Expr_isConstOf(v___x_887_, v___x_890_);
lean_dec_ref(v___x_887_);
if (v___x_891_ == 0)
{
lean_dec_ref(v_arg_886_);
goto v___jp_863_;
}
else
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Meta_getNatValue_x3f(v_arg_886_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec_ref(v_arg_886_);
return v___x_892_;
}
}
else
{
lean_object* v___x_893_; 
lean_dec_ref(v___x_887_);
v___x_893_ = l_Lean_Meta_getNatValue_x3f(v_arg_886_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec_ref(v_arg_886_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_915_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_915_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_915_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_915_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
if (lean_obj_tag(v_a_894_) == 1)
{
lean_object* v_val_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_910_; 
v_val_898_ = lean_ctor_get(v_a_894_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_a_894_);
if (v_isSharedCheck_910_ == 0)
{
v___x_900_ = v_a_894_;
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_val_898_);
lean_dec(v_a_894_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_902_ = lean_unsigned_to_nat(2u);
v___x_903_ = lean_nat_pow(v___x_902_, v_val_898_);
lean_dec(v_val_898_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_903_);
v___x_905_ = v___x_900_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_909_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_907_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_905_);
v___x_907_ = v___x_896_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_object* v___x_911_; lean_object* v___x_913_; 
lean_dec(v_a_894_);
v___x_911_ = lean_box(0);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_911_);
v___x_913_ = v___x_896_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
else
{
return v___x_893_;
}
}
}
}
else
{
lean_dec_ref(v___x_868_);
goto v___jp_860_;
}
}
else
{
lean_dec_ref(v___x_868_);
goto v___jp_857_;
}
}
else
{
lean_dec_ref(v___x_868_);
goto v___jp_854_;
}
}
else
{
lean_dec_ref(v___x_868_);
goto v___jp_851_;
}
}
else
{
lean_dec_ref(v___x_868_);
goto v___jp_860_;
}
}
else
{
lean_dec_ref(v___x_868_);
goto v___jp_857_;
}
}
else
{
lean_dec_ref(v___x_868_);
goto v___jp_854_;
}
}
else
{
lean_dec_ref(v___x_868_);
goto v___jp_851_;
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
v_a_916_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_866_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_866_);
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
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
v___jp_851_:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__1, &l_Lean_Meta_getLitValueModulus_x3f___closed__1_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__1);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
v___jp_854_:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_obj_once(&l_Lean_Meta_getLitValueModulus_x3f___closed__2, &l_Lean_Meta_getLitValueModulus_x3f___closed__2_once, _init_l_Lean_Meta_getLitValueModulus_x3f___closed__2);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
v___jp_857_:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__3));
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
v___jp_860_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__4));
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
v___jp_863_:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_box(0);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getLitValueModulus_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03b1_845_ = stack[0].m_obj;
lean_object* v_a_846_ = stack[1].m_obj;
lean_object* v_a_847_ = stack[2].m_obj;
lean_object* v_a_848_ = stack[3].m_obj;
lean_object* v_a_849_ = stack[4].m_obj;
lean_object* v_res_924_;
v_res_924_ = l_Lean_Meta_getLitValueModulus_x3f(v_00_u03b1_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLitValueModulus_x3f___boxed(lean_object* v_00_u03b1_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Meta_getLitValueModulus_x3f(v_00_u03b1_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
return v_res_931_;
}
}
lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object* v_e_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_939_ = l_Lean_Meta_getOfNatValue_x3f(v_e_932_, v___x_938_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_962_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_962_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_962_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_962_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
if (lean_obj_tag(v_a_940_) == 0)
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = lean_box(0);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
else
{
lean_object* v_val_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_961_; 
v_val_948_ = lean_ctor_get(v_a_940_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v_a_940_);
if (v_isSharedCheck_961_ == 0)
{
v___x_950_ = v_a_940_;
v_isShared_951_ = v_isSharedCheck_961_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_val_948_);
lean_dec(v_a_940_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_961_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_fst_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
v_fst_952_ = lean_ctor_get(v_val_948_, 0);
lean_inc(v_fst_952_);
lean_dec(v_val_948_);
v___x_953_ = lean_uint8_of_nat(v_fst_952_);
lean_dec(v_fst_952_);
v___x_954_ = lean_box(v___x_953_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_954_);
v___x_956_ = v___x_950_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_960_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_958_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_956_);
v___x_958_ = v___x_942_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_963_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_939_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_939_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getUInt8Value_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_932_ = stack[0].m_obj;
lean_object* v_a_933_ = stack[1].m_obj;
lean_object* v_a_934_ = stack[2].m_obj;
lean_object* v_a_935_ = stack[3].m_obj;
lean_object* v_a_936_ = stack[4].m_obj;
lean_object* v_res_971_;
v_res_971_ = l_Lean_Meta_getUInt8Value_x3f(v_e_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
stack->m_obj
 = v_res_971_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f___boxed(lean_object* v_e_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Meta_getUInt8Value_x3f(v_e_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_978_;
}
}
lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object* v_e_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_986_ = l_Lean_Meta_getOfNatValue_x3f(v_e_979_, v___x_985_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1009_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_1009_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1009_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
if (lean_obj_tag(v_a_987_) == 0)
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_box(0);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
else
{
lean_object* v_val_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1008_; 
v_val_995_ = lean_ctor_get(v_a_987_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_a_987_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_997_ = v_a_987_;
v_isShared_998_ = v_isSharedCheck_1008_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_val_995_);
lean_dec(v_a_987_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1008_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_fst_999_; uint16_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v_fst_999_ = lean_ctor_get(v_val_995_, 0);
lean_inc(v_fst_999_);
lean_dec(v_val_995_);
v___x_1000_ = lean_uint16_of_nat(v_fst_999_);
lean_dec(v_fst_999_);
v___x_1001_ = lean_box(v___x_1000_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1001_);
v___x_1003_ = v___x_997_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_1003_);
v___x_1005_ = v___x_989_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_986_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_986_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getUInt16Value_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_979_ = stack[0].m_obj;
lean_object* v_a_980_ = stack[1].m_obj;
lean_object* v_a_981_ = stack[2].m_obj;
lean_object* v_a_982_ = stack[3].m_obj;
lean_object* v_a_983_ = stack[4].m_obj;
lean_object* v_res_1018_;
v_res_1018_ = l_Lean_Meta_getUInt16Value_x3f(v_e_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
stack->m_obj
 = v_res_1018_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f___boxed(lean_object* v_e_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Meta_getUInt16Value_x3f(v_e_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
return v_res_1025_;
}
}
lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object* v_e_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_1033_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1026_, v___x_1032_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1056_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1056_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1056_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
if (lean_obj_tag(v_a_1034_) == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1038_ = lean_box(0);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1038_);
v___x_1040_ = v___x_1036_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
else
{
lean_object* v_val_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1055_; 
v_val_1042_ = lean_ctor_get(v_a_1034_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_a_1034_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1044_ = v_a_1034_;
v_isShared_1045_ = v_isSharedCheck_1055_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_val_1042_);
lean_dec(v_a_1034_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1055_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_fst_1046_; uint32_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v_fst_1046_ = lean_ctor_get(v_val_1042_, 0);
lean_inc(v_fst_1046_);
lean_dec(v_val_1042_);
v___x_1047_ = lean_uint32_of_nat(v_fst_1046_);
lean_dec(v_fst_1046_);
v___x_1048_ = lean_box_uint32(v___x_1047_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1048_);
v___x_1050_ = v___x_1044_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1050_);
v___x_1052_ = v___x_1036_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_a_1057_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1033_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1033_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getUInt32Value_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1026_ = stack[0].m_obj;
lean_object* v_a_1027_ = stack[1].m_obj;
lean_object* v_a_1028_ = stack[2].m_obj;
lean_object* v_a_1029_ = stack[3].m_obj;
lean_object* v_a_1030_ = stack[4].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l_Lean_Meta_getUInt32Value_x3f(v_e_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f___boxed(lean_object* v_e_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Meta_getUInt32Value_x3f(v_e_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
return v_res_1072_;
}
}
lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object* v_e_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_1080_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1073_, v___x_1079_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1103_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1103_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1103_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
if (lean_obj_tag(v_a_1081_) == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_box(0);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1087_ = v___x_1083_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
else
{
lean_object* v_val_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1102_; 
v_val_1089_ = lean_ctor_get(v_a_1081_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_a_1081_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1091_ = v_a_1081_;
v_isShared_1092_ = v_isSharedCheck_1102_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_val_1089_);
lean_dec(v_a_1081_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1102_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_fst_1093_; uint64_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v_fst_1093_ = lean_ctor_get(v_val_1089_, 0);
lean_inc(v_fst_1093_);
lean_dec(v_val_1089_);
v___x_1094_ = lean_uint64_of_nat(v_fst_1093_);
lean_dec(v_fst_1093_);
v___x_1095_ = lean_box_uint64(v___x_1094_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1095_);
v___x_1097_ = v___x_1091_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1097_);
v___x_1099_ = v___x_1083_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
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
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1080_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1080_);
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
}
LEAN_EXPORT void l_Lean_Meta_getUInt64Value_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1073_ = stack[0].m_obj;
lean_object* v_a_1074_ = stack[1].m_obj;
lean_object* v_a_1075_ = stack[2].m_obj;
lean_object* v_a_1076_ = stack[3].m_obj;
lean_object* v_a_1077_ = stack[4].m_obj;
lean_object* v_res_1112_;
v_res_1112_ = l_Lean_Meta_getUInt64Value_x3f(v_e_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
stack->m_obj
 = v_res_1112_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f___boxed(lean_object* v_e_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Meta_getUInt64Value_x3f(v_e_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(lean_object* v_e_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_Expr_consumeMData(v_e_1123_);
if (lean_obj_tag(v___x_1124_) == 4)
{
lean_object* v_declName_1125_; 
v_declName_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_declName_1125_);
lean_dec_ref_known(v___x_1124_, 2);
if (lean_obj_tag(v_declName_1125_) == 1)
{
lean_object* v_pre_1126_; 
v_pre_1126_ = lean_ctor_get(v_declName_1125_, 0);
lean_inc(v_pre_1126_);
if (lean_obj_tag(v_pre_1126_) == 1)
{
lean_object* v_pre_1127_; 
v_pre_1127_ = lean_ctor_get(v_pre_1126_, 0);
if (lean_obj_tag(v_pre_1127_) == 0)
{
lean_object* v_str_1128_; lean_object* v_str_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v_str_1128_ = lean_ctor_get(v_declName_1125_, 1);
lean_inc_ref(v_str_1128_);
lean_dec_ref_known(v_declName_1125_, 2);
v_str_1129_ = lean_ctor_get(v_pre_1126_, 1);
lean_inc_ref(v_str_1129_);
lean_dec_ref_known(v_pre_1126_, 2);
v___x_1130_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0));
v___x_1131_ = lean_string_dec_eq(v_str_1129_, v___x_1130_);
lean_dec_ref(v_str_1129_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref(v_str_1128_);
v___x_1132_ = lean_box(0);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1));
v___x_1134_ = lean_string_dec_eq(v_str_1128_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2));
v___x_1136_ = lean_string_dec_eq(v_str_1128_, v___x_1135_);
lean_dec_ref(v_str_1128_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_box(0);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_box(v___x_1134_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec_ref(v_str_1128_);
v___x_1140_ = lean_box(v___x_1134_);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
else
{
lean_object* v___x_1142_; 
lean_dec_ref_known(v_pre_1126_, 2);
lean_dec_ref_known(v_declName_1125_, 2);
v___x_1142_ = lean_box(0);
return v___x_1142_;
}
}
else
{
lean_object* v___x_1143_; 
lean_dec_ref_known(v_declName_1125_, 2);
lean_dec(v_pre_1126_);
v___x_1143_ = lean_box(0);
return v___x_1143_;
}
}
else
{
lean_object* v___x_1144_; 
lean_dec(v_declName_1125_);
v___x_1144_ = lean_box(0);
return v___x_1144_;
}
}
else
{
lean_object* v___x_1145_; 
lean_dec_ref(v___x_1124_);
v___x_1145_ = lean_box(0);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___boxed(lean_object* v_e_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_e_1146_);
lean_dec_ref(v_e_1146_);
return v_res_1147_;
}
}
lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(lean_object* v_e_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___x_1200_; 
lean_inc_ref(v_e_1156_);
v___x_1200_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1156_, v_a_1158_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1200_, 1);
v___x_1202_ = l_Lean_Expr_cleanupAnnotations(v_a_1201_);
v___x_1203_ = l_Lean_Expr_isApp(v___x_1202_);
if (v___x_1203_ == 0)
{
lean_dec_ref(v___x_1202_);
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
v___y_1166_ = v_a_1160_;
goto v___jp_1162_;
}
else
{
lean_object* v_arg_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v_arg_1204_ = lean_ctor_get(v___x_1202_, 1);
lean_inc_ref(v_arg_1204_);
v___x_1205_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1202_);
v___x_1206_ = l_Lean_Expr_isApp(v___x_1205_);
if (v___x_1206_ == 0)
{
lean_dec_ref(v___x_1205_);
lean_dec_ref(v_arg_1204_);
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
v___y_1166_ = v_a_1160_;
goto v___jp_1162_;
}
else
{
lean_object* v_arg_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v_arg_1207_ = lean_ctor_get(v___x_1205_, 1);
lean_inc_ref(v_arg_1207_);
v___x_1208_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1205_);
v___x_1209_ = l_Lean_Expr_isApp(v___x_1208_);
if (v___x_1209_ == 0)
{
lean_dec_ref(v___x_1208_);
lean_dec_ref(v_arg_1207_);
lean_dec_ref(v_arg_1204_);
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
v___y_1166_ = v_a_1160_;
goto v___jp_1162_;
}
else
{
lean_object* v_arg_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_arg_1210_ = lean_ctor_get(v___x_1208_, 1);
lean_inc_ref(v_arg_1210_);
v___x_1211_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1208_);
v___x_1212_ = l_Lean_Expr_isApp(v___x_1211_);
if (v___x_1212_ == 0)
{
lean_dec_ref(v___x_1211_);
lean_dec_ref(v_arg_1210_);
lean_dec_ref(v_arg_1207_);
lean_dec_ref(v_arg_1204_);
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
v___y_1166_ = v_a_1160_;
goto v___jp_1162_;
}
else
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1211_);
v___x_1214_ = l_Lean_Expr_isApp(v___x_1213_);
if (v___x_1214_ == 0)
{
lean_dec_ref(v___x_1213_);
lean_dec_ref(v_arg_1210_);
lean_dec_ref(v_arg_1207_);
lean_dec_ref(v_arg_1204_);
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
v___y_1166_ = v_a_1160_;
goto v___jp_1162_;
}
else
{
lean_object* v_arg_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v_arg_1215_ = lean_ctor_get(v___x_1213_, 1);
lean_inc_ref(v_arg_1215_);
v___x_1216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1213_);
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__4));
v___x_1218_ = l_Lean_Expr_isConstOf(v___x_1216_, v___x_1217_);
lean_dec_ref(v___x_1216_);
if (v___x_1218_ == 0)
{
lean_dec_ref(v_arg_1215_);
lean_dec_ref(v_arg_1210_);
lean_dec_ref(v_arg_1207_);
lean_dec_ref(v_arg_1204_);
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
v___y_1166_ = v_a_1160_;
goto v___jp_1162_;
}
else
{
lean_object* v___x_1219_; 
lean_dec_ref(v_e_1156_);
v___x_1219_ = l_Lean_Meta_whnfD(v_arg_1215_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1287_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1287_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1287_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1225_ = l_Lean_Expr_isConstOf(v_a_1220_, v___x_1224_);
lean_dec(v_a_1220_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
lean_dec_ref(v_arg_1210_);
lean_dec_ref(v_arg_1207_);
lean_dec_ref(v_arg_1204_);
v___x_1226_ = lean_box(0);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1226_);
v___x_1228_ = v___x_1222_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
else
{
lean_object* v___x_1230_; 
v___x_1230_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_1207_);
lean_dec_ref(v_arg_1207_);
if (lean_obj_tag(v___x_1230_) == 1)
{
lean_object* v_val_1231_; lean_object* v___x_1232_; 
lean_del_object(v___x_1222_);
v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = l_Lean_Meta_getNatValue_x3f(v_arg_1210_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec_ref(v_arg_1210_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1274_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1274_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1274_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
if (lean_obj_tag(v_a_1233_) == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
lean_dec(v_val_1231_);
lean_dec_ref(v_arg_1204_);
v___x_1237_ = lean_box(0);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1237_);
v___x_1239_ = v___x_1235_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
else
{
lean_object* v_val_1241_; lean_object* v___x_1242_; 
lean_del_object(v___x_1235_);
v_val_1241_ = lean_ctor_get(v_a_1233_, 0);
lean_inc(v_val_1241_);
lean_dec_ref_known(v_a_1233_, 1);
v___x_1242_ = l_Lean_Meta_getNatValue_x3f(v_arg_1204_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec_ref(v_arg_1204_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1265_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1265_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1265_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
if (lean_obj_tag(v_a_1243_) == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
lean_dec(v_val_1241_);
lean_dec(v_val_1231_);
v___x_1247_ = lean_box(0);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
else
{
lean_object* v_val_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1264_; 
v_val_1251_ = lean_ctor_get(v_a_1243_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_a_1243_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1253_ = v_a_1243_;
v_isShared_1254_ = v_isSharedCheck_1264_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_val_1251_);
lean_dec(v_a_1243_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1264_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
uint8_t v___x_1255_; double v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1255_ = lean_unbox(v_val_1231_);
lean_dec(v_val_1231_);
v___x_1256_ = l_Float_ofScientific(v_val_1241_, v___x_1255_, v_val_1251_);
v___x_1257_ = lean_box_float(v___x_1256_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1257_);
v___x_1259_ = v___x_1253_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1261_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1259_);
v___x_1261_ = v___x_1245_;
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
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_val_1241_);
lean_dec(v_val_1231_);
v_a_1266_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1242_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1242_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
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
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_val_1231_);
lean_dec_ref(v_arg_1204_);
v_a_1275_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1232_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1232_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
lean_dec(v___x_1230_);
lean_dec_ref(v_arg_1210_);
lean_dec_ref(v_arg_1204_);
v___x_1283_ = lean_box(0);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1283_);
v___x_1285_ = v___x_1222_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_arg_1210_);
lean_dec_ref(v_arg_1207_);
lean_dec_ref(v_arg_1204_);
v_a_1288_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1219_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1219_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
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
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_e_1156_);
v_a_1296_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1200_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1200_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
v___jp_1162_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1168_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1156_, v___x_1167_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1191_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1191_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1191_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
if (lean_obj_tag(v_a_1169_) == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = lean_box(0);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1173_);
v___x_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
else
{
lean_object* v_val_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1190_; 
v_val_1177_ = lean_ctor_get(v_a_1169_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_a_1169_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1179_ = v_a_1169_;
v_isShared_1180_ = v_isSharedCheck_1190_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_val_1177_);
lean_dec(v_a_1169_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1190_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_fst_1181_; double v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v_fst_1181_ = lean_ctor_get(v_val_1177_, 0);
lean_inc(v_fst_1181_);
lean_dec(v_val_1177_);
v___x_1182_ = lean_float_of_nat(v_fst_1181_);
v___x_1183_ = lean_box_float(v___x_1182_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1183_);
v___x_1185_ = v___x_1179_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1185_);
v___x_1187_ = v___x_1171_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_a_1192_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1168_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1168_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1156_ = stack[0].m_obj;
lean_object* v_a_1157_ = stack[1].m_obj;
lean_object* v_a_1158_ = stack[2].m_obj;
lean_object* v_a_1159_ = stack[3].m_obj;
lean_object* v_a_1160_ = stack[4].m_obj;
lean_object* v_res_1304_;
v_res_1304_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
stack->m_obj
 = v_res_1304_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___boxed(lean_object* v_e_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
return v_res_1311_;
}
}
lean_object* l_Lean_Meta_getFloatValue_x3f(lean_object* v_e_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___x_1321_; 
lean_inc_ref(v_e_1312_);
v___x_1321_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
if (lean_obj_tag(v_a_1322_) == 1)
{
lean_dec_ref(v_e_1312_);
return v___x_1321_;
}
else
{
lean_object* v___x_1323_; 
lean_dec_ref_known(v___x_1321_, 1);
v___x_1323_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1312_, v_a_1314_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v___x_1325_ = l_Lean_Expr_cleanupAnnotations(v_a_1324_);
v___x_1326_ = l_Lean_Expr_isApp(v___x_1325_);
if (v___x_1326_ == 0)
{
lean_dec_ref(v___x_1325_);
goto v___jp_1318_;
}
else
{
lean_object* v_arg_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_arg_1327_ = lean_ctor_get(v___x_1325_, 1);
lean_inc_ref(v_arg_1327_);
v___x_1328_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1325_);
v___x_1329_ = l_Lean_Expr_isApp(v___x_1328_);
if (v___x_1329_ == 0)
{
lean_dec_ref(v___x_1328_);
lean_dec_ref(v_arg_1327_);
goto v___jp_1318_;
}
else
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1328_);
v___x_1331_ = l_Lean_Expr_isApp(v___x_1330_);
if (v___x_1331_ == 0)
{
lean_dec_ref(v___x_1330_);
lean_dec_ref(v_arg_1327_);
goto v___jp_1318_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1330_);
v___x_1333_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1334_ = l_Lean_Expr_isConstOf(v___x_1332_, v___x_1333_);
lean_dec_ref(v___x_1332_);
if (v___x_1334_ == 0)
{
lean_dec_ref(v_arg_1327_);
goto v___jp_1318_;
}
else
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_arg_1327_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1358_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1358_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1358_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
if (lean_obj_tag(v_a_1336_) == 1)
{
lean_object* v_val_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1353_; 
v_val_1340_ = lean_ctor_get(v_a_1336_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_a_1336_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1342_ = v_a_1336_;
v_isShared_1343_ = v_isSharedCheck_1353_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_val_1340_);
lean_dec(v_a_1336_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1353_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
double v___x_1344_; double v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1344_ = lean_unbox_float(v_val_1340_);
lean_dec(v_val_1340_);
v___x_1345_ = lean_float_negate(v___x_1344_);
v___x_1346_ = lean_box_float(v___x_1345_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1346_);
v___x_1348_ = v___x_1342_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1350_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1348_);
v___x_1350_ = v___x_1338_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
lean_dec(v_a_1336_);
v___x_1354_ = lean_box(0);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1354_);
v___x_1356_ = v___x_1338_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
return v___x_1335_;
}
}
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_a_1359_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1323_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1323_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1312_);
return v___x_1321_;
}
v___jp_1318_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getFloatValue_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1312_ = stack[0].m_obj;
lean_object* v_a_1313_ = stack[1].m_obj;
lean_object* v_a_1314_ = stack[2].m_obj;
lean_object* v_a_1315_ = stack[3].m_obj;
lean_object* v_a_1316_ = stack[4].m_obj;
lean_object* v_res_1367_;
v_res_1367_ = l_Lean_Meta_getFloatValue_x3f(v_e_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
stack->m_obj
 = v_res_1367_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f___boxed(lean_object* v_e_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Meta_getFloatValue_x3f(v_e_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
return v_res_1374_;
}
}
lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(lean_object* v_e_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___x_1422_; 
lean_inc_ref(v_e_1378_);
v___x_1422_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1378_, v_a_1380_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = l_Lean_Expr_cleanupAnnotations(v_a_1423_);
v___x_1425_ = l_Lean_Expr_isApp(v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec_ref(v___x_1424_);
v___y_1385_ = v_a_1379_;
v___y_1386_ = v_a_1380_;
v___y_1387_ = v_a_1381_;
v___y_1388_ = v_a_1382_;
goto v___jp_1384_;
}
else
{
lean_object* v_arg_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_arg_1426_ = lean_ctor_get(v___x_1424_, 1);
lean_inc_ref(v_arg_1426_);
v___x_1427_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1424_);
v___x_1428_ = l_Lean_Expr_isApp(v___x_1427_);
if (v___x_1428_ == 0)
{
lean_dec_ref(v___x_1427_);
lean_dec_ref(v_arg_1426_);
v___y_1385_ = v_a_1379_;
v___y_1386_ = v_a_1380_;
v___y_1387_ = v_a_1381_;
v___y_1388_ = v_a_1382_;
goto v___jp_1384_;
}
else
{
lean_object* v_arg_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_arg_1429_ = lean_ctor_get(v___x_1427_, 1);
lean_inc_ref(v_arg_1429_);
v___x_1430_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1427_);
v___x_1431_ = l_Lean_Expr_isApp(v___x_1430_);
if (v___x_1431_ == 0)
{
lean_dec_ref(v___x_1430_);
lean_dec_ref(v_arg_1429_);
lean_dec_ref(v_arg_1426_);
v___y_1385_ = v_a_1379_;
v___y_1386_ = v_a_1380_;
v___y_1387_ = v_a_1381_;
v___y_1388_ = v_a_1382_;
goto v___jp_1384_;
}
else
{
lean_object* v_arg_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_arg_1432_ = lean_ctor_get(v___x_1430_, 1);
lean_inc_ref(v_arg_1432_);
v___x_1433_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1430_);
v___x_1434_ = l_Lean_Expr_isApp(v___x_1433_);
if (v___x_1434_ == 0)
{
lean_dec_ref(v___x_1433_);
lean_dec_ref(v_arg_1432_);
lean_dec_ref(v_arg_1429_);
lean_dec_ref(v_arg_1426_);
v___y_1385_ = v_a_1379_;
v___y_1386_ = v_a_1380_;
v___y_1387_ = v_a_1381_;
v___y_1388_ = v_a_1382_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1433_);
v___x_1436_ = l_Lean_Expr_isApp(v___x_1435_);
if (v___x_1436_ == 0)
{
lean_dec_ref(v___x_1435_);
lean_dec_ref(v_arg_1432_);
lean_dec_ref(v_arg_1429_);
lean_dec_ref(v_arg_1426_);
v___y_1385_ = v_a_1379_;
v___y_1386_ = v_a_1380_;
v___y_1387_ = v_a_1381_;
v___y_1388_ = v_a_1382_;
goto v___jp_1384_;
}
else
{
lean_object* v_arg_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v_arg_1437_ = lean_ctor_get(v___x_1435_, 1);
lean_inc_ref(v_arg_1437_);
v___x_1438_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1435_);
v___x_1439_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__4));
v___x_1440_ = l_Lean_Expr_isConstOf(v___x_1438_, v___x_1439_);
lean_dec_ref(v___x_1438_);
if (v___x_1440_ == 0)
{
lean_dec_ref(v_arg_1437_);
lean_dec_ref(v_arg_1432_);
lean_dec_ref(v_arg_1429_);
lean_dec_ref(v_arg_1426_);
v___y_1385_ = v_a_1379_;
v___y_1386_ = v_a_1380_;
v___y_1387_ = v_a_1381_;
v___y_1388_ = v_a_1382_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1441_; 
lean_dec_ref(v_e_1378_);
v___x_1441_ = l_Lean_Meta_whnfD(v_arg_1437_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1509_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1509_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1509_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_1447_ = l_Lean_Expr_isConstOf(v_a_1442_, v___x_1446_);
lean_dec(v_a_1442_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_dec_ref(v_arg_1432_);
lean_dec_ref(v_arg_1429_);
lean_dec_ref(v_arg_1426_);
v___x_1448_ = lean_box(0);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1448_);
v___x_1450_ = v___x_1444_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
else
{
lean_object* v___x_1452_; 
v___x_1452_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_1429_);
lean_dec_ref(v_arg_1429_);
if (lean_obj_tag(v___x_1452_) == 1)
{
lean_object* v_val_1453_; lean_object* v___x_1454_; 
lean_del_object(v___x_1444_);
v_val_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_val_1453_);
lean_dec_ref_known(v___x_1452_, 1);
v___x_1454_ = l_Lean_Meta_getNatValue_x3f(v_arg_1432_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec_ref(v_arg_1432_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1496_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1496_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1496_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
if (lean_obj_tag(v_a_1455_) == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
lean_dec(v_val_1453_);
lean_dec_ref(v_arg_1426_);
v___x_1459_ = lean_box(0);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1459_);
v___x_1461_ = v___x_1457_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
else
{
lean_object* v_val_1463_; lean_object* v___x_1464_; 
lean_del_object(v___x_1457_);
v_val_1463_ = lean_ctor_get(v_a_1455_, 0);
lean_inc(v_val_1463_);
lean_dec_ref_known(v_a_1455_, 1);
v___x_1464_ = l_Lean_Meta_getNatValue_x3f(v_arg_1426_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec_ref(v_arg_1426_);
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
lean_dec(v_val_1463_);
lean_dec(v_val_1453_);
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
uint8_t v___x_1477_; float v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1477_ = lean_unbox(v_val_1453_);
lean_dec(v_val_1453_);
v___x_1478_ = l_Float32_ofScientific(v_val_1463_, v___x_1477_, v_val_1473_);
v___x_1479_ = lean_box_float32(v___x_1478_);
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
lean_dec(v_val_1463_);
lean_dec(v_val_1453_);
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
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec(v_val_1453_);
lean_dec_ref(v_arg_1426_);
v_a_1497_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1454_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1454_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
lean_dec(v___x_1452_);
lean_dec_ref(v_arg_1432_);
lean_dec_ref(v_arg_1426_);
v___x_1505_ = lean_box(0);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1505_);
v___x_1507_ = v___x_1444_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_arg_1432_);
lean_dec_ref(v_arg_1429_);
lean_dec_ref(v_arg_1426_);
v_a_1510_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1441_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1441_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
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
}
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec_ref(v_e_1378_);
v_a_1518_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1422_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1422_);
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
v___jp_1384_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_1390_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1378_, v___x_1389_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1413_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1413_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1413_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
if (lean_obj_tag(v_a_1391_) == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1395_ = lean_box(0);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1395_);
v___x_1397_ = v___x_1393_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
else
{
lean_object* v_val_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1412_; 
v_val_1399_ = lean_ctor_get(v_a_1391_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_a_1391_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1401_ = v_a_1391_;
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_val_1399_);
lean_dec(v_a_1391_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_fst_1403_; float v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v_fst_1403_ = lean_ctor_get(v_val_1399_, 0);
lean_inc(v_fst_1403_);
lean_dec(v_val_1399_);
v___x_1404_ = lean_float32_of_nat(v_fst_1403_);
v___x_1405_ = lean_box_float32(v___x_1404_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1405_);
v___x_1407_ = v___x_1401_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1409_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1407_);
v___x_1409_ = v___x_1393_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_a_1414_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1390_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1390_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1378_ = stack[0].m_obj;
lean_object* v_a_1379_ = stack[1].m_obj;
lean_object* v_a_1380_ = stack[2].m_obj;
lean_object* v_a_1381_ = stack[3].m_obj;
lean_object* v_a_1382_ = stack[4].m_obj;
lean_object* v_res_1526_;
v_res_1526_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
stack->m_obj
 = v_res_1526_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___boxed(lean_object* v_e_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
return v_res_1533_;
}
}
lean_object* l_Lean_Meta_getFloat32Value_x3f(lean_object* v_e_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v___x_1543_; 
lean_inc_ref(v_e_1534_);
v___x_1543_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
if (lean_obj_tag(v_a_1544_) == 1)
{
lean_dec_ref(v_e_1534_);
return v___x_1543_;
}
else
{
lean_object* v___x_1545_; 
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1534_, v_a_1536_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = l_Lean_Expr_cleanupAnnotations(v_a_1546_);
v___x_1548_ = l_Lean_Expr_isApp(v___x_1547_);
if (v___x_1548_ == 0)
{
lean_dec_ref(v___x_1547_);
goto v___jp_1540_;
}
else
{
lean_object* v_arg_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_arg_1549_ = lean_ctor_get(v___x_1547_, 1);
lean_inc_ref(v_arg_1549_);
v___x_1550_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1547_);
v___x_1551_ = l_Lean_Expr_isApp(v___x_1550_);
if (v___x_1551_ == 0)
{
lean_dec_ref(v___x_1550_);
lean_dec_ref(v_arg_1549_);
goto v___jp_1540_;
}
else
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1550_);
v___x_1553_ = l_Lean_Expr_isApp(v___x_1552_);
if (v___x_1553_ == 0)
{
lean_dec_ref(v___x_1552_);
lean_dec_ref(v_arg_1549_);
goto v___jp_1540_;
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1552_);
v___x_1555_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1556_ = l_Lean_Expr_isConstOf(v___x_1554_, v___x_1555_);
lean_dec_ref(v___x_1554_);
if (v___x_1556_ == 0)
{
lean_dec_ref(v_arg_1549_);
goto v___jp_1540_;
}
else
{
lean_object* v___x_1557_; 
v___x_1557_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_arg_1549_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
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
if (lean_obj_tag(v_a_1558_) == 1)
{
lean_object* v_val_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1575_; 
v_val_1562_ = lean_ctor_get(v_a_1558_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_a_1558_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1564_ = v_a_1558_;
v_isShared_1565_ = v_isSharedCheck_1575_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_val_1562_);
lean_dec(v_a_1558_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1575_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
float v___x_1566_; float v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1566_ = lean_unbox_float32(v_val_1562_);
lean_dec(v_val_1562_);
v___x_1567_ = lean_float32_negate(v___x_1566_);
v___x_1568_ = lean_box_float32(v___x_1567_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1568_);
v___x_1570_ = v___x_1564_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1570_);
v___x_1572_ = v___x_1560_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
lean_dec(v_a_1558_);
v___x_1576_ = lean_box(0);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1576_);
v___x_1578_ = v___x_1560_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
return v___x_1557_;
}
}
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
v_a_1581_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1545_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1545_);
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
else
{
lean_dec_ref(v_e_1534_);
return v___x_1543_;
}
v___jp_1540_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getFloat32Value_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1534_ = stack[0].m_obj;
lean_object* v_a_1535_ = stack[1].m_obj;
lean_object* v_a_1536_ = stack[2].m_obj;
lean_object* v_a_1537_ = stack[3].m_obj;
lean_object* v_a_1538_ = stack[4].m_obj;
lean_object* v_res_1589_;
v_res_1589_ = l_Lean_Meta_getFloat32Value_x3f(v_e_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
stack->m_obj
 = v_res_1589_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f___boxed(lean_object* v_e_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Meta_getFloat32Value_x3f(v_e_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1596_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(lean_object* v_e_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v___x_1600_; 
v___x_1600_ = l_Lean_Expr_hasMVar(v_e_1597_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_e_1597_);
return v___x_1601_;
}
else
{
lean_object* v___x_1602_; lean_object* v_mctx_1603_; lean_object* v___x_1604_; lean_object* v_fst_1605_; lean_object* v_snd_1606_; lean_object* v___x_1607_; lean_object* v_cache_1608_; lean_object* v_zetaDeltaFVarIds_1609_; lean_object* v_postponed_1610_; lean_object* v_diag_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1620_; 
v___x_1602_ = lean_st_ref_get(v___y_1598_);
v_mctx_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc_ref(v_mctx_1603_);
lean_dec(v___x_1602_);
v___x_1604_ = l_Lean_instantiateMVarsCore(v_mctx_1603_, v_e_1597_);
v_fst_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_fst_1605_);
v_snd_1606_ = lean_ctor_get(v___x_1604_, 1);
lean_inc(v_snd_1606_);
lean_dec_ref(v___x_1604_);
v___x_1607_ = lean_st_ref_take(v___y_1598_);
v_cache_1608_ = lean_ctor_get(v___x_1607_, 1);
v_zetaDeltaFVarIds_1609_ = lean_ctor_get(v___x_1607_, 2);
v_postponed_1610_ = lean_ctor_get(v___x_1607_, 3);
v_diag_1611_ = lean_ctor_get(v___x_1607_, 4);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; 
v_unused_1621_ = lean_ctor_get(v___x_1607_, 0);
lean_dec(v_unused_1621_);
v___x_1613_ = v___x_1607_;
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_diag_1611_);
lean_inc(v_postponed_1610_);
lean_inc(v_zetaDeltaFVarIds_1609_);
lean_inc(v_cache_1608_);
lean_dec(v___x_1607_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v_snd_1606_);
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_snd_1606_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_cache_1608_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_zetaDeltaFVarIds_1609_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_postponed_1610_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_diag_1611_);
v___x_1616_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_st_ref_put(v___y_1598_, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v_fst_1605_);
return v___x_1618_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1597_ = stack[0].m_obj;
lean_object* v___y_1598_ = stack[1].m_obj;
lean_object* v_res_1622_;
v_res_1622_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1597_, v___y_1598_);
stack->m_obj
 = v_res_1622_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg___boxed(lean_object* v_e_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1623_, v___y_1624_);
lean_dec(v___y_1624_);
return v_res_1626_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(lean_object* v_e_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1627_, v___y_1629_);
return v___x_1633_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1627_ = stack[0].m_obj;
lean_object* v___y_1628_ = stack[1].m_obj;
lean_object* v___y_1629_ = stack[2].m_obj;
lean_object* v___y_1630_ = stack[3].m_obj;
lean_object* v___y_1631_ = stack[4].m_obj;
lean_object* v_res_1634_;
v_res_1634_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(v_e_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
stack->m_obj
 = v_res_1634_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___boxed(lean_object* v_e_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(v_e_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
return v_res_1641_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__0(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_unsigned_to_nat(0u);
v___x_1643_ = lean_nat_to_int(v___x_1642_);
return v___x_1643_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__1(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = l_Lean_Level_ofNat(v___x_1644_);
return v___x_1645_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__2(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__1, &l_Lean_Meta_normLitValue___closed__1_once, _init_l_Lean_Meta_normLitValue___closed__1);
v___x_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v___x_1646_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__3(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_1650_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1651_ = l_Lean_Expr_const___override(v___x_1650_, v___x_1649_);
return v___x_1651_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__4(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_1654_ = l_Lean_Expr_const___override(v___x_1653_, v___x_1652_);
return v___x_1654_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__7(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_box(0);
v___x_1660_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__6));
v___x_1661_ = l_Lean_Expr_const___override(v___x_1660_, v___x_1659_);
return v___x_1661_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__8(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_1663_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_1664_ = l_Lean_Expr_const___override(v___x_1663_, v___x_1662_);
return v___x_1664_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__9(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = lean_box(0);
v___x_1666_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_1667_ = l_Lean_mkConst(v___x_1666_, v___x_1665_);
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__12(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_box(0);
v___x_1673_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__11));
v___x_1674_ = l_Lean_Expr_const___override(v___x_1673_, v___x_1672_);
return v___x_1674_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__15(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_box(0);
v___x_1680_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__14));
v___x_1681_ = l_Lean_Expr_const___override(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__16(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_box(0);
v___x_1683_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_1684_ = l_Lean_Expr_const___override(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__17(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_box(0);
v___x_1686_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_1687_ = l_Lean_mkConst(v___x_1686_, v___x_1685_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__18(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_box(0);
v___x_1689_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__20));
v___x_1690_ = l_Lean_mkConst(v___x_1689_, v___x_1688_);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__20(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_box(0);
v___x_1695_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__19));
v___x_1696_ = l_Lean_Expr_const___override(v___x_1695_, v___x_1694_);
return v___x_1696_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__21(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = lean_box(0);
v___x_1698_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__18));
v___x_1699_ = l_Lean_mkConst(v___x_1698_, v___x_1697_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__23(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = lean_box(0);
v___x_1704_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__22));
v___x_1705_ = l_Lean_Expr_const___override(v___x_1704_, v___x_1703_);
return v___x_1705_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__24(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_box(0);
v___x_1707_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__16));
v___x_1708_ = l_Lean_mkConst(v___x_1707_, v___x_1706_);
return v___x_1708_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__26(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_box(0);
v___x_1713_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__25));
v___x_1714_ = l_Lean_Expr_const___override(v___x_1713_, v___x_1712_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__27(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = lean_box(0);
v___x_1716_ = ((lean_object*)(l_Lean_Meta_getLitValueModulus_x3f___closed__14));
v___x_1717_ = l_Lean_mkConst(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__29(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_box(0);
v___x_1722_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__28));
v___x_1723_ = l_Lean_Expr_const___override(v___x_1722_, v___x_1721_);
return v___x_1723_;
}
}
lean_object* l_Lean_Meta_normLitValue(lean_object* v_e_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v___x_1730_; lean_object* v_a_1731_; lean_object* v___x_1732_; 
v___x_1730_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1724_, v_a_1726_);
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = l_Lean_Meta_getNatValue_x3f(v_a_1731_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1967_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1967_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1967_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
if (lean_obj_tag(v_a_1733_) == 1)
{
lean_object* v_val_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
lean_dec(v_a_1731_);
v_val_1737_ = lean_ctor_get(v_a_1733_, 0);
lean_inc(v_val_1737_);
lean_dec_ref_known(v_a_1733_, 1);
v___x_1738_ = l_Lean_mkNatLit(v_val_1737_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1738_);
v___x_1740_ = v___x_1735_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
else
{
lean_object* v___x_1742_; 
lean_del_object(v___x_1735_);
lean_dec(v_a_1733_);
lean_inc(v_a_1731_);
v___x_1742_ = l_Lean_Meta_getIntValue_x3f(v_a_1731_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1958_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1958_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1958_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
if (lean_obj_tag(v_a_1743_) == 1)
{
lean_object* v_val_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
lean_dec(v_a_1731_);
v_val_1747_ = lean_ctor_get(v_a_1743_, 0);
lean_inc(v_val_1747_);
lean_dec_ref_known(v_a_1743_, 1);
v___x_1748_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_1749_ = lean_int_dec_le(v___x_1748_, v_val_1747_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1750_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_1751_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__4, &l_Lean_Meta_normLitValue___closed__4_once, _init_l_Lean_Meta_normLitValue___closed__4);
v___x_1752_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__7, &l_Lean_Meta_normLitValue___closed__7_once, _init_l_Lean_Meta_normLitValue___closed__7);
v___x_1753_ = lean_int_neg(v_val_1747_);
lean_dec(v_val_1747_);
v___x_1754_ = l_Int_toNat(v___x_1753_);
lean_dec(v___x_1753_);
v___x_1755_ = l_Lean_instToExprInt_mkNat(v___x_1754_);
v___x_1756_ = l_Lean_mkApp3(v___x_1750_, v___x_1751_, v___x_1752_, v___x_1755_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1756_);
v___x_1758_ = v___x_1745_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1760_ = l_Int_toNat(v_val_1747_);
lean_dec(v_val_1747_);
v___x_1761_ = l_Lean_instToExprInt_mkNat(v___x_1760_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1761_);
v___x_1763_ = v___x_1745_;
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
}
else
{
lean_object* v___x_1765_; 
lean_del_object(v___x_1745_);
lean_dec(v_a_1743_);
lean_inc(v_a_1731_);
v___x_1765_ = l_Lean_Meta_getFinValue_x3f(v_a_1731_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1949_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1949_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1949_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
if (lean_obj_tag(v_a_1766_) == 1)
{
lean_object* v_val_1770_; lean_object* v_fst_1771_; lean_object* v_snd_1772_; lean_object* v_r_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_dec(v_a_1731_);
v_val_1770_ = lean_ctor_get(v_a_1766_, 0);
lean_inc(v_val_1770_);
lean_dec_ref_known(v_a_1766_, 1);
v_fst_1771_ = lean_ctor_get(v_val_1770_, 0);
lean_inc_n(v_fst_1771_, 2);
v_snd_1772_ = lean_ctor_get(v_val_1770_, 1);
lean_inc(v_snd_1772_);
lean_dec(v_val_1770_);
v_r_1773_ = l_Lean_mkRawNatLit(v_snd_1772_);
v___x_1774_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1775_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__9, &l_Lean_Meta_normLitValue___closed__9_once, _init_l_Lean_Meta_normLitValue___closed__9);
v___x_1776_ = l_Lean_mkNatLit(v_fst_1771_);
lean_inc_ref(v___x_1776_);
v___x_1777_ = l_Lean_Expr_app___override(v___x_1775_, v___x_1776_);
v___x_1778_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__12, &l_Lean_Meta_normLitValue___closed__12_once, _init_l_Lean_Meta_normLitValue___closed__12);
v___x_1779_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__15, &l_Lean_Meta_normLitValue___closed__15_once, _init_l_Lean_Meta_normLitValue___closed__15);
v___x_1780_ = lean_unsigned_to_nat(1u);
v___x_1781_ = lean_nat_sub(v_fst_1771_, v___x_1780_);
lean_dec(v_fst_1771_);
v___x_1782_ = l_Lean_mkNatLit(v___x_1781_);
v___x_1783_ = l_Lean_Expr_app___override(v___x_1779_, v___x_1782_);
lean_inc_ref(v_r_1773_);
v___x_1784_ = l_Lean_mkApp3(v___x_1778_, v___x_1776_, v___x_1783_, v_r_1773_);
v___x_1785_ = l_Lean_mkApp3(v___x_1774_, v___x_1777_, v_r_1773_, v___x_1784_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1785_);
v___x_1787_ = v___x_1768_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
else
{
lean_object* v___x_1789_; 
lean_del_object(v___x_1768_);
lean_dec(v_a_1766_);
lean_inc(v_a_1731_);
v___x_1789_ = l_Lean_Meta_getBitVecValue_x3f(v_a_1731_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1940_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1940_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1940_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
if (lean_obj_tag(v_a_1790_) == 1)
{
lean_object* v_val_1794_; lean_object* v_fst_1795_; lean_object* v_snd_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
lean_dec(v_a_1731_);
v_val_1794_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_val_1794_);
lean_dec_ref_known(v_a_1790_, 1);
v_fst_1795_ = lean_ctor_get(v_val_1794_, 0);
lean_inc(v_fst_1795_);
v_snd_1796_ = lean_ctor_get(v_val_1794_, 1);
lean_inc(v_snd_1796_);
lean_dec(v_val_1794_);
v___x_1797_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__16, &l_Lean_Meta_normLitValue___closed__16_once, _init_l_Lean_Meta_normLitValue___closed__16);
v___x_1798_ = l_Lean_mkNatLit(v_fst_1795_);
v___x_1799_ = l_Lean_mkNatLit(v_snd_1796_);
v___x_1800_ = l_Lean_mkAppB(v___x_1797_, v___x_1798_, v___x_1799_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1800_);
v___x_1802_ = v___x_1792_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
else
{
lean_object* v___x_1804_; 
lean_dec(v_a_1790_);
lean_inc(v_a_1731_);
v___x_1804_ = l_Lean_Meta_getStringValue_x3f(v_a_1731_);
if (lean_obj_tag(v___x_1804_) == 1)
{
lean_object* v_val_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
lean_dec(v_a_1731_);
v_val_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = l_Lean_mkStrLit(v_val_1805_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1806_);
v___x_1808_ = v___x_1792_;
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
lean_object* v___x_1810_; 
lean_dec(v___x_1804_);
lean_del_object(v___x_1792_);
lean_inc(v_a_1731_);
v___x_1810_ = l_Lean_Meta_getCharValue_x3f(v_a_1731_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1931_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1931_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1931_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
if (lean_obj_tag(v_a_1811_) == 1)
{
lean_object* v_val_1815_; lean_object* v___x_1816_; uint32_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
lean_dec(v_a_1731_);
v_val_1815_ = lean_ctor_get(v_a_1811_, 0);
lean_inc(v_val_1815_);
lean_dec_ref_known(v_a_1811_, 1);
v___x_1816_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__17, &l_Lean_Meta_normLitValue___closed__17_once, _init_l_Lean_Meta_normLitValue___closed__17);
v___x_1817_ = lean_unbox_uint32(v_val_1815_);
lean_dec(v_val_1815_);
v___x_1818_ = lean_uint32_to_nat(v___x_1817_);
v___x_1819_ = l_Lean_mkRawNatLit(v___x_1818_);
v___x_1820_ = l_Lean_Expr_app___override(v___x_1816_, v___x_1819_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1820_);
v___x_1822_ = v___x_1813_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
else
{
lean_object* v___x_1824_; 
lean_del_object(v___x_1813_);
lean_dec(v_a_1811_);
lean_inc(v_a_1731_);
v___x_1824_ = l_Lean_Meta_getUInt8Value_x3f(v_a_1731_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1922_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1922_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1922_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
if (lean_obj_tag(v_a_1825_) == 1)
{
lean_object* v_val_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v_r_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec(v_a_1731_);
v_val_1829_ = lean_ctor_get(v_a_1825_, 0);
lean_inc(v_val_1829_);
lean_dec_ref_known(v_a_1825_, 1);
v___x_1830_ = lean_unbox(v_val_1829_);
lean_dec(v_val_1829_);
v___x_1831_ = lean_uint8_to_nat(v___x_1830_);
v_r_1832_ = l_Lean_mkRawNatLit(v___x_1831_);
v___x_1833_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1834_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__18, &l_Lean_Meta_normLitValue___closed__18_once, _init_l_Lean_Meta_normLitValue___closed__18);
v___x_1835_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__20, &l_Lean_Meta_normLitValue___closed__20_once, _init_l_Lean_Meta_normLitValue___closed__20);
lean_inc_ref(v_r_1832_);
v___x_1836_ = l_Lean_Expr_app___override(v___x_1835_, v_r_1832_);
v___x_1837_ = l_Lean_mkApp3(v___x_1833_, v___x_1834_, v_r_1832_, v___x_1836_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1837_);
v___x_1839_ = v___x_1827_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
lean_object* v___x_1841_; 
lean_del_object(v___x_1827_);
lean_dec(v_a_1825_);
lean_inc(v_a_1731_);
v___x_1841_ = l_Lean_Meta_getUInt16Value_x3f(v_a_1731_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1913_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1913_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1913_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
if (lean_obj_tag(v_a_1842_) == 1)
{
lean_object* v_val_1846_; uint16_t v___x_1847_; lean_object* v___x_1848_; lean_object* v_r_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_dec(v_a_1731_);
v_val_1846_ = lean_ctor_get(v_a_1842_, 0);
lean_inc(v_val_1846_);
lean_dec_ref_known(v_a_1842_, 1);
v___x_1847_ = lean_unbox(v_val_1846_);
lean_dec(v_val_1846_);
v___x_1848_ = lean_uint16_to_nat(v___x_1847_);
v_r_1849_ = l_Lean_mkRawNatLit(v___x_1848_);
v___x_1850_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1851_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__21, &l_Lean_Meta_normLitValue___closed__21_once, _init_l_Lean_Meta_normLitValue___closed__21);
v___x_1852_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__23, &l_Lean_Meta_normLitValue___closed__23_once, _init_l_Lean_Meta_normLitValue___closed__23);
lean_inc_ref(v_r_1849_);
v___x_1853_ = l_Lean_Expr_app___override(v___x_1852_, v_r_1849_);
v___x_1854_ = l_Lean_mkApp3(v___x_1850_, v___x_1851_, v_r_1849_, v___x_1853_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1854_);
v___x_1856_ = v___x_1844_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
else
{
lean_object* v___x_1858_; 
lean_del_object(v___x_1844_);
lean_dec(v_a_1842_);
lean_inc(v_a_1731_);
v___x_1858_ = l_Lean_Meta_getUInt32Value_x3f(v_a_1731_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1904_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1904_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1904_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
if (lean_obj_tag(v_a_1859_) == 1)
{
lean_object* v_val_1863_; uint32_t v___x_1864_; lean_object* v___x_1865_; lean_object* v_r_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1873_; 
lean_dec(v_a_1731_);
v_val_1863_ = lean_ctor_get(v_a_1859_, 0);
lean_inc(v_val_1863_);
lean_dec_ref_known(v_a_1859_, 1);
v___x_1864_ = lean_unbox_uint32(v_val_1863_);
lean_dec(v_val_1863_);
v___x_1865_ = lean_uint32_to_nat(v___x_1864_);
v_r_1866_ = l_Lean_mkRawNatLit(v___x_1865_);
v___x_1867_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1868_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__24, &l_Lean_Meta_normLitValue___closed__24_once, _init_l_Lean_Meta_normLitValue___closed__24);
v___x_1869_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__26, &l_Lean_Meta_normLitValue___closed__26_once, _init_l_Lean_Meta_normLitValue___closed__26);
lean_inc_ref(v_r_1866_);
v___x_1870_ = l_Lean_Expr_app___override(v___x_1869_, v_r_1866_);
v___x_1871_ = l_Lean_mkApp3(v___x_1867_, v___x_1868_, v_r_1866_, v___x_1870_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1871_);
v___x_1873_ = v___x_1861_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
else
{
lean_object* v___x_1875_; 
lean_del_object(v___x_1861_);
lean_dec(v_a_1859_);
lean_inc(v_a_1731_);
v___x_1875_ = l_Lean_Meta_getUInt64Value_x3f(v_a_1731_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1895_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1895_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1895_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
if (lean_obj_tag(v_a_1876_) == 1)
{
lean_object* v_val_1880_; uint64_t v___x_1881_; lean_object* v___x_1882_; lean_object* v_r_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
lean_dec(v_a_1731_);
v_val_1880_ = lean_ctor_get(v_a_1876_, 0);
lean_inc(v_val_1880_);
lean_dec_ref_known(v_a_1876_, 1);
v___x_1881_ = lean_unbox_uint64(v_val_1880_);
lean_dec(v_val_1880_);
v___x_1882_ = lean_uint64_to_nat(v___x_1881_);
v_r_1883_ = l_Lean_mkRawNatLit(v___x_1882_);
v___x_1884_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1885_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__27, &l_Lean_Meta_normLitValue___closed__27_once, _init_l_Lean_Meta_normLitValue___closed__27);
v___x_1886_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__29, &l_Lean_Meta_normLitValue___closed__29_once, _init_l_Lean_Meta_normLitValue___closed__29);
lean_inc_ref(v_r_1883_);
v___x_1887_ = l_Lean_Expr_app___override(v___x_1886_, v_r_1883_);
v___x_1888_ = l_Lean_mkApp3(v___x_1884_, v___x_1885_, v_r_1883_, v___x_1887_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1888_);
v___x_1890_ = v___x_1878_;
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
else
{
lean_object* v___x_1893_; 
lean_dec(v_a_1876_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v_a_1731_);
v___x_1893_ = v___x_1878_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1731_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec(v_a_1731_);
v_a_1896_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1875_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1875_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v_a_1731_);
v_a_1905_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1858_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1858_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_a_1731_);
v_a_1914_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1841_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1841_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec(v_a_1731_);
v_a_1923_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1824_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1824_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v_a_1731_);
v_a_1932_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1810_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1810_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v_a_1731_);
v_a_1941_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1789_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1789_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_a_1731_);
v_a_1950_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1765_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1765_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v_a_1731_);
v_a_1959_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1742_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1742_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v_a_1731_);
v_a_1968_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1732_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1732_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_normLitValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1724_ = stack[0].m_obj;
lean_object* v_a_1725_ = stack[1].m_obj;
lean_object* v_a_1726_ = stack[2].m_obj;
lean_object* v_a_1727_ = stack[3].m_obj;
lean_object* v_a_1728_ = stack[4].m_obj;
lean_object* v_res_1976_;
v_res_1976_ = l_Lean_Meta_normLitValue(v_e_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
stack->m_obj
 = v_res_1976_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue___boxed(lean_object* v_e_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Meta_normLitValue(v_e_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
return v_res_1983_;
}
}
lean_object* l_Lean_Meta_isLitValue(lean_object* v_e_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v___x_1990_; lean_object* v_a_1991_; lean_object* v___x_1992_; 
v___x_1990_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1984_, v_a_1986_);
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref(v___x_1990_);
v___x_1992_ = l_Lean_Meta_getNatValue_x3f(v_a_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2193_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2193_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2193_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
if (lean_obj_tag(v_a_1993_) == 0)
{
uint8_t v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; 
lean_del_object(v___x_1995_);
v___x_1997_ = 0;
v___x_1998_ = 1;
lean_inc(v_a_1991_);
v___x_1999_ = l_Lean_Meta_getIntValue_x3f(v_a_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2179_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2179_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2179_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
if (lean_obj_tag(v_a_2000_) == 0)
{
lean_object* v___x_2004_; 
lean_del_object(v___x_2002_);
lean_inc(v_a_1991_);
v___x_2004_ = l_Lean_Meta_getFinValue_x3f(v_a_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2166_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2166_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2166_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
if (lean_obj_tag(v_a_2005_) == 0)
{
lean_object* v___x_2009_; 
lean_del_object(v___x_2007_);
lean_inc(v_a_1991_);
v___x_2009_ = l_Lean_Meta_getBitVecValue_x3f(v_a_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2153_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2153_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2153_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
if (lean_obj_tag(v_a_2010_) == 0)
{
lean_object* v___x_2014_; 
lean_inc(v_a_1991_);
v___x_2014_ = l_Lean_Meta_getStringValue_x3f(v_a_1991_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2015_; 
lean_del_object(v___x_2012_);
lean_inc(v_a_1991_);
v___x_2015_ = l_Lean_Meta_getCharValue_x3f(v_a_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2136_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2136_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2136_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
if (lean_obj_tag(v_a_2016_) == 0)
{
lean_object* v___x_2020_; 
lean_del_object(v___x_2018_);
lean_inc(v_a_1991_);
v___x_2020_ = l_Lean_Meta_getUInt8Value_x3f(v_a_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2123_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2123_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2123_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
if (lean_obj_tag(v_a_2021_) == 0)
{
lean_object* v___x_2025_; 
lean_del_object(v___x_2023_);
lean_inc(v_a_1991_);
v___x_2025_ = l_Lean_Meta_getUInt16Value_x3f(v_a_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2110_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2110_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2110_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
if (lean_obj_tag(v_a_2026_) == 0)
{
lean_object* v___x_2030_; 
lean_del_object(v___x_2028_);
lean_inc(v_a_1991_);
v___x_2030_ = l_Lean_Meta_getUInt32Value_x3f(v_a_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2097_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2097_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2097_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
if (lean_obj_tag(v_a_2031_) == 0)
{
lean_object* v___x_2035_; 
lean_del_object(v___x_2033_);
lean_inc(v_a_1991_);
v___x_2035_ = l_Lean_Meta_getUInt64Value_x3f(v_a_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2084_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2084_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2084_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
if (lean_obj_tag(v_a_2036_) == 0)
{
lean_object* v___x_2040_; 
lean_del_object(v___x_2038_);
lean_inc(v_a_1991_);
v___x_2040_ = l_Lean_Meta_getFloatValue_x3f(v_a_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2071_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2071_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2071_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
if (lean_obj_tag(v_a_2041_) == 0)
{
lean_object* v___x_2045_; 
lean_del_object(v___x_2043_);
v___x_2045_ = l_Lean_Meta_getFloat32Value_x3f(v_a_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2058_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2058_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2058_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
if (lean_obj_tag(v_a_2046_) == 0)
{
lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2050_ = lean_box(v___x_1997_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2050_);
v___x_2052_ = v___x_2048_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
lean_dec_ref_known(v_a_2046_, 1);
v___x_2054_ = lean_box(v___x_1998_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2054_);
v___x_2056_ = v___x_2048_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2045_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2045_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
lean_dec_ref_known(v_a_2041_, 1);
lean_dec(v_a_1991_);
v___x_2067_ = lean_box(v___x_1998_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2067_);
v___x_2069_ = v___x_2043_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_a_1991_);
v_a_2072_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2040_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2040_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
lean_dec_ref_known(v_a_2036_, 1);
lean_dec(v_a_1991_);
v___x_2080_ = lean_box(v___x_1998_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2080_);
v___x_2082_ = v___x_2038_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_a_1991_);
v_a_2085_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2035_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2035_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
lean_dec_ref_known(v_a_2031_, 1);
lean_dec(v_a_1991_);
v___x_2093_ = lean_box(v___x_1998_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2093_);
v___x_2095_ = v___x_2033_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v_a_1991_);
v_a_2098_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2030_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2030_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
lean_dec_ref_known(v_a_2026_, 1);
lean_dec(v_a_1991_);
v___x_2106_ = lean_box(v___x_1998_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2106_);
v___x_2108_ = v___x_2028_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v_a_1991_);
v_a_2111_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2025_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2025_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
lean_dec_ref_known(v_a_2021_, 1);
lean_dec(v_a_1991_);
v___x_2119_ = lean_box(v___x_1998_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2119_);
v___x_2121_ = v___x_2023_;
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
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec(v_a_1991_);
v_a_2124_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2020_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2020_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
lean_dec_ref_known(v_a_2016_, 1);
lean_dec(v_a_1991_);
v___x_2132_ = lean_box(v___x_1998_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2132_);
v___x_2134_ = v___x_2018_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_a_1991_);
v_a_2137_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2015_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2015_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
lean_dec_ref_known(v___x_2014_, 1);
lean_dec(v_a_1991_);
v___x_2145_ = lean_box(v___x_1998_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2145_);
v___x_2147_ = v___x_2012_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
lean_dec_ref_known(v_a_2010_, 1);
lean_dec(v_a_1991_);
v___x_2149_ = lean_box(v___x_1998_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2149_);
v___x_2151_ = v___x_2012_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
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
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_a_1991_);
v_a_2154_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2009_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2009_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
lean_dec_ref_known(v_a_2005_, 1);
lean_dec(v_a_1991_);
v___x_2162_ = lean_box(v___x_1998_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2162_);
v___x_2164_ = v___x_2007_;
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
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_a_1991_);
v_a_2167_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2004_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2004_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
lean_dec_ref_known(v_a_2000_, 1);
lean_dec(v_a_1991_);
v___x_2175_ = lean_box(v___x_1998_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2175_);
v___x_2177_ = v___x_2002_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_a_1991_);
v_a_2180_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_1999_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_1999_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
uint8_t v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
lean_dec_ref_known(v_a_1993_, 1);
lean_dec(v_a_1991_);
v___x_2188_ = 1;
v___x_2189_ = lean_box(v___x_2188_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2189_);
v___x_2191_ = v___x_1995_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v_a_1991_);
v_a_2194_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_1992_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_1992_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
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
}
LEAN_EXPORT void l_Lean_Meta_isLitValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1984_ = stack[0].m_obj;
lean_object* v_a_1985_ = stack[1].m_obj;
lean_object* v_a_1986_ = stack[2].m_obj;
lean_object* v_a_1987_ = stack[3].m_obj;
lean_object* v_a_1988_ = stack[4].m_obj;
lean_object* v_res_2202_;
v_res_2202_ = l_Lean_Meta_isLitValue(v_e_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
stack->m_obj
 = v_res_2202_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue___boxed(lean_object* v_e_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_Meta_isLitValue(v_e_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
return v_res_2209_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__2(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = lean_box(0);
v___x_2215_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__1));
v___x_2216_ = l_Lean_mkConst(v___x_2215_, v___x_2214_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__5(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = lean_box(0);
v___x_2222_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__4));
v___x_2223_ = l_Lean_mkConst(v___x_2222_, v___x_2221_);
return v___x_2223_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__7(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_box(0);
v___x_2228_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__6));
v___x_2229_ = l_Lean_mkConst(v___x_2228_, v___x_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__10(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = lean_box(0);
v___x_2235_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__9));
v___x_2236_ = l_Lean_mkConst(v___x_2235_, v___x_2234_);
return v___x_2236_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__11(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_to_int(v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__15(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_2245_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__14));
v___x_2246_ = l_Lean_mkConst(v___x_2245_, v___x_2244_);
return v___x_2246_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__16(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = lean_box(0);
v___x_2248_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_2249_ = l_Lean_mkConst(v___x_2248_, v___x_2247_);
return v___x_2249_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__19(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = lean_box(0);
v___x_2254_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__18));
v___x_2255_ = l_Lean_mkConst(v___x_2254_, v___x_2253_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__22(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2259_ = lean_box(0);
v___x_2260_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__21));
v___x_2261_ = l_Lean_mkConst(v___x_2260_, v___x_2259_);
return v___x_2261_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__25(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__24));
v___x_2268_ = l_Lean_mkConst(v___x_2267_, v___x_2266_);
return v___x_2268_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__28(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__27));
v___x_2275_ = l_Lean_mkConst(v___x_2274_, v___x_2273_);
return v___x_2275_;
}
}
lean_object* l_Lean_Meta_litToCtor(lean_object* v_e_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___x_2282_; lean_object* v_a_2283_; lean_object* v___x_2284_; 
v___x_2282_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2276_, v_a_2278_);
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref(v___x_2282_);
v___x_2284_ = l_Lean_Meta_getNatValue_x3f(v_a_2283_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2374_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2374_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2374_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
if (lean_obj_tag(v_a_2285_) == 1)
{
lean_object* v_val_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
lean_dec(v_a_2283_);
v_val_2289_ = lean_ctor_get(v_a_2285_, 0);
lean_inc(v_val_2289_);
lean_dec_ref_known(v_a_2285_, 1);
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = lean_nat_dec_eq(v_val_2289_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2292_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__2, &l_Lean_Meta_litToCtor___closed__2_once, _init_l_Lean_Meta_litToCtor___closed__2);
v___x_2293_ = lean_unsigned_to_nat(1u);
v___x_2294_ = lean_nat_sub(v_val_2289_, v___x_2293_);
lean_dec(v_val_2289_);
v___x_2295_ = l_Lean_mkNatLit(v___x_2294_);
v___x_2296_ = l_Lean_Expr_app___override(v___x_2292_, v___x_2295_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2296_);
v___x_2298_ = v___x_2287_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
lean_dec(v_val_2289_);
v___x_2300_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__5, &l_Lean_Meta_litToCtor___closed__5_once, _init_l_Lean_Meta_litToCtor___closed__5);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2300_);
v___x_2302_ = v___x_2287_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
else
{
lean_object* v___x_2304_; 
lean_del_object(v___x_2287_);
lean_dec(v_a_2285_);
lean_inc(v_a_2283_);
v___x_2304_ = l_Lean_Meta_getIntValue_x3f(v_a_2283_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2365_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2307_ = v___x_2304_;
v_isShared_2308_ = v_isSharedCheck_2365_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2365_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
if (lean_obj_tag(v_a_2305_) == 1)
{
lean_object* v_val_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
lean_dec(v_a_2283_);
v_val_2309_ = lean_ctor_get(v_a_2305_, 0);
lean_inc(v_val_2309_);
lean_dec_ref_known(v_a_2305_, 1);
v___x_2310_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_2311_ = lean_int_dec_lt(v_val_2309_, v___x_2310_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2312_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__7, &l_Lean_Meta_litToCtor___closed__7_once, _init_l_Lean_Meta_litToCtor___closed__7);
v___x_2313_ = l_Int_toNat(v_val_2309_);
lean_dec(v_val_2309_);
v___x_2314_ = l_Lean_mkNatLit(v___x_2313_);
v___x_2315_ = l_Lean_Expr_app___override(v___x_2312_, v___x_2314_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2315_);
v___x_2317_ = v___x_2307_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2319_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__10, &l_Lean_Meta_litToCtor___closed__10_once, _init_l_Lean_Meta_litToCtor___closed__10);
v___x_2320_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__11, &l_Lean_Meta_litToCtor___closed__11_once, _init_l_Lean_Meta_litToCtor___closed__11);
v___x_2321_ = lean_int_add(v_val_2309_, v___x_2320_);
lean_dec(v_val_2309_);
v___x_2322_ = lean_int_neg(v___x_2321_);
lean_dec(v___x_2321_);
v___x_2323_ = l_Int_toNat(v___x_2322_);
lean_dec(v___x_2322_);
v___x_2324_ = l_Lean_mkNatLit(v___x_2323_);
v___x_2325_ = l_Lean_Expr_app___override(v___x_2319_, v___x_2324_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2325_);
v___x_2327_ = v___x_2307_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_object* v___x_2329_; 
lean_del_object(v___x_2307_);
lean_dec(v_a_2305_);
lean_inc(v_a_2283_);
v___x_2329_ = l_Lean_Meta_getFinValue_x3f(v_a_2283_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2356_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2356_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2356_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
if (lean_obj_tag(v_a_2330_) == 1)
{
lean_object* v_val_2334_; lean_object* v_fst_2335_; lean_object* v_snd_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
lean_dec(v_a_2283_);
v_val_2334_ = lean_ctor_get(v_a_2330_, 0);
lean_inc(v_val_2334_);
lean_dec_ref_known(v_a_2330_, 1);
v_fst_2335_ = lean_ctor_get(v_val_2334_, 0);
lean_inc(v_fst_2335_);
v_snd_2336_ = lean_ctor_get(v_val_2334_, 1);
lean_inc(v_snd_2336_);
lean_dec(v_val_2334_);
v___x_2337_ = l_Lean_mkNatLit(v_snd_2336_);
v___x_2338_ = l_Lean_mkNatLit(v_fst_2335_);
v___x_2339_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__15, &l_Lean_Meta_litToCtor___closed__15_once, _init_l_Lean_Meta_litToCtor___closed__15);
v___x_2340_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__16, &l_Lean_Meta_litToCtor___closed__16_once, _init_l_Lean_Meta_litToCtor___closed__16);
v___x_2341_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__19, &l_Lean_Meta_litToCtor___closed__19_once, _init_l_Lean_Meta_litToCtor___closed__19);
lean_inc_ref_n(v___x_2338_, 2);
lean_inc_ref_n(v___x_2337_, 2);
v___x_2342_ = l_Lean_mkApp4(v___x_2339_, v___x_2340_, v___x_2341_, v___x_2337_, v___x_2338_);
v___x_2343_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__22, &l_Lean_Meta_litToCtor___closed__22_once, _init_l_Lean_Meta_litToCtor___closed__22);
v___x_2344_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__25, &l_Lean_Meta_litToCtor___closed__25_once, _init_l_Lean_Meta_litToCtor___closed__25);
v___x_2345_ = l_Lean_mkAppB(v___x_2344_, v___x_2337_, v___x_2338_);
v___x_2346_ = l_Lean_eagerReflBoolTrue;
v___x_2347_ = l_Lean_mkApp3(v___x_2343_, v___x_2342_, v___x_2345_, v___x_2346_);
v___x_2348_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__28, &l_Lean_Meta_litToCtor___closed__28_once, _init_l_Lean_Meta_litToCtor___closed__28);
v___x_2349_ = l_Lean_mkApp3(v___x_2348_, v___x_2338_, v___x_2337_, v___x_2347_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2349_);
v___x_2351_ = v___x_2332_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
else
{
lean_object* v___x_2354_; 
lean_dec(v_a_2330_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v_a_2283_);
v___x_2354_ = v___x_2332_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2283_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_a_2283_);
v_a_2357_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2329_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2329_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_a_2283_);
v_a_2366_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2304_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2304_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v_a_2283_);
v_a_2375_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2284_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2284_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_litToCtor_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2276_ = stack[0].m_obj;
lean_object* v_a_2277_ = stack[1].m_obj;
lean_object* v_a_2278_ = stack[2].m_obj;
lean_object* v_a_2279_ = stack[3].m_obj;
lean_object* v_a_2280_ = stack[4].m_obj;
lean_object* v_res_2383_;
v_res_2383_ = l_Lean_Meta_litToCtor(v_e_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
stack->m_obj
 = v_res_2383_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor___boxed(lean_object* v_e_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Meta_litToCtor(v_e_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
return v_res_2390_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(lean_object* v_fst_2393_, lean_object* v_snd_2394_, lean_object* v_x_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2401_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0));
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_fst_2393_);
lean_ctor_set(v___x_2402_, 1, v_snd_2394_);
v___x_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2401_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2393_ = stack[0].m_obj;
lean_object* v_snd_2394_ = stack[1].m_obj;
lean_object* v_x_2395_ = stack[2].m_obj;
lean_object* v___y_2396_ = stack[3].m_obj;
lean_object* v___y_2397_ = stack[4].m_obj;
lean_object* v___y_2398_ = stack[5].m_obj;
lean_object* v___y_2399_ = stack[6].m_obj;
lean_object* v_res_2406_;
v_res_2406_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2393_, v_snd_2394_, v_x_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
stack->m_obj
 = v_res_2406_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2407_, lean_object* v_snd_2408_, lean_object* v_x_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2407_, v_snd_2408_, v_x_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
return v_res_2415_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(lean_object* v_f_2427_, lean_object* v_a_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___y_2435_; lean_object* v_snd_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2543_; 
v_snd_2455_ = lean_ctor_get(v_a_2428_, 1);
v_isSharedCheck_2543_ = !lean_is_exclusive(v_a_2428_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v_a_2428_, 0);
lean_dec(v_unused_2544_);
v___x_2457_ = v_a_2428_;
v_isShared_2458_ = v_isSharedCheck_2543_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_snd_2455_);
lean_dec(v_a_2428_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2543_;
goto v_resetjp_2456_;
}
v___jp_2434_:
{
if (lean_obj_tag(v___y_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2446_; 
v_a_2436_ = lean_ctor_get(v___y_2435_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___y_2435_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2438_ = v___y_2435_;
v_isShared_2439_ = v_isSharedCheck_2446_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___y_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2446_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
if (lean_obj_tag(v_a_2436_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2442_; 
lean_dec_ref(v_f_2427_);
v_a_2440_ = lean_ctor_get(v_a_2436_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v_a_2436_, 1);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v_a_2440_);
v___x_2442_ = v___x_2438_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
else
{
lean_object* v_a_2444_; 
lean_del_object(v___x_2438_);
v_a_2444_ = lean_ctor_get(v_a_2436_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v_a_2436_, 1);
v_a_2428_ = v_a_2444_;
goto _start;
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec_ref(v_f_2427_);
v_a_2447_ = lean_ctor_get(v___y_2435_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___y_2435_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___y_2435_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___y_2435_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
v_resetjp_2456_:
{
lean_object* v_fst_2459_; lean_object* v_snd_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2542_; 
v_fst_2459_ = lean_ctor_get(v_snd_2455_, 0);
v_snd_2460_ = lean_ctor_get(v_snd_2455_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_snd_2455_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2462_ = v_snd_2455_;
v_isShared_2463_ = v_isSharedCheck_2542_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_snd_2460_);
lean_inc(v_fst_2459_);
lean_dec(v_snd_2455_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2542_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = lean_box(0);
lean_inc(v_fst_2459_);
v___x_2465_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_fst_2459_, v___y_2430_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2533_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2533_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2533_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2470_ = l_Lean_Expr_cleanupAnnotations(v_a_2466_);
v___x_2471_ = l_Lean_Expr_isApp(v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_dec_ref(v___x_2470_);
lean_del_object(v___x_2468_);
lean_del_object(v___x_2462_);
lean_del_object(v___x_2457_);
v___x_2472_ = lean_box(0);
v___x_2473_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2459_, v_snd_2460_, v___x_2472_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
v___y_2435_ = v___x_2473_;
goto v___jp_2434_;
}
else
{
lean_object* v_arg_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v_arg_2474_ = lean_ctor_get(v___x_2470_, 1);
lean_inc_ref(v_arg_2474_);
v___x_2475_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2470_);
v___x_2476_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2));
v___x_2477_ = l_Lean_Expr_isConstOf(v___x_2475_, v___x_2476_);
if (v___x_2477_ == 0)
{
uint8_t v___x_2478_; 
lean_del_object(v___x_2468_);
v___x_2478_ = l_Lean_Expr_isApp(v___x_2475_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec_ref(v___x_2475_);
lean_dec_ref(v_arg_2474_);
lean_del_object(v___x_2462_);
lean_del_object(v___x_2457_);
v___x_2479_ = lean_box(0);
v___x_2480_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2459_, v_snd_2460_, v___x_2479_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
v___y_2435_ = v___x_2480_;
goto v___jp_2434_;
}
else
{
lean_object* v_arg_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_arg_2481_ = lean_ctor_get(v___x_2475_, 1);
lean_inc_ref(v_arg_2481_);
v___x_2482_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2475_);
v___x_2483_ = l_Lean_Expr_isApp(v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec_ref(v___x_2482_);
lean_dec_ref(v_arg_2481_);
lean_dec_ref(v_arg_2474_);
lean_del_object(v___x_2462_);
lean_del_object(v___x_2457_);
v___x_2484_ = lean_box(0);
v___x_2485_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2459_, v_snd_2460_, v___x_2484_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
v___y_2435_ = v___x_2485_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2486_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2482_);
v___x_2487_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4));
v___x_2488_ = l_Lean_Expr_isConstOf(v___x_2486_, v___x_2487_);
lean_dec_ref(v___x_2486_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
lean_dec_ref(v_arg_2481_);
lean_dec_ref(v_arg_2474_);
lean_del_object(v___x_2462_);
lean_del_object(v___x_2457_);
v___x_2489_ = lean_box(0);
v___x_2490_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2459_, v_snd_2460_, v___x_2489_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
v___y_2435_ = v___x_2490_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2491_; 
lean_inc_ref(v_f_2427_);
lean_inc(v___y_2432_);
lean_inc_ref(v___y_2431_);
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2429_);
v___x_2491_ = lean_apply_6(v_f_2427_, v_arg_2481_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, lean_box(0));
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2515_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2515_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2515_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
if (lean_obj_tag(v_a_2492_) == 1)
{
lean_object* v_val_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
lean_del_object(v___x_2494_);
lean_dec(v_fst_2459_);
v_val_2496_ = lean_ctor_get(v_a_2492_, 0);
lean_inc(v_val_2496_);
lean_dec_ref_known(v_a_2492_, 1);
v___x_2497_ = lean_array_push(v_snd_2460_, v_val_2496_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v___x_2497_);
lean_ctor_set(v___x_2462_, 0, v_arg_2474_);
v___x_2499_ = v___x_2462_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_arg_2474_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2501_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 1, v___x_2499_);
lean_ctor_set(v___x_2457_, 0, v___x_2464_);
v___x_2501_ = v___x_2457_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
v_a_2428_ = v___x_2501_;
goto _start;
}
}
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2507_; 
lean_dec(v_a_2492_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_f_2427_);
v___x_2505_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5));
if (v_isShared_2463_ == 0)
{
v___x_2507_ = v___x_2462_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_fst_2459_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_snd_2460_);
v___x_2507_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2509_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 1, v___x_2507_);
lean_ctor_set(v___x_2457_, 0, v___x_2505_);
v___x_2509_ = v___x_2457_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2505_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2511_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2509_);
v___x_2511_ = v___x_2494_;
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
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec_ref(v_arg_2474_);
lean_del_object(v___x_2462_);
lean_dec(v_snd_2460_);
lean_dec(v_fst_2459_);
lean_del_object(v___x_2457_);
lean_dec_ref(v_f_2427_);
v_a_2516_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2491_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2491_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2525_; 
lean_dec_ref(v___x_2475_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_f_2427_);
if (v_isShared_2463_ == 0)
{
v___x_2525_ = v___x_2462_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_fst_2459_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_snd_2460_);
v___x_2525_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
lean_object* v___x_2527_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 1, v___x_2525_);
lean_ctor_set(v___x_2457_, 0, v___x_2464_);
v___x_2527_ = v___x_2457_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2529_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2527_);
v___x_2529_ = v___x_2468_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_del_object(v___x_2462_);
lean_dec(v_snd_2460_);
lean_dec(v_fst_2459_);
lean_del_object(v___x_2457_);
lean_dec_ref(v_f_2427_);
v_a_2534_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2465_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2465_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2427_ = stack[0].m_obj;
lean_object* v_a_2428_ = stack[1].m_obj;
lean_object* v___y_2429_ = stack[2].m_obj;
lean_object* v___y_2430_ = stack[3].m_obj;
lean_object* v___y_2431_ = stack[4].m_obj;
lean_object* v___y_2432_ = stack[5].m_obj;
lean_object* v_res_2545_;
v_res_2545_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_2427_, v_a_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
stack->m_obj
 = v_res_2545_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___boxed(lean_object* v_f_2546_, lean_object* v_a_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_2546_, v_a_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
return v_res_2553_;
}
}
lean_object* l_Lean_Meta_getListLitOf_x3f___redArg(lean_object* v_e_2556_, lean_object* v_f_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2600_; 
v___x_2563_ = l_Lean_Expr_consumeMData(v_e_2556_);
v___x_2564_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_2563_, v_a_2559_);
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2600_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2600_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2569_ = ((lean_object*)(l_Lean_Meta_getListLitOf_x3f___redArg___closed__0));
v___x_2570_ = lean_box(0);
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v_a_2565_);
lean_ctor_set(v___x_2571_, 1, v___x_2569_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_2557_, v___x_2572_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2591_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2591_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2591_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v_fst_2578_; 
v_fst_2578_ = lean_ctor_get(v_a_2574_, 0);
if (lean_obj_tag(v_fst_2578_) == 0)
{
lean_object* v_snd_2579_; lean_object* v_snd_2580_; lean_object* v___x_2582_; 
v_snd_2579_ = lean_ctor_get(v_a_2574_, 1);
lean_inc(v_snd_2579_);
lean_dec(v_a_2574_);
v_snd_2580_ = lean_ctor_get(v_snd_2579_, 1);
lean_inc(v_snd_2580_);
lean_dec(v_snd_2579_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 1);
lean_ctor_set(v___x_2567_, 0, v_snd_2580_);
v___x_2582_ = v___x_2567_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_snd_2580_);
v___x_2582_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2584_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2582_);
v___x_2584_ = v___x_2576_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
lean_object* v_val_2587_; lean_object* v___x_2589_; 
lean_inc_ref(v_fst_2578_);
lean_dec(v_a_2574_);
lean_del_object(v___x_2567_);
v_val_2587_ = lean_ctor_get(v_fst_2578_, 0);
lean_inc(v_val_2587_);
lean_dec_ref_known(v_fst_2578_, 1);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v_val_2587_);
v___x_2589_ = v___x_2576_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_val_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_del_object(v___x_2567_);
v_a_2592_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2573_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2573_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getListLitOf_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2556_ = stack[0].m_obj;
lean_object* v_f_2557_ = stack[1].m_obj;
lean_object* v_a_2558_ = stack[2].m_obj;
lean_object* v_a_2559_ = stack[3].m_obj;
lean_object* v_a_2560_ = stack[4].m_obj;
lean_object* v_a_2561_ = stack[5].m_obj;
lean_object* v_res_2601_;
v_res_2601_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_2556_, v_f_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
stack->m_obj
 = v_res_2601_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___boxed(lean_object* v_e_2602_, lean_object* v_f_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_2602_, v_f_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec_ref(v_e_2602_);
return v_res_2609_;
}
}
lean_object* l_Lean_Meta_getListLitOf_x3f(lean_object* v_00_u03b1_2610_, lean_object* v_e_2611_, lean_object* v_f_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_2611_, v_f_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
return v___x_2618_;
}
}
LEAN_EXPORT void l_Lean_Meta_getListLitOf_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2611_ = stack[1].m_obj;
lean_object* v_f_2612_ = stack[2].m_obj;
lean_object* v_a_2613_ = stack[3].m_obj;
lean_object* v_a_2614_ = stack[4].m_obj;
lean_object* v_a_2615_ = stack[5].m_obj;
lean_object* v_a_2616_ = stack[6].m_obj;
lean_object* v_res_2619_;
v_res_2619_ = l_Lean_Meta_getListLitOf_x3f(lean_box(0), v_e_2611_, v_f_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
stack->m_obj
 = v_res_2619_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___boxed(lean_object* v_00_u03b1_2620_, lean_object* v_e_2621_, lean_object* v_f_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_Meta_getListLitOf_x3f(v_00_u03b1_2620_, v_e_2621_, v_f_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec_ref(v_e_2621_);
return v_res_2628_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(lean_object* v_00_u03b1_2629_, lean_object* v_f_2630_, lean_object* v_inst_2631_, lean_object* v_a_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_2630_, v_a_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
return v___x_2638_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2630_ = stack[1].m_obj;
lean_object* v_a_2632_ = stack[3].m_obj;
lean_object* v___y_2633_ = stack[4].m_obj;
lean_object* v___y_2634_ = stack[5].m_obj;
lean_object* v___y_2635_ = stack[6].m_obj;
lean_object* v___y_2636_ = stack[7].m_obj;
lean_object* v_res_2639_;
v_res_2639_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(lean_box(0), v_f_2630_, lean_box(0), v_a_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
stack->m_obj
 = v_res_2639_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_f_2641_, lean_object* v_inst_2642_, lean_object* v_a_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(v_00_u03b1_2640_, v_f_2641_, v_inst_2642_, v_a_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
return v_res_2649_;
}
}
lean_object* l_Lean_Meta_getListLit_x3f___lam__0(lean_object* v_s_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_s_2650_);
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT void l_Lean_Meta_getListLit_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2650_ = stack[0].m_obj;
lean_object* v___y_2651_ = stack[1].m_obj;
lean_object* v___y_2652_ = stack[2].m_obj;
lean_object* v___y_2653_ = stack[3].m_obj;
lean_object* v___y_2654_ = stack[4].m_obj;
lean_object* v_res_2658_;
v_res_2658_ = l_Lean_Meta_getListLit_x3f___lam__0(v_s_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
stack->m_obj
 = v_res_2658_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0___boxed(lean_object* v_s_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Meta_getListLit_x3f___lam__0(v_s_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
return v_res_2665_;
}
}
lean_object* l_Lean_Meta_getListLit_x3f(lean_object* v_e_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v___f_2673_; lean_object* v___x_2674_; 
v___f_2673_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_2674_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_2667_, v___f_2673_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
return v___x_2674_;
}
}
LEAN_EXPORT void l_Lean_Meta_getListLit_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2667_ = stack[0].m_obj;
lean_object* v_a_2668_ = stack[1].m_obj;
lean_object* v_a_2669_ = stack[2].m_obj;
lean_object* v_a_2670_ = stack[3].m_obj;
lean_object* v_a_2671_ = stack[4].m_obj;
lean_object* v_res_2675_;
v_res_2675_ = l_Lean_Meta_getListLit_x3f(v_e_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
stack->m_obj
 = v_res_2675_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___boxed(lean_object* v_e_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_Meta_getListLit_x3f(v_e_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec_ref(v_e_2676_);
return v_res_2682_;
}
}
lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg(lean_object* v_e_2687_, lean_object* v_f_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v_a_2699_; lean_object* v___x_2700_; 
v___x_2697_ = l_Lean_Expr_consumeMData(v_e_2687_);
v___x_2698_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_2697_, v_a_2690_);
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref(v___x_2698_);
v___x_2700_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2699_, v_a_2690_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___x_2700_, 1);
v___x_2702_ = l_Lean_Expr_cleanupAnnotations(v_a_2701_);
v___x_2703_ = l_Lean_Expr_isApp(v___x_2702_);
if (v___x_2703_ == 0)
{
lean_dec_ref(v___x_2702_);
lean_dec_ref(v_f_2688_);
goto v___jp_2694_;
}
else
{
lean_object* v_arg_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v_arg_2704_ = lean_ctor_get(v___x_2702_, 1);
lean_inc_ref(v_arg_2704_);
v___x_2705_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2702_);
v___x_2706_ = l_Lean_Expr_isApp(v___x_2705_);
if (v___x_2706_ == 0)
{
lean_dec_ref(v___x_2705_);
lean_dec_ref(v_arg_2704_);
lean_dec_ref(v_f_2688_);
goto v___jp_2694_;
}
else
{
lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2707_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2705_);
v___x_2708_ = ((lean_object*)(l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1));
v___x_2709_ = l_Lean_Expr_isConstOf(v___x_2707_, v___x_2708_);
lean_dec_ref(v___x_2707_);
if (v___x_2709_ == 0)
{
lean_dec_ref(v_arg_2704_);
lean_dec_ref(v_f_2688_);
goto v___jp_2694_;
}
else
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_arg_2704_, v_f_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec_ref(v_arg_2704_);
return v___x_2710_;
}
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v_f_2688_);
v_a_2711_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2700_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2700_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
v___jp_2694_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = lean_box(0);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
return v___x_2696_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getArrayLitOf_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2687_ = stack[0].m_obj;
lean_object* v_f_2688_ = stack[1].m_obj;
lean_object* v_a_2689_ = stack[2].m_obj;
lean_object* v_a_2690_ = stack[3].m_obj;
lean_object* v_a_2691_ = stack[4].m_obj;
lean_object* v_a_2692_ = stack[5].m_obj;
lean_object* v_res_2719_;
v_res_2719_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2687_, v_f_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
stack->m_obj
 = v_res_2719_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___boxed(lean_object* v_e_2720_, lean_object* v_f_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2720_, v_f_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec_ref(v_e_2720_);
return v_res_2727_;
}
}
lean_object* l_Lean_Meta_getArrayLitOf_x3f(lean_object* v_00_u03b1_2728_, lean_object* v_e_2729_, lean_object* v_f_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2729_, v_f_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
return v___x_2736_;
}
}
LEAN_EXPORT void l_Lean_Meta_getArrayLitOf_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2729_ = stack[1].m_obj;
lean_object* v_f_2730_ = stack[2].m_obj;
lean_object* v_a_2731_ = stack[3].m_obj;
lean_object* v_a_2732_ = stack[4].m_obj;
lean_object* v_a_2733_ = stack[5].m_obj;
lean_object* v_a_2734_ = stack[6].m_obj;
lean_object* v_res_2737_;
v_res_2737_ = l_Lean_Meta_getArrayLitOf_x3f(lean_box(0), v_e_2729_, v_f_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
stack->m_obj
 = v_res_2737_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___boxed(lean_object* v_00_u03b1_2738_, lean_object* v_e_2739_, lean_object* v_f_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_Meta_getArrayLitOf_x3f(v_00_u03b1_2738_, v_e_2739_, v_f_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
lean_dec_ref(v_e_2739_);
return v_res_2746_;
}
}
lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object* v_e_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v___f_2753_; lean_object* v___x_2754_; 
v___f_2753_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_2754_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2747_, v___f_2753_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
return v___x_2754_;
}
}
LEAN_EXPORT void l_Lean_Meta_getArrayLit_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2747_ = stack[0].m_obj;
lean_object* v_a_2748_ = stack[1].m_obj;
lean_object* v_a_2749_ = stack[2].m_obj;
lean_object* v_a_2750_ = stack[3].m_obj;
lean_object* v_a_2751_ = stack[4].m_obj;
lean_object* v_res_2755_;
v_res_2755_ = l_Lean_Meta_getArrayLit_x3f(v_e_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
stack->m_obj
 = v_res_2755_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f___boxed(lean_object* v_e_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_Meta_getArrayLit_x3f(v_e_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec_ref(v_e_2756_);
return v_res_2762_;
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
