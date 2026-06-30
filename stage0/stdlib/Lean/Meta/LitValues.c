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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_getUInt8Value_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Meta_getUInt8Value_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getUInt8Value_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getUInt8Value_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getUInt8Value_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l_Lean_Meta_getUInt8Value_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getUInt8Value_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getUInt16Value_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Meta_getUInt16Value_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getUInt16Value_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getUInt16Value_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getUInt16Value_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l_Lean_Meta_getUInt16Value_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getUInt16Value_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getUInt32Value_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Meta_getUInt32Value_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getUInt32Value_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getUInt32Value_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getUInt32Value_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_Meta_getUInt32Value_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getUInt32Value_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getUInt64Value_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Meta_getUInt64Value_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getUInt64Value_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getUInt64Value_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getUInt64Value_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l_Lean_Meta_getUInt64Value_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_getUInt64Value_x3f___closed__1_value;
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
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getUInt8Value_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__10_value),LEAN_SCALAR_PTR_LITERAL(106, 22, 191, 22, 91, 53, 63, 20)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__19 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__19_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__20;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__21;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getUInt16Value_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__10_value),LEAN_SCALAR_PTR_LITERAL(100, 85, 82, 103, 43, 170, 82, 231)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__22 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__22_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__23;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__24;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getUInt32Value_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_normLitValue___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_normLitValue___closed__10_value),LEAN_SCALAR_PTR_LITERAL(112, 78, 205, 187, 174, 188, 116, 224)}};
static const lean_object* l_Lean_Meta_normLitValue___closed__25 = (const lean_object*)&l_Lean_Meta_normLitValue___closed__25_value;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__26;
static lean_once_cell_t l_Lean_Meta_normLitValue___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normLitValue___closed__27;
static const lean_ctor_object l_Lean_Meta_normLitValue___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getUInt64Value_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object* v_e_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_Lean_Meta_getUInt8Value_x3f___closed__1));
v___x_838_ = l_Lean_Meta_getOfNatValue_x3f(v_e_831_, v___x_837_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_861_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_861_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_861_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_861_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
if (lean_obj_tag(v_a_839_) == 0)
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_box(0);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v_val_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_860_; 
v_val_847_ = lean_ctor_get(v_a_839_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_a_839_);
if (v_isSharedCheck_860_ == 0)
{
v___x_849_ = v_a_839_;
v_isShared_850_ = v_isSharedCheck_860_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_val_847_);
lean_dec(v_a_839_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_860_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_fst_851_; uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v_fst_851_ = lean_ctor_get(v_val_847_, 0);
lean_inc(v_fst_851_);
lean_dec(v_val_847_);
v___x_852_ = lean_uint8_of_nat(v_fst_851_);
lean_dec(v_fst_851_);
v___x_853_ = lean_box(v___x_852_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_853_);
v___x_855_ = v___x_849_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_855_);
v___x_857_ = v___x_841_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_a_862_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_838_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_838_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f___boxed(lean_object* v_e_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Meta_getUInt8Value_x3f(v_e_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object* v_e_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_Meta_getUInt16Value_x3f___closed__1));
v___x_887_ = l_Lean_Meta_getOfNatValue_x3f(v_e_880_, v___x_886_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_910_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_910_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_910_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_910_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
if (lean_obj_tag(v_a_888_) == 0)
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_box(0);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_892_);
v___x_894_ = v___x_890_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
else
{
lean_object* v_val_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_909_; 
v_val_896_ = lean_ctor_get(v_a_888_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_909_ == 0)
{
v___x_898_ = v_a_888_;
v_isShared_899_ = v_isSharedCheck_909_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_val_896_);
lean_dec(v_a_888_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_909_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_fst_900_; uint16_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v_fst_900_ = lean_ctor_get(v_val_896_, 0);
lean_inc(v_fst_900_);
lean_dec(v_val_896_);
v___x_901_ = lean_uint16_of_nat(v_fst_900_);
lean_dec(v_fst_900_);
v___x_902_ = lean_box(v___x_901_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_902_);
v___x_904_ = v___x_898_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_908_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_906_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_904_);
v___x_906_ = v___x_890_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_911_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_887_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_887_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f___boxed(lean_object* v_e_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Meta_getUInt16Value_x3f(v_e_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object* v_e_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l_Lean_Meta_getUInt32Value_x3f___closed__1));
v___x_936_ = l_Lean_Meta_getOfNatValue_x3f(v_e_929_, v___x_935_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_959_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_959_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_959_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_959_;
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
lean_object* v_val_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_958_; 
v_val_945_ = lean_ctor_get(v_a_937_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v_a_937_);
if (v_isSharedCheck_958_ == 0)
{
v___x_947_ = v_a_937_;
v_isShared_948_ = v_isSharedCheck_958_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_val_945_);
lean_dec(v_a_937_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_958_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_fst_949_; uint32_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v_fst_949_ = lean_ctor_get(v_val_945_, 0);
lean_inc(v_fst_949_);
lean_dec(v_val_945_);
v___x_950_ = lean_uint32_of_nat(v_fst_949_);
lean_dec(v_fst_949_);
v___x_951_ = lean_box_uint32(v___x_950_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_951_);
v___x_953_ = v___x_947_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_953_);
v___x_955_ = v___x_939_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
v_a_960_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_936_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_936_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f___boxed(lean_object* v_e_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Meta_getUInt32Value_x3f(v_e_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object* v_e_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Meta_getUInt64Value_x3f___closed__1));
v___x_985_ = l_Lean_Meta_getOfNatValue_x3f(v_e_978_, v___x_984_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1008_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1008_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1008_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
if (lean_obj_tag(v_a_986_) == 0)
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = lean_box(0);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_990_);
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
else
{
lean_object* v_val_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1007_; 
v_val_994_ = lean_ctor_get(v_a_986_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_a_986_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_996_ = v_a_986_;
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_val_994_);
lean_dec(v_a_986_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_fst_998_; uint64_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v_fst_998_ = lean_ctor_get(v_val_994_, 0);
lean_inc(v_fst_998_);
lean_dec(v_val_994_);
v___x_999_ = lean_uint64_of_nat(v_fst_998_);
lean_dec(v_fst_998_);
v___x_1000_ = lean_box_uint64(v___x_999_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1000_);
v___x_1002_ = v___x_996_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_1002_);
v___x_1004_ = v___x_988_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_a_1009_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_985_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_985_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f___boxed(lean_object* v_e_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Meta_getUInt64Value_x3f(v_e_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(lean_object* v_e_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_Expr_consumeMData(v_e_1027_);
if (lean_obj_tag(v___x_1028_) == 4)
{
lean_object* v_declName_1029_; 
v_declName_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_declName_1029_);
lean_dec_ref_known(v___x_1028_, 2);
if (lean_obj_tag(v_declName_1029_) == 1)
{
lean_object* v_pre_1030_; 
v_pre_1030_ = lean_ctor_get(v_declName_1029_, 0);
lean_inc(v_pre_1030_);
if (lean_obj_tag(v_pre_1030_) == 1)
{
lean_object* v_pre_1031_; 
v_pre_1031_ = lean_ctor_get(v_pre_1030_, 0);
if (lean_obj_tag(v_pre_1031_) == 0)
{
lean_object* v_str_1032_; lean_object* v_str_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_str_1032_ = lean_ctor_get(v_declName_1029_, 1);
lean_inc_ref(v_str_1032_);
lean_dec_ref_known(v_declName_1029_, 2);
v_str_1033_ = lean_ctor_get(v_pre_1030_, 1);
lean_inc_ref(v_str_1033_);
lean_dec_ref_known(v_pre_1030_, 2);
v___x_1034_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__0));
v___x_1035_ = lean_string_dec_eq(v_str_1033_, v___x_1034_);
lean_dec_ref(v_str_1033_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
lean_dec_ref(v_str_1032_);
v___x_1036_ = lean_box(0);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__1));
v___x_1038_ = lean_string_dec_eq(v_str_1032_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___closed__2));
v___x_1040_ = lean_string_dec_eq(v_str_1032_, v___x_1039_);
lean_dec_ref(v_str_1032_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_box(0);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_box(v___x_1038_);
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec_ref(v_str_1032_);
v___x_1044_ = lean_box(v___x_1038_);
v___x_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
}
}
else
{
lean_object* v___x_1046_; 
lean_dec_ref_known(v_pre_1030_, 2);
lean_dec_ref_known(v_declName_1029_, 2);
v___x_1046_ = lean_box(0);
return v___x_1046_;
}
}
else
{
lean_object* v___x_1047_; 
lean_dec_ref_known(v_declName_1029_, 2);
lean_dec(v_pre_1030_);
v___x_1047_ = lean_box(0);
return v___x_1047_;
}
}
else
{
lean_object* v___x_1048_; 
lean_dec(v_declName_1029_);
v___x_1048_ = lean_box(0);
return v___x_1048_;
}
}
else
{
lean_object* v___x_1049_; 
lean_dec_ref(v___x_1028_);
v___x_1049_ = lean_box(0);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f___boxed(lean_object* v_e_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_e_1050_);
lean_dec_ref(v_e_1050_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(lean_object* v_e_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v___x_1066_; 
lean_inc_ref(v_e_1060_);
v___x_1066_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1060_, v_a_1062_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1106_ = l_Lean_Expr_cleanupAnnotations(v_a_1067_);
v___x_1107_ = l_Lean_Expr_isApp(v___x_1106_);
if (v___x_1107_ == 0)
{
lean_dec_ref(v___x_1106_);
v___y_1069_ = v_a_1061_;
v___y_1070_ = v_a_1062_;
v___y_1071_ = v_a_1063_;
v___y_1072_ = v_a_1064_;
goto v___jp_1068_;
}
else
{
lean_object* v_arg_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_arg_1108_ = lean_ctor_get(v___x_1106_, 1);
lean_inc_ref(v_arg_1108_);
v___x_1109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1106_);
v___x_1110_ = l_Lean_Expr_isApp(v___x_1109_);
if (v___x_1110_ == 0)
{
lean_dec_ref(v___x_1109_);
lean_dec_ref(v_arg_1108_);
v___y_1069_ = v_a_1061_;
v___y_1070_ = v_a_1062_;
v___y_1071_ = v_a_1063_;
v___y_1072_ = v_a_1064_;
goto v___jp_1068_;
}
else
{
lean_object* v_arg_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_arg_1111_ = lean_ctor_get(v___x_1109_, 1);
lean_inc_ref(v_arg_1111_);
v___x_1112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1109_);
v___x_1113_ = l_Lean_Expr_isApp(v___x_1112_);
if (v___x_1113_ == 0)
{
lean_dec_ref(v___x_1112_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1108_);
v___y_1069_ = v_a_1061_;
v___y_1070_ = v_a_1062_;
v___y_1071_ = v_a_1063_;
v___y_1072_ = v_a_1064_;
goto v___jp_1068_;
}
else
{
lean_object* v_arg_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_arg_1114_ = lean_ctor_get(v___x_1112_, 1);
lean_inc_ref(v_arg_1114_);
v___x_1115_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1112_);
v___x_1116_ = l_Lean_Expr_isApp(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1108_);
v___y_1069_ = v_a_1061_;
v___y_1070_ = v_a_1062_;
v___y_1071_ = v_a_1063_;
v___y_1072_ = v_a_1064_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1115_);
v___x_1118_ = l_Lean_Expr_isApp(v___x_1117_);
if (v___x_1118_ == 0)
{
lean_dec_ref(v___x_1117_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1108_);
v___y_1069_ = v_a_1061_;
v___y_1070_ = v_a_1062_;
v___y_1071_ = v_a_1063_;
v___y_1072_ = v_a_1064_;
goto v___jp_1068_;
}
else
{
lean_object* v_arg_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v_arg_1119_ = lean_ctor_get(v___x_1117_, 1);
lean_inc_ref(v_arg_1119_);
v___x_1120_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1117_);
v___x_1121_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__4));
v___x_1122_ = l_Lean_Expr_isConstOf(v___x_1120_, v___x_1121_);
lean_dec_ref(v___x_1120_);
if (v___x_1122_ == 0)
{
lean_dec_ref(v_arg_1119_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1108_);
v___y_1069_ = v_a_1061_;
v___y_1070_ = v_a_1062_;
v___y_1071_ = v_a_1063_;
v___y_1072_ = v_a_1064_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1123_; 
lean_dec_ref(v_e_1060_);
v___x_1123_ = l_Lean_Meta_whnfD(v_arg_1119_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1191_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1191_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1191_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1129_ = l_Lean_Expr_isConstOf(v_a_1124_, v___x_1128_);
lean_dec(v_a_1124_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1108_);
v___x_1130_ = lean_box(0);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1130_);
v___x_1132_ = v___x_1126_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_1111_);
lean_dec_ref(v_arg_1111_);
if (lean_obj_tag(v___x_1134_) == 1)
{
lean_object* v_val_1135_; lean_object* v___x_1136_; 
lean_del_object(v___x_1126_);
v_val_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_val_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1136_ = l_Lean_Meta_getNatValue_x3f(v_arg_1114_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec_ref(v_arg_1114_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1178_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1178_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1178_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
if (lean_obj_tag(v_a_1137_) == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_val_1135_);
lean_dec_ref(v_arg_1108_);
v___x_1141_ = lean_box(0);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1141_);
v___x_1143_ = v___x_1139_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
else
{
lean_object* v_val_1145_; lean_object* v___x_1146_; 
lean_del_object(v___x_1139_);
v_val_1145_ = lean_ctor_get(v_a_1137_, 0);
lean_inc(v_val_1145_);
lean_dec_ref_known(v_a_1137_, 1);
v___x_1146_ = l_Lean_Meta_getNatValue_x3f(v_arg_1108_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec_ref(v_arg_1108_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1169_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1169_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1169_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
if (lean_obj_tag(v_a_1147_) == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
lean_dec(v_val_1145_);
lean_dec(v_val_1135_);
v___x_1151_ = lean_box(0);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
else
{
lean_object* v_val_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1168_; 
v_val_1155_ = lean_ctor_get(v_a_1147_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_a_1147_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1157_ = v_a_1147_;
v_isShared_1158_ = v_isSharedCheck_1168_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_val_1155_);
lean_dec(v_a_1147_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1168_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v___x_1159_; double v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1159_ = lean_unbox(v_val_1135_);
lean_dec(v_val_1135_);
v___x_1160_ = l_Float_ofScientific(v_val_1145_, v___x_1159_, v_val_1155_);
v___x_1161_ = lean_box_float(v___x_1160_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1161_);
v___x_1163_ = v___x_1157_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1163_);
v___x_1165_ = v___x_1149_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v_val_1145_);
lean_dec(v_val_1135_);
v_a_1170_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1146_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1146_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_val_1135_);
lean_dec_ref(v_arg_1108_);
v_a_1179_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1136_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1136_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
lean_dec(v___x_1134_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1108_);
v___x_1187_ = lean_box(0);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1187_);
v___x_1189_ = v___x_1126_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1108_);
v_a_1192_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1123_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1123_);
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
}
}
}
v___jp_1068_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__1));
v___x_1074_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1060_, v___x_1073_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1097_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1097_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1097_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
if (lean_obj_tag(v_a_1075_) == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(0);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
else
{
lean_object* v_val_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1096_; 
v_val_1083_ = lean_ctor_get(v_a_1075_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_a_1075_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1085_ = v_a_1075_;
v_isShared_1086_ = v_isSharedCheck_1096_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_val_1083_);
lean_dec(v_a_1075_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1096_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v_fst_1087_; double v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v_fst_1087_ = lean_ctor_get(v_val_1083_, 0);
lean_inc(v_fst_1087_);
lean_dec(v_val_1083_);
v___x_1088_ = lean_float_of_nat(v_fst_1087_);
v___x_1089_ = lean_box_float(v___x_1088_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1089_);
v___x_1091_ = v___x_1085_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1091_);
v___x_1093_ = v___x_1077_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1074_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1074_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_e_1060_);
v_a_1200_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1066_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1066_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___boxed(lean_object* v_e_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f(lean_object* v_e_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1221_; 
lean_inc_ref(v_e_1215_);
v___x_1221_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_e_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
if (lean_obj_tag(v_a_1222_) == 1)
{
lean_dec_ref_known(v_a_1222_, 1);
lean_dec_ref(v_e_1215_);
return v___x_1221_;
}
else
{
lean_object* v___x_1223_; 
lean_dec(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1215_, v_a_1217_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1267_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1267_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1267_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = l_Lean_Expr_cleanupAnnotations(v_a_1224_);
v___x_1234_ = l_Lean_Expr_isApp(v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec_ref(v___x_1233_);
goto v___jp_1228_;
}
else
{
lean_object* v_arg_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_arg_1235_ = lean_ctor_get(v___x_1233_, 1);
lean_inc_ref(v_arg_1235_);
v___x_1236_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1233_);
v___x_1237_ = l_Lean_Expr_isApp(v___x_1236_);
if (v___x_1237_ == 0)
{
lean_dec_ref(v___x_1236_);
lean_dec_ref(v_arg_1235_);
goto v___jp_1228_;
}
else
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1236_);
v___x_1239_ = l_Lean_Expr_isApp(v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_arg_1235_);
goto v___jp_1228_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1240_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1238_);
v___x_1241_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1242_ = l_Lean_Expr_isConstOf(v___x_1240_, v___x_1241_);
lean_dec_ref(v___x_1240_);
if (v___x_1242_ == 0)
{
lean_dec_ref(v_arg_1235_);
goto v___jp_1228_;
}
else
{
lean_object* v___x_1243_; 
lean_del_object(v___x_1226_);
v___x_1243_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f(v_arg_1235_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1266_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1266_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1266_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
if (lean_obj_tag(v_a_1244_) == 1)
{
lean_object* v_val_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1261_; 
v_val_1248_ = lean_ctor_get(v_a_1244_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_a_1244_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1250_ = v_a_1244_;
v_isShared_1251_ = v_isSharedCheck_1261_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_val_1248_);
lean_dec(v_a_1244_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1261_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
double v___x_1252_; double v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1252_ = lean_unbox_float(v_val_1248_);
lean_dec(v_val_1248_);
v___x_1253_ = lean_float_negate(v___x_1252_);
v___x_1254_ = lean_box_float(v___x_1253_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1254_);
v___x_1256_ = v___x_1250_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1258_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1256_);
v___x_1258_ = v___x_1246_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
lean_dec(v_a_1244_);
v___x_1262_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1262_);
v___x_1264_ = v___x_1246_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
return v___x_1243_;
}
}
}
}
}
v___jp_1228_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = lean_box(0);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1229_);
v___x_1231_ = v___x_1226_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
v_a_1268_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1223_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1223_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1215_);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloatValue_x3f___boxed(lean_object* v_e_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_Meta_getFloatValue_x3f(v_e_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(lean_object* v_e_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v___x_1292_; 
lean_inc_ref(v_e_1286_);
v___x_1292_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1286_, v_a_1288_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1292_, 1);
v___x_1332_ = l_Lean_Expr_cleanupAnnotations(v_a_1293_);
v___x_1333_ = l_Lean_Expr_isApp(v___x_1332_);
if (v___x_1333_ == 0)
{
lean_dec_ref(v___x_1332_);
v___y_1295_ = v_a_1287_;
v___y_1296_ = v_a_1288_;
v___y_1297_ = v_a_1289_;
v___y_1298_ = v_a_1290_;
goto v___jp_1294_;
}
else
{
lean_object* v_arg_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_arg_1334_ = lean_ctor_get(v___x_1332_, 1);
lean_inc_ref(v_arg_1334_);
v___x_1335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1332_);
v___x_1336_ = l_Lean_Expr_isApp(v___x_1335_);
if (v___x_1336_ == 0)
{
lean_dec_ref(v___x_1335_);
lean_dec_ref(v_arg_1334_);
v___y_1295_ = v_a_1287_;
v___y_1296_ = v_a_1288_;
v___y_1297_ = v_a_1289_;
v___y_1298_ = v_a_1290_;
goto v___jp_1294_;
}
else
{
lean_object* v_arg_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_arg_1337_ = lean_ctor_get(v___x_1335_, 1);
lean_inc_ref(v_arg_1337_);
v___x_1338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1335_);
v___x_1339_ = l_Lean_Expr_isApp(v___x_1338_);
if (v___x_1339_ == 0)
{
lean_dec_ref(v___x_1338_);
lean_dec_ref(v_arg_1337_);
lean_dec_ref(v_arg_1334_);
v___y_1295_ = v_a_1287_;
v___y_1296_ = v_a_1288_;
v___y_1297_ = v_a_1289_;
v___y_1298_ = v_a_1290_;
goto v___jp_1294_;
}
else
{
lean_object* v_arg_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_arg_1340_ = lean_ctor_get(v___x_1338_, 1);
lean_inc_ref(v_arg_1340_);
v___x_1341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1338_);
v___x_1342_ = l_Lean_Expr_isApp(v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec_ref(v___x_1341_);
lean_dec_ref(v_arg_1340_);
lean_dec_ref(v_arg_1337_);
lean_dec_ref(v_arg_1334_);
v___y_1295_ = v_a_1287_;
v___y_1296_ = v_a_1288_;
v___y_1297_ = v_a_1289_;
v___y_1298_ = v_a_1290_;
goto v___jp_1294_;
}
else
{
lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1341_);
v___x_1344_ = l_Lean_Expr_isApp(v___x_1343_);
if (v___x_1344_ == 0)
{
lean_dec_ref(v___x_1343_);
lean_dec_ref(v_arg_1340_);
lean_dec_ref(v_arg_1337_);
lean_dec_ref(v_arg_1334_);
v___y_1295_ = v_a_1287_;
v___y_1296_ = v_a_1288_;
v___y_1297_ = v_a_1289_;
v___y_1298_ = v_a_1290_;
goto v___jp_1294_;
}
else
{
lean_object* v_arg_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_arg_1345_ = lean_ctor_get(v___x_1343_, 1);
lean_inc_ref(v_arg_1345_);
v___x_1346_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1343_);
v___x_1347_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloatLit_x3f___closed__4));
v___x_1348_ = l_Lean_Expr_isConstOf(v___x_1346_, v___x_1347_);
lean_dec_ref(v___x_1346_);
if (v___x_1348_ == 0)
{
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1340_);
lean_dec_ref(v_arg_1337_);
lean_dec_ref(v_arg_1334_);
v___y_1295_ = v_a_1287_;
v___y_1296_ = v_a_1288_;
v___y_1297_ = v_a_1289_;
v___y_1298_ = v_a_1290_;
goto v___jp_1294_;
}
else
{
lean_object* v___x_1349_; 
lean_dec_ref(v_e_1286_);
v___x_1349_ = l_Lean_Meta_whnfD(v_arg_1345_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1417_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1417_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1417_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_1355_ = l_Lean_Expr_isConstOf(v_a_1350_, v___x_1354_);
lean_dec(v_a_1350_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_dec_ref(v_arg_1340_);
lean_dec_ref(v_arg_1337_);
lean_dec_ref(v_arg_1334_);
v___x_1356_ = lean_box(0);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1356_);
v___x_1358_ = v___x_1352_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
else
{
lean_object* v___x_1360_; 
v___x_1360_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getBoolLit_x3f(v_arg_1337_);
lean_dec_ref(v_arg_1337_);
if (lean_obj_tag(v___x_1360_) == 1)
{
lean_object* v_val_1361_; lean_object* v___x_1362_; 
lean_del_object(v___x_1352_);
v_val_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_val_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1362_ = l_Lean_Meta_getNatValue_x3f(v_arg_1340_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec_ref(v_arg_1340_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1404_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1404_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1404_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
if (lean_obj_tag(v_a_1363_) == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
lean_dec(v_val_1361_);
lean_dec_ref(v_arg_1334_);
v___x_1367_ = lean_box(0);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1367_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
else
{
lean_object* v_val_1371_; lean_object* v___x_1372_; 
lean_del_object(v___x_1365_);
v_val_1371_ = lean_ctor_get(v_a_1363_, 0);
lean_inc(v_val_1371_);
lean_dec_ref_known(v_a_1363_, 1);
v___x_1372_ = l_Lean_Meta_getNatValue_x3f(v_arg_1334_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec_ref(v_arg_1334_);
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
lean_dec(v_val_1371_);
lean_dec(v_val_1361_);
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
uint8_t v___x_1385_; float v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1385_ = lean_unbox(v_val_1361_);
lean_dec(v_val_1361_);
v___x_1386_ = l_Float32_ofScientific(v_val_1371_, v___x_1385_, v_val_1381_);
v___x_1387_ = lean_box_float32(v___x_1386_);
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
lean_dec(v_val_1371_);
lean_dec(v_val_1361_);
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
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_val_1361_);
lean_dec_ref(v_arg_1334_);
v_a_1405_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1362_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1362_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
lean_dec(v___x_1360_);
lean_dec_ref(v_arg_1340_);
lean_dec_ref(v_arg_1334_);
v___x_1413_ = lean_box(0);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1413_);
v___x_1415_ = v___x_1352_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v_arg_1340_);
lean_dec_ref(v_arg_1337_);
lean_dec_ref(v_arg_1334_);
v_a_1418_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1349_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1349_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
}
}
}
v___jp_1294_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___closed__1));
v___x_1300_ = l_Lean_Meta_getOfNatValue_x3f(v_e_1286_, v___x_1299_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1323_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1323_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1323_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
if (lean_obj_tag(v_a_1301_) == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = lean_box(0);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1305_);
v___x_1307_ = v___x_1303_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
else
{
lean_object* v_val_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1322_; 
v_val_1309_ = lean_ctor_get(v_a_1301_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_a_1301_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1311_ = v_a_1301_;
v_isShared_1312_ = v_isSharedCheck_1322_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_val_1309_);
lean_dec(v_a_1301_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1322_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_fst_1313_; float v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v_fst_1313_ = lean_ctor_get(v_val_1309_, 0);
lean_inc(v_fst_1313_);
lean_dec(v_val_1309_);
v___x_1314_ = lean_float32_of_nat(v_fst_1313_);
v___x_1315_ = lean_box_float32(v___x_1314_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1315_);
v___x_1317_ = v___x_1311_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1319_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1317_);
v___x_1319_ = v___x_1303_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
v_a_1324_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1300_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1300_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec_ref(v_e_1286_);
v_a_1426_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1292_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1292_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f___boxed(lean_object* v_e_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f(lean_object* v_e_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v___x_1447_; 
lean_inc_ref(v_e_1441_);
v___x_1447_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_e_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
if (lean_obj_tag(v_a_1448_) == 1)
{
lean_dec_ref_known(v_a_1448_, 1);
lean_dec_ref(v_e_1441_);
return v___x_1447_;
}
else
{
lean_object* v___x_1449_; 
lean_dec(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1441_, v_a_1443_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1493_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1493_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1493_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = l_Lean_Expr_cleanupAnnotations(v_a_1450_);
v___x_1460_ = l_Lean_Expr_isApp(v___x_1459_);
if (v___x_1460_ == 0)
{
lean_dec_ref(v___x_1459_);
goto v___jp_1454_;
}
else
{
lean_object* v_arg_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_arg_1461_ = lean_ctor_get(v___x_1459_, 1);
lean_inc_ref(v_arg_1461_);
v___x_1462_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1459_);
v___x_1463_ = l_Lean_Expr_isApp(v___x_1462_);
if (v___x_1463_ == 0)
{
lean_dec_ref(v___x_1462_);
lean_dec_ref(v_arg_1461_);
goto v___jp_1454_;
}
else
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1462_);
v___x_1465_ = l_Lean_Expr_isApp(v___x_1464_);
if (v___x_1465_ == 0)
{
lean_dec_ref(v___x_1464_);
lean_dec_ref(v_arg_1461_);
goto v___jp_1454_;
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1464_);
v___x_1467_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1468_ = l_Lean_Expr_isConstOf(v___x_1466_, v___x_1467_);
lean_dec_ref(v___x_1466_);
if (v___x_1468_ == 0)
{
lean_dec_ref(v_arg_1461_);
goto v___jp_1454_;
}
else
{
lean_object* v___x_1469_; 
lean_del_object(v___x_1452_);
v___x_1469_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getFloat32Lit_x3f(v_arg_1461_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1492_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1492_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1492_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
if (lean_obj_tag(v_a_1470_) == 1)
{
lean_object* v_val_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1487_; 
v_val_1474_ = lean_ctor_get(v_a_1470_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_a_1470_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1476_ = v_a_1470_;
v_isShared_1477_ = v_isSharedCheck_1487_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_val_1474_);
lean_dec(v_a_1470_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1487_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
float v___x_1478_; float v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1478_ = lean_unbox_float32(v_val_1474_);
lean_dec(v_val_1474_);
v___x_1479_ = lean_float32_negate(v___x_1478_);
v___x_1480_ = lean_box_float32(v___x_1479_);
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
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1482_);
v___x_1484_ = v___x_1472_;
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
else
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
lean_dec(v_a_1470_);
v___x_1488_ = lean_box(0);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1488_);
v___x_1490_ = v___x_1472_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
return v___x_1469_;
}
}
}
}
}
v___jp_1454_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_box(0);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1455_);
v___x_1457_ = v___x_1452_;
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
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
v_a_1494_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1449_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1449_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1441_);
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFloat32Value_x3f___boxed(lean_object* v_e_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_Meta_getFloat32Value_x3f(v_e_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(lean_object* v_e_1509_, lean_object* v___y_1510_){
_start:
{
uint8_t v___x_1512_; 
v___x_1512_ = l_Lean_Expr_hasMVar(v_e_1509_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_e_1509_);
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; lean_object* v_mctx_1515_; lean_object* v___x_1516_; lean_object* v_fst_1517_; lean_object* v_snd_1518_; lean_object* v___x_1519_; lean_object* v_cache_1520_; lean_object* v_zetaDeltaFVarIds_1521_; lean_object* v_postponed_1522_; lean_object* v_diag_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1532_; 
v___x_1514_ = lean_st_ref_get(v___y_1510_);
v_mctx_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc_ref(v_mctx_1515_);
lean_dec(v___x_1514_);
v___x_1516_ = l_Lean_instantiateMVarsCore(v_mctx_1515_, v_e_1509_);
v_fst_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_fst_1517_);
v_snd_1518_ = lean_ctor_get(v___x_1516_, 1);
lean_inc(v_snd_1518_);
lean_dec_ref(v___x_1516_);
v___x_1519_ = lean_st_ref_take(v___y_1510_);
v_cache_1520_ = lean_ctor_get(v___x_1519_, 1);
v_zetaDeltaFVarIds_1521_ = lean_ctor_get(v___x_1519_, 2);
v_postponed_1522_ = lean_ctor_get(v___x_1519_, 3);
v_diag_1523_ = lean_ctor_get(v___x_1519_, 4);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v___x_1519_, 0);
lean_dec(v_unused_1533_);
v___x_1525_ = v___x_1519_;
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_diag_1523_);
lean_inc(v_postponed_1522_);
lean_inc(v_zetaDeltaFVarIds_1521_);
lean_inc(v_cache_1520_);
lean_dec(v___x_1519_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v_snd_1518_);
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_snd_1518_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_cache_1520_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_zetaDeltaFVarIds_1521_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_postponed_1522_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_diag_1523_);
v___x_1528_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_st_ref_set(v___y_1510_, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_fst_1517_);
return v___x_1530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg___boxed(lean_object* v_e_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1534_, v___y_1535_);
lean_dec(v___y_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(lean_object* v_e_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1538_, v___y_1540_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___boxed(lean_object* v_e_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(v_e_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1551_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__0(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = lean_nat_to_int(v___x_1552_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__1(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_unsigned_to_nat(0u);
v___x_1555_ = l_Lean_Level_ofNat(v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__2(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__1, &l_Lean_Meta_normLitValue___closed__1_once, _init_l_Lean_Meta_normLitValue___closed__1);
v___x_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v___x_1556_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__3(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_1560_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1561_ = l_Lean_Expr_const___override(v___x_1560_, v___x_1559_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__4(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_1564_ = l_Lean_Expr_const___override(v___x_1563_, v___x_1562_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__7(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_box(0);
v___x_1570_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__6));
v___x_1571_ = l_Lean_Expr_const___override(v___x_1570_, v___x_1569_);
return v___x_1571_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__8(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1572_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_1573_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_1574_ = l_Lean_Expr_const___override(v___x_1573_, v___x_1572_);
return v___x_1574_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__9(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = lean_box(0);
v___x_1576_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_1577_ = l_Lean_mkConst(v___x_1576_, v___x_1575_);
return v___x_1577_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__12(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = lean_box(0);
v___x_1583_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__11));
v___x_1584_ = l_Lean_Expr_const___override(v___x_1583_, v___x_1582_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__15(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = lean_box(0);
v___x_1590_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__14));
v___x_1591_ = l_Lean_Expr_const___override(v___x_1590_, v___x_1589_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__16(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = lean_box(0);
v___x_1593_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_1594_ = l_Lean_Expr_const___override(v___x_1593_, v___x_1592_);
return v___x_1594_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__17(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = lean_box(0);
v___x_1596_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_1597_ = l_Lean_mkConst(v___x_1596_, v___x_1595_);
return v___x_1597_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__18(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = lean_box(0);
v___x_1599_ = ((lean_object*)(l_Lean_Meta_getUInt8Value_x3f___closed__1));
v___x_1600_ = l_Lean_mkConst(v___x_1599_, v___x_1598_);
return v___x_1600_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__20(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = lean_box(0);
v___x_1605_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__19));
v___x_1606_ = l_Lean_Expr_const___override(v___x_1605_, v___x_1604_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__21(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = lean_box(0);
v___x_1608_ = ((lean_object*)(l_Lean_Meta_getUInt16Value_x3f___closed__1));
v___x_1609_ = l_Lean_mkConst(v___x_1608_, v___x_1607_);
return v___x_1609_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__23(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = lean_box(0);
v___x_1614_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__22));
v___x_1615_ = l_Lean_Expr_const___override(v___x_1614_, v___x_1613_);
return v___x_1615_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__24(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_box(0);
v___x_1617_ = ((lean_object*)(l_Lean_Meta_getUInt32Value_x3f___closed__1));
v___x_1618_ = l_Lean_mkConst(v___x_1617_, v___x_1616_);
return v___x_1618_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__26(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = lean_box(0);
v___x_1623_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__25));
v___x_1624_ = l_Lean_Expr_const___override(v___x_1623_, v___x_1622_);
return v___x_1624_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__27(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = lean_box(0);
v___x_1626_ = ((lean_object*)(l_Lean_Meta_getUInt64Value_x3f___closed__1));
v___x_1627_ = l_Lean_mkConst(v___x_1626_, v___x_1625_);
return v___x_1627_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__29(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = lean_box(0);
v___x_1632_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__28));
v___x_1633_ = l_Lean_Expr_const___override(v___x_1632_, v___x_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue(lean_object* v_e_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v_a_1641_; lean_object* v___x_1642_; 
v___x_1640_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1634_, v_a_1636_);
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref(v___x_1640_);
v___x_1642_ = l_Lean_Meta_getNatValue_x3f(v_a_1641_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1877_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1877_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1877_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
if (lean_obj_tag(v_a_1643_) == 1)
{
lean_object* v_val_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
lean_dec(v_a_1641_);
v_val_1647_ = lean_ctor_get(v_a_1643_, 0);
lean_inc(v_val_1647_);
lean_dec_ref_known(v_a_1643_, 1);
v___x_1648_ = l_Lean_mkNatLit(v_val_1647_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1648_);
v___x_1650_ = v___x_1645_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
else
{
lean_object* v___x_1652_; 
lean_del_object(v___x_1645_);
lean_dec(v_a_1643_);
lean_inc(v_a_1641_);
v___x_1652_ = l_Lean_Meta_getIntValue_x3f(v_a_1641_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1868_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1868_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1868_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
if (lean_obj_tag(v_a_1653_) == 1)
{
lean_object* v_val_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
lean_dec(v_a_1641_);
v_val_1657_ = lean_ctor_get(v_a_1653_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v_a_1653_, 1);
v___x_1658_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_1659_ = lean_int_dec_le(v___x_1658_, v_val_1657_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1660_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_1661_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__4, &l_Lean_Meta_normLitValue___closed__4_once, _init_l_Lean_Meta_normLitValue___closed__4);
v___x_1662_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__7, &l_Lean_Meta_normLitValue___closed__7_once, _init_l_Lean_Meta_normLitValue___closed__7);
v___x_1663_ = lean_int_neg(v_val_1657_);
lean_dec(v_val_1657_);
v___x_1664_ = l_Int_toNat(v___x_1663_);
lean_dec(v___x_1663_);
v___x_1665_ = l_Lean_instToExprInt_mkNat(v___x_1664_);
v___x_1666_ = l_Lean_mkApp3(v___x_1660_, v___x_1661_, v___x_1662_, v___x_1665_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1666_);
v___x_1668_ = v___x_1655_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1670_ = l_Int_toNat(v_val_1657_);
lean_dec(v_val_1657_);
v___x_1671_ = l_Lean_instToExprInt_mkNat(v___x_1670_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1671_);
v___x_1673_ = v___x_1655_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
else
{
lean_object* v___x_1675_; 
lean_del_object(v___x_1655_);
lean_dec(v_a_1653_);
lean_inc(v_a_1641_);
v___x_1675_ = l_Lean_Meta_getFinValue_x3f(v_a_1641_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1859_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1859_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1859_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
if (lean_obj_tag(v_a_1676_) == 1)
{
lean_object* v_val_1680_; lean_object* v_fst_1681_; lean_object* v_snd_1682_; lean_object* v_r_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
lean_dec(v_a_1641_);
v_val_1680_ = lean_ctor_get(v_a_1676_, 0);
lean_inc(v_val_1680_);
lean_dec_ref_known(v_a_1676_, 1);
v_fst_1681_ = lean_ctor_get(v_val_1680_, 0);
lean_inc_n(v_fst_1681_, 2);
v_snd_1682_ = lean_ctor_get(v_val_1680_, 1);
lean_inc(v_snd_1682_);
lean_dec(v_val_1680_);
v_r_1683_ = l_Lean_mkRawNatLit(v_snd_1682_);
v___x_1684_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1685_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__9, &l_Lean_Meta_normLitValue___closed__9_once, _init_l_Lean_Meta_normLitValue___closed__9);
v___x_1686_ = l_Lean_mkNatLit(v_fst_1681_);
lean_inc_ref(v___x_1686_);
v___x_1687_ = l_Lean_Expr_app___override(v___x_1685_, v___x_1686_);
v___x_1688_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__12, &l_Lean_Meta_normLitValue___closed__12_once, _init_l_Lean_Meta_normLitValue___closed__12);
v___x_1689_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__15, &l_Lean_Meta_normLitValue___closed__15_once, _init_l_Lean_Meta_normLitValue___closed__15);
v___x_1690_ = lean_unsigned_to_nat(1u);
v___x_1691_ = lean_nat_sub(v_fst_1681_, v___x_1690_);
lean_dec(v_fst_1681_);
v___x_1692_ = l_Lean_mkNatLit(v___x_1691_);
v___x_1693_ = l_Lean_Expr_app___override(v___x_1689_, v___x_1692_);
lean_inc_ref(v_r_1683_);
v___x_1694_ = l_Lean_mkApp3(v___x_1688_, v___x_1686_, v___x_1693_, v_r_1683_);
v___x_1695_ = l_Lean_mkApp3(v___x_1684_, v___x_1687_, v_r_1683_, v___x_1694_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1695_);
v___x_1697_ = v___x_1678_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
lean_object* v___x_1699_; 
lean_del_object(v___x_1678_);
lean_dec(v_a_1676_);
lean_inc(v_a_1641_);
v___x_1699_ = l_Lean_Meta_getBitVecValue_x3f(v_a_1641_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1850_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1850_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1850_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
if (lean_obj_tag(v_a_1700_) == 1)
{
lean_object* v_val_1704_; lean_object* v_fst_1705_; lean_object* v_snd_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_dec(v_a_1641_);
v_val_1704_ = lean_ctor_get(v_a_1700_, 0);
lean_inc(v_val_1704_);
lean_dec_ref_known(v_a_1700_, 1);
v_fst_1705_ = lean_ctor_get(v_val_1704_, 0);
lean_inc(v_fst_1705_);
v_snd_1706_ = lean_ctor_get(v_val_1704_, 1);
lean_inc(v_snd_1706_);
lean_dec(v_val_1704_);
v___x_1707_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__16, &l_Lean_Meta_normLitValue___closed__16_once, _init_l_Lean_Meta_normLitValue___closed__16);
v___x_1708_ = l_Lean_mkNatLit(v_fst_1705_);
v___x_1709_ = l_Lean_mkNatLit(v_snd_1706_);
v___x_1710_ = l_Lean_mkAppB(v___x_1707_, v___x_1708_, v___x_1709_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1710_);
v___x_1712_ = v___x_1702_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
else
{
lean_object* v___x_1714_; 
lean_dec(v_a_1700_);
lean_inc(v_a_1641_);
v___x_1714_ = l_Lean_Meta_getStringValue_x3f(v_a_1641_);
if (lean_obj_tag(v___x_1714_) == 1)
{
lean_object* v_val_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
lean_dec(v_a_1641_);
v_val_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_val_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v___x_1716_ = l_Lean_mkStrLit(v_val_1715_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1716_);
v___x_1718_ = v___x_1702_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
else
{
lean_object* v___x_1720_; 
lean_dec(v___x_1714_);
lean_del_object(v___x_1702_);
lean_inc(v_a_1641_);
v___x_1720_ = l_Lean_Meta_getCharValue_x3f(v_a_1641_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1841_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1841_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1841_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
if (lean_obj_tag(v_a_1721_) == 1)
{
lean_object* v_val_1725_; lean_object* v___x_1726_; uint32_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
lean_dec(v_a_1641_);
v_val_1725_ = lean_ctor_get(v_a_1721_, 0);
lean_inc(v_val_1725_);
lean_dec_ref_known(v_a_1721_, 1);
v___x_1726_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__17, &l_Lean_Meta_normLitValue___closed__17_once, _init_l_Lean_Meta_normLitValue___closed__17);
v___x_1727_ = lean_unbox_uint32(v_val_1725_);
lean_dec(v_val_1725_);
v___x_1728_ = lean_uint32_to_nat(v___x_1727_);
v___x_1729_ = l_Lean_mkRawNatLit(v___x_1728_);
v___x_1730_ = l_Lean_Expr_app___override(v___x_1726_, v___x_1729_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1730_);
v___x_1732_ = v___x_1723_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
else
{
lean_object* v___x_1734_; 
lean_del_object(v___x_1723_);
lean_dec(v_a_1721_);
lean_inc(v_a_1641_);
v___x_1734_ = l_Lean_Meta_getUInt8Value_x3f(v_a_1641_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1832_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1832_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1832_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
if (lean_obj_tag(v_a_1735_) == 1)
{
lean_object* v_val_1739_; uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v_r_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_dec(v_a_1641_);
v_val_1739_ = lean_ctor_get(v_a_1735_, 0);
lean_inc(v_val_1739_);
lean_dec_ref_known(v_a_1735_, 1);
v___x_1740_ = lean_unbox(v_val_1739_);
lean_dec(v_val_1739_);
v___x_1741_ = lean_uint8_to_nat(v___x_1740_);
v_r_1742_ = l_Lean_mkRawNatLit(v___x_1741_);
v___x_1743_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1744_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__18, &l_Lean_Meta_normLitValue___closed__18_once, _init_l_Lean_Meta_normLitValue___closed__18);
v___x_1745_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__20, &l_Lean_Meta_normLitValue___closed__20_once, _init_l_Lean_Meta_normLitValue___closed__20);
lean_inc_ref(v_r_1742_);
v___x_1746_ = l_Lean_Expr_app___override(v___x_1745_, v_r_1742_);
v___x_1747_ = l_Lean_mkApp3(v___x_1743_, v___x_1744_, v_r_1742_, v___x_1746_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1747_);
v___x_1749_ = v___x_1737_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
else
{
lean_object* v___x_1751_; 
lean_del_object(v___x_1737_);
lean_dec(v_a_1735_);
lean_inc(v_a_1641_);
v___x_1751_ = l_Lean_Meta_getUInt16Value_x3f(v_a_1641_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1823_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1823_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1823_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
if (lean_obj_tag(v_a_1752_) == 1)
{
lean_object* v_val_1756_; uint16_t v___x_1757_; lean_object* v___x_1758_; lean_object* v_r_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_dec(v_a_1641_);
v_val_1756_ = lean_ctor_get(v_a_1752_, 0);
lean_inc(v_val_1756_);
lean_dec_ref_known(v_a_1752_, 1);
v___x_1757_ = lean_unbox(v_val_1756_);
lean_dec(v_val_1756_);
v___x_1758_ = lean_uint16_to_nat(v___x_1757_);
v_r_1759_ = l_Lean_mkRawNatLit(v___x_1758_);
v___x_1760_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1761_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__21, &l_Lean_Meta_normLitValue___closed__21_once, _init_l_Lean_Meta_normLitValue___closed__21);
v___x_1762_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__23, &l_Lean_Meta_normLitValue___closed__23_once, _init_l_Lean_Meta_normLitValue___closed__23);
lean_inc_ref(v_r_1759_);
v___x_1763_ = l_Lean_Expr_app___override(v___x_1762_, v_r_1759_);
v___x_1764_ = l_Lean_mkApp3(v___x_1760_, v___x_1761_, v_r_1759_, v___x_1763_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1764_);
v___x_1766_ = v___x_1754_;
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
else
{
lean_object* v___x_1768_; 
lean_del_object(v___x_1754_);
lean_dec(v_a_1752_);
lean_inc(v_a_1641_);
v___x_1768_ = l_Lean_Meta_getUInt32Value_x3f(v_a_1641_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1814_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1814_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1814_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
if (lean_obj_tag(v_a_1769_) == 1)
{
lean_object* v_val_1773_; uint32_t v___x_1774_; lean_object* v___x_1775_; lean_object* v_r_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
lean_dec(v_a_1641_);
v_val_1773_ = lean_ctor_get(v_a_1769_, 0);
lean_inc(v_val_1773_);
lean_dec_ref_known(v_a_1769_, 1);
v___x_1774_ = lean_unbox_uint32(v_val_1773_);
lean_dec(v_val_1773_);
v___x_1775_ = lean_uint32_to_nat(v___x_1774_);
v_r_1776_ = l_Lean_mkRawNatLit(v___x_1775_);
v___x_1777_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1778_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__24, &l_Lean_Meta_normLitValue___closed__24_once, _init_l_Lean_Meta_normLitValue___closed__24);
v___x_1779_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__26, &l_Lean_Meta_normLitValue___closed__26_once, _init_l_Lean_Meta_normLitValue___closed__26);
lean_inc_ref(v_r_1776_);
v___x_1780_ = l_Lean_Expr_app___override(v___x_1779_, v_r_1776_);
v___x_1781_ = l_Lean_mkApp3(v___x_1777_, v___x_1778_, v_r_1776_, v___x_1780_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1781_);
v___x_1783_ = v___x_1771_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
else
{
lean_object* v___x_1785_; 
lean_del_object(v___x_1771_);
lean_dec(v_a_1769_);
lean_inc(v_a_1641_);
v___x_1785_ = l_Lean_Meta_getUInt64Value_x3f(v_a_1641_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1805_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1805_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1805_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
if (lean_obj_tag(v_a_1786_) == 1)
{
lean_object* v_val_1790_; uint64_t v___x_1791_; lean_object* v___x_1792_; lean_object* v_r_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
lean_dec(v_a_1641_);
v_val_1790_ = lean_ctor_get(v_a_1786_, 0);
lean_inc(v_val_1790_);
lean_dec_ref_known(v_a_1786_, 1);
v___x_1791_ = lean_unbox_uint64(v_val_1790_);
lean_dec(v_val_1790_);
v___x_1792_ = lean_uint64_to_nat(v___x_1791_);
v_r_1793_ = l_Lean_mkRawNatLit(v___x_1792_);
v___x_1794_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1795_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__27, &l_Lean_Meta_normLitValue___closed__27_once, _init_l_Lean_Meta_normLitValue___closed__27);
v___x_1796_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__29, &l_Lean_Meta_normLitValue___closed__29_once, _init_l_Lean_Meta_normLitValue___closed__29);
lean_inc_ref(v_r_1793_);
v___x_1797_ = l_Lean_Expr_app___override(v___x_1796_, v_r_1793_);
v___x_1798_ = l_Lean_mkApp3(v___x_1794_, v___x_1795_, v_r_1793_, v___x_1797_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1798_);
v___x_1800_ = v___x_1788_;
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
else
{
lean_object* v___x_1803_; 
lean_dec(v_a_1786_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v_a_1641_);
v___x_1803_ = v___x_1788_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1641_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_a_1641_);
v_a_1806_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1785_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1785_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec(v_a_1641_);
v_a_1815_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1768_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1768_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
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
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v_a_1641_);
v_a_1824_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1751_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1751_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec(v_a_1641_);
v_a_1833_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1734_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1734_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec(v_a_1641_);
v_a_1842_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1720_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1720_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_a_1641_);
v_a_1851_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1699_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1699_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_a_1641_);
v_a_1860_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1675_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1675_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1641_);
v_a_1869_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1652_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1652_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1641_);
v_a_1878_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1642_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1642_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue___boxed(lean_object* v_e_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_Meta_normLitValue(v_e_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue(lean_object* v_e_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v_a_1900_; lean_object* v___x_1901_; 
v___x_1899_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1893_, v_a_1895_);
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
v___x_1901_ = l_Lean_Meta_getNatValue_x3f(v_a_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_2102_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_2102_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_2102_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
if (lean_obj_tag(v_a_1902_) == 0)
{
lean_object* v___x_1906_; 
lean_del_object(v___x_1904_);
lean_inc(v_a_1900_);
v___x_1906_ = l_Lean_Meta_getIntValue_x3f(v_a_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_2088_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_2088_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_2088_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
uint8_t v___x_1911_; 
v___x_1911_ = 1;
if (lean_obj_tag(v_a_1907_) == 0)
{
lean_object* v___x_1912_; 
lean_del_object(v___x_1909_);
lean_inc(v_a_1900_);
v___x_1912_ = l_Lean_Meta_getFinValue_x3f(v_a_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_2075_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_2075_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_2075_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
if (lean_obj_tag(v_a_1913_) == 0)
{
lean_object* v___x_1917_; 
lean_del_object(v___x_1915_);
lean_inc(v_a_1900_);
v___x_1917_ = l_Lean_Meta_getBitVecValue_x3f(v_a_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_2062_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_2062_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_2062_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
if (lean_obj_tag(v_a_1918_) == 0)
{
lean_object* v___x_1922_; 
lean_inc(v_a_1900_);
v___x_1922_ = l_Lean_Meta_getStringValue_x3f(v_a_1900_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v___x_1923_; 
lean_del_object(v___x_1920_);
lean_inc(v_a_1900_);
v___x_1923_ = l_Lean_Meta_getCharValue_x3f(v_a_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_2045_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_2045_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_2045_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
if (lean_obj_tag(v_a_1924_) == 0)
{
lean_object* v___x_1928_; 
lean_del_object(v___x_1926_);
lean_inc(v_a_1900_);
v___x_1928_ = l_Lean_Meta_getUInt8Value_x3f(v_a_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_2032_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_2032_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_2032_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
if (lean_obj_tag(v_a_1929_) == 0)
{
lean_object* v___x_1933_; 
lean_del_object(v___x_1931_);
lean_inc(v_a_1900_);
v___x_1933_ = l_Lean_Meta_getUInt16Value_x3f(v_a_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_2019_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_2019_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_2019_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
if (lean_obj_tag(v_a_1934_) == 0)
{
lean_object* v___x_1938_; 
lean_del_object(v___x_1936_);
lean_inc(v_a_1900_);
v___x_1938_ = l_Lean_Meta_getUInt32Value_x3f(v_a_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_2006_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_2006_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_2006_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
if (lean_obj_tag(v_a_1939_) == 0)
{
lean_object* v___x_1943_; 
lean_del_object(v___x_1941_);
lean_inc(v_a_1900_);
v___x_1943_ = l_Lean_Meta_getUInt64Value_x3f(v_a_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1993_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_1993_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1993_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
if (lean_obj_tag(v_a_1944_) == 0)
{
lean_object* v___x_1948_; 
lean_del_object(v___x_1946_);
lean_inc(v_a_1900_);
v___x_1948_ = l_Lean_Meta_getFloatValue_x3f(v_a_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1980_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1980_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1980_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
if (lean_obj_tag(v_a_1949_) == 0)
{
lean_object* v___x_1953_; 
lean_del_object(v___x_1951_);
v___x_1953_ = l_Lean_Meta_getFloat32Value_x3f(v_a_1900_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1967_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1956_ = v___x_1953_;
v_isShared_1957_ = v_isSharedCheck_1967_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1967_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
if (lean_obj_tag(v_a_1954_) == 0)
{
uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1958_ = 0;
v___x_1959_ = lean_box(v___x_1958_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1959_);
v___x_1961_ = v___x_1956_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
lean_dec_ref_known(v_a_1954_, 1);
v___x_1963_ = lean_box(v___x_1911_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1963_);
v___x_1965_ = v___x_1956_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
v_a_1968_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1953_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1953_);
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
else
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
lean_dec_ref_known(v_a_1949_, 1);
lean_dec(v_a_1900_);
v___x_1976_ = lean_box(v___x_1911_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1976_);
v___x_1978_ = v___x_1951_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
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
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v_a_1900_);
v_a_1981_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1948_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1948_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_dec_ref_known(v_a_1944_, 1);
lean_dec(v_a_1900_);
v___x_1989_ = lean_box(v___x_1911_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1989_);
v___x_1991_ = v___x_1946_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v_a_1900_);
v_a_1994_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1943_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1943_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
lean_dec_ref_known(v_a_1939_, 1);
lean_dec(v_a_1900_);
v___x_2002_ = lean_box(v___x_1911_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_2002_);
v___x_2004_ = v___x_1941_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v_a_1900_);
v_a_2007_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1938_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1938_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
lean_dec_ref_known(v_a_1934_, 1);
lean_dec(v_a_1900_);
v___x_2015_ = lean_box(v___x_1911_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_2015_);
v___x_2017_ = v___x_1936_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_a_1900_);
v_a_2020_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1933_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1933_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
lean_dec_ref_known(v_a_1929_, 1);
lean_dec(v_a_1900_);
v___x_2028_ = lean_box(v___x_1911_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_2028_);
v___x_2030_ = v___x_1931_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_a_1900_);
v_a_2033_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_1928_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_1928_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2043_; 
lean_dec_ref_known(v_a_1924_, 1);
lean_dec(v_a_1900_);
v___x_2041_ = lean_box(v___x_1911_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_2041_);
v___x_2043_ = v___x_1926_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2041_);
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
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_a_1900_);
v_a_2046_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_1923_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_1923_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
lean_dec_ref_known(v___x_1922_, 1);
lean_dec(v_a_1900_);
v___x_2054_ = lean_box(v___x_1911_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_2054_);
v___x_2056_ = v___x_1920_;
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
else
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
lean_dec_ref_known(v_a_1918_, 1);
lean_dec(v_a_1900_);
v___x_2058_ = lean_box(v___x_1911_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_2058_);
v___x_2060_ = v___x_1920_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_a_1900_);
v_a_2063_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_1917_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_1917_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_dec_ref_known(v_a_1913_, 1);
lean_dec(v_a_1900_);
v___x_2071_ = lean_box(v___x_1911_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_2071_);
v___x_2073_ = v___x_1915_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_a_1900_);
v_a_2076_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_1912_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_1912_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
lean_dec_ref_known(v_a_1907_, 1);
lean_dec(v_a_1900_);
v___x_2084_ = lean_box(v___x_1911_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_2084_);
v___x_2086_ = v___x_1909_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
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
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_a_1900_);
v_a_2089_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_1906_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_1906_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
uint8_t v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
lean_dec_ref_known(v_a_1902_, 1);
lean_dec(v_a_1900_);
v___x_2097_ = 1;
v___x_2098_ = lean_box(v___x_2097_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_2098_);
v___x_2100_ = v___x_1904_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec(v_a_1900_);
v_a_2103_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_1901_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_1901_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue___boxed(lean_object* v_e_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_Meta_isLitValue(v_e_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
return v_res_2117_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__2(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = lean_box(0);
v___x_2123_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__1));
v___x_2124_ = l_Lean_mkConst(v___x_2123_, v___x_2122_);
return v___x_2124_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__5(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = lean_box(0);
v___x_2130_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__4));
v___x_2131_ = l_Lean_mkConst(v___x_2130_, v___x_2129_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__7(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = lean_box(0);
v___x_2136_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__6));
v___x_2137_ = l_Lean_mkConst(v___x_2136_, v___x_2135_);
return v___x_2137_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__10(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = lean_box(0);
v___x_2143_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__9));
v___x_2144_ = l_Lean_mkConst(v___x_2143_, v___x_2142_);
return v___x_2144_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__11(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_to_int(v___x_2145_);
return v___x_2146_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__15(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_2153_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__14));
v___x_2154_ = l_Lean_mkConst(v___x_2153_, v___x_2152_);
return v___x_2154_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__16(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_2157_ = l_Lean_mkConst(v___x_2156_, v___x_2155_);
return v___x_2157_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__19(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_box(0);
v___x_2162_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__18));
v___x_2163_ = l_Lean_mkConst(v___x_2162_, v___x_2161_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__22(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_box(0);
v___x_2168_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__21));
v___x_2169_ = l_Lean_mkConst(v___x_2168_, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__25(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_box(0);
v___x_2175_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__24));
v___x_2176_ = l_Lean_mkConst(v___x_2175_, v___x_2174_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__28(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = lean_box(0);
v___x_2182_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__27));
v___x_2183_ = l_Lean_mkConst(v___x_2182_, v___x_2181_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor(lean_object* v_e_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2190_; lean_object* v_a_2191_; lean_object* v___x_2192_; 
v___x_2190_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_2184_, v_a_2186_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v___x_2190_);
v___x_2192_ = l_Lean_Meta_getNatValue_x3f(v_a_2191_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2282_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2282_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2282_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
if (lean_obj_tag(v_a_2193_) == 1)
{
lean_object* v_val_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
lean_dec(v_a_2191_);
v_val_2197_ = lean_ctor_get(v_a_2193_, 0);
lean_inc(v_val_2197_);
lean_dec_ref_known(v_a_2193_, 1);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = lean_nat_dec_eq(v_val_2197_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2200_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__2, &l_Lean_Meta_litToCtor___closed__2_once, _init_l_Lean_Meta_litToCtor___closed__2);
v___x_2201_ = lean_unsigned_to_nat(1u);
v___x_2202_ = lean_nat_sub(v_val_2197_, v___x_2201_);
lean_dec(v_val_2197_);
v___x_2203_ = l_Lean_mkNatLit(v___x_2202_);
v___x_2204_ = l_Lean_Expr_app___override(v___x_2200_, v___x_2203_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2204_);
v___x_2206_ = v___x_2195_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
lean_dec(v_val_2197_);
v___x_2208_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__5, &l_Lean_Meta_litToCtor___closed__5_once, _init_l_Lean_Meta_litToCtor___closed__5);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2208_);
v___x_2210_ = v___x_2195_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v___x_2212_; 
lean_del_object(v___x_2195_);
lean_dec(v_a_2193_);
lean_inc(v_a_2191_);
v___x_2212_ = l_Lean_Meta_getIntValue_x3f(v_a_2191_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2273_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2273_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2273_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
if (lean_obj_tag(v_a_2213_) == 1)
{
lean_object* v_val_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
lean_dec(v_a_2191_);
v_val_2217_ = lean_ctor_get(v_a_2213_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v_a_2213_, 1);
v___x_2218_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_2219_ = lean_int_dec_lt(v_val_2217_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2220_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__7, &l_Lean_Meta_litToCtor___closed__7_once, _init_l_Lean_Meta_litToCtor___closed__7);
v___x_2221_ = l_Int_toNat(v_val_2217_);
lean_dec(v_val_2217_);
v___x_2222_ = l_Lean_mkNatLit(v___x_2221_);
v___x_2223_ = l_Lean_Expr_app___override(v___x_2220_, v___x_2222_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2223_);
v___x_2225_ = v___x_2215_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2227_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__10, &l_Lean_Meta_litToCtor___closed__10_once, _init_l_Lean_Meta_litToCtor___closed__10);
v___x_2228_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__11, &l_Lean_Meta_litToCtor___closed__11_once, _init_l_Lean_Meta_litToCtor___closed__11);
v___x_2229_ = lean_int_add(v_val_2217_, v___x_2228_);
lean_dec(v_val_2217_);
v___x_2230_ = lean_int_neg(v___x_2229_);
lean_dec(v___x_2229_);
v___x_2231_ = l_Int_toNat(v___x_2230_);
lean_dec(v___x_2230_);
v___x_2232_ = l_Lean_mkNatLit(v___x_2231_);
v___x_2233_ = l_Lean_Expr_app___override(v___x_2227_, v___x_2232_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2233_);
v___x_2235_ = v___x_2215_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
else
{
lean_object* v___x_2237_; 
lean_del_object(v___x_2215_);
lean_dec(v_a_2213_);
lean_inc(v_a_2191_);
v___x_2237_ = l_Lean_Meta_getFinValue_x3f(v_a_2191_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2264_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2264_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2264_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
if (lean_obj_tag(v_a_2238_) == 1)
{
lean_object* v_val_2242_; lean_object* v_fst_2243_; lean_object* v_snd_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
lean_dec(v_a_2191_);
v_val_2242_ = lean_ctor_get(v_a_2238_, 0);
lean_inc(v_val_2242_);
lean_dec_ref_known(v_a_2238_, 1);
v_fst_2243_ = lean_ctor_get(v_val_2242_, 0);
lean_inc(v_fst_2243_);
v_snd_2244_ = lean_ctor_get(v_val_2242_, 1);
lean_inc(v_snd_2244_);
lean_dec(v_val_2242_);
v___x_2245_ = l_Lean_mkNatLit(v_snd_2244_);
v___x_2246_ = l_Lean_mkNatLit(v_fst_2243_);
v___x_2247_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__15, &l_Lean_Meta_litToCtor___closed__15_once, _init_l_Lean_Meta_litToCtor___closed__15);
v___x_2248_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__16, &l_Lean_Meta_litToCtor___closed__16_once, _init_l_Lean_Meta_litToCtor___closed__16);
v___x_2249_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__19, &l_Lean_Meta_litToCtor___closed__19_once, _init_l_Lean_Meta_litToCtor___closed__19);
lean_inc_ref_n(v___x_2246_, 2);
lean_inc_ref_n(v___x_2245_, 2);
v___x_2250_ = l_Lean_mkApp4(v___x_2247_, v___x_2248_, v___x_2249_, v___x_2245_, v___x_2246_);
v___x_2251_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__22, &l_Lean_Meta_litToCtor___closed__22_once, _init_l_Lean_Meta_litToCtor___closed__22);
v___x_2252_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__25, &l_Lean_Meta_litToCtor___closed__25_once, _init_l_Lean_Meta_litToCtor___closed__25);
v___x_2253_ = l_Lean_mkAppB(v___x_2252_, v___x_2245_, v___x_2246_);
v___x_2254_ = l_Lean_eagerReflBoolTrue;
v___x_2255_ = l_Lean_mkApp3(v___x_2251_, v___x_2250_, v___x_2253_, v___x_2254_);
v___x_2256_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__28, &l_Lean_Meta_litToCtor___closed__28_once, _init_l_Lean_Meta_litToCtor___closed__28);
v___x_2257_ = l_Lean_mkApp3(v___x_2256_, v___x_2246_, v___x_2245_, v___x_2255_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2257_);
v___x_2259_ = v___x_2240_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
else
{
lean_object* v___x_2262_; 
lean_dec(v_a_2238_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v_a_2191_);
v___x_2262_ = v___x_2240_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2191_);
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
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_a_2191_);
v_a_2265_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2237_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2237_);
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
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_a_2191_);
v_a_2274_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2212_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2212_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v_a_2191_);
v_a_2283_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2192_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2192_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor___boxed(lean_object* v_e_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_Meta_litToCtor(v_e_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(lean_object* v_fst_2300_, lean_object* v_snd_2301_, lean_object* v_x_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2308_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0));
v___x_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2309_, 0, v_fst_2300_);
lean_ctor_set(v___x_2309_, 1, v_snd_2301_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2313_, lean_object* v_snd_2314_, lean_object* v_x_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2313_, v_snd_2314_, v_x_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(lean_object* v_f_2333_, lean_object* v_a_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___y_2341_; lean_object* v_snd_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2449_; 
v_snd_2361_ = lean_ctor_get(v_a_2334_, 1);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_a_2334_);
if (v_isSharedCheck_2449_ == 0)
{
lean_object* v_unused_2450_; 
v_unused_2450_ = lean_ctor_get(v_a_2334_, 0);
lean_dec(v_unused_2450_);
v___x_2363_ = v_a_2334_;
v_isShared_2364_ = v_isSharedCheck_2449_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_snd_2361_);
lean_dec(v_a_2334_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2449_;
goto v_resetjp_2362_;
}
v___jp_2340_:
{
if (lean_obj_tag(v___y_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2352_; 
v_a_2342_ = lean_ctor_get(v___y_2341_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___y_2341_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2344_ = v___y_2341_;
v_isShared_2345_ = v_isSharedCheck_2352_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___y_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2352_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
if (lean_obj_tag(v_a_2342_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; 
lean_dec_ref(v_f_2333_);
v_a_2346_ = lean_ctor_get(v_a_2342_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v_a_2342_, 1);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v_a_2346_);
v___x_2348_ = v___x_2344_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
else
{
lean_object* v_a_2350_; 
lean_del_object(v___x_2344_);
v_a_2350_ = lean_ctor_get(v_a_2342_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v_a_2342_, 1);
v_a_2334_ = v_a_2350_;
goto _start;
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v_f_2333_);
v_a_2353_ = lean_ctor_get(v___y_2341_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___y_2341_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___y_2341_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___y_2341_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
v_resetjp_2362_:
{
lean_object* v_fst_2365_; lean_object* v_snd_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2448_; 
v_fst_2365_ = lean_ctor_get(v_snd_2361_, 0);
v_snd_2366_ = lean_ctor_get(v_snd_2361_, 1);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_snd_2361_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2368_ = v_snd_2361_;
v_isShared_2369_ = v_isSharedCheck_2448_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_snd_2366_);
lean_inc(v_fst_2365_);
lean_dec(v_snd_2361_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2448_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; 
lean_inc(v_fst_2365_);
v___x_2370_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_fst_2365_, v___y_2336_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2439_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2439_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2439_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; uint8_t v___x_2376_; 
v___x_2375_ = l_Lean_Expr_cleanupAnnotations(v_a_2371_);
v___x_2376_ = l_Lean_Expr_isApp(v___x_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec_ref(v___x_2375_);
lean_del_object(v___x_2373_);
lean_del_object(v___x_2368_);
lean_del_object(v___x_2363_);
v___x_2377_ = lean_box(0);
v___x_2378_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2365_, v_snd_2366_, v___x_2377_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
v___y_2341_ = v___x_2378_;
goto v___jp_2340_;
}
else
{
lean_object* v_arg_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; 
v_arg_2379_ = lean_ctor_get(v___x_2375_, 1);
lean_inc_ref(v_arg_2379_);
v___x_2380_ = lean_box(0);
v___x_2381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2375_);
v___x_2382_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2));
v___x_2383_ = l_Lean_Expr_isConstOf(v___x_2381_, v___x_2382_);
if (v___x_2383_ == 0)
{
uint8_t v___x_2384_; 
lean_del_object(v___x_2373_);
v___x_2384_ = l_Lean_Expr_isApp(v___x_2381_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v___x_2381_);
lean_dec_ref(v_arg_2379_);
lean_del_object(v___x_2368_);
lean_del_object(v___x_2363_);
v___x_2385_ = lean_box(0);
v___x_2386_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2365_, v_snd_2366_, v___x_2385_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
v___y_2341_ = v___x_2386_;
goto v___jp_2340_;
}
else
{
lean_object* v_arg_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v_arg_2387_ = lean_ctor_get(v___x_2381_, 1);
lean_inc_ref(v_arg_2387_);
v___x_2388_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2381_);
v___x_2389_ = l_Lean_Expr_isApp(v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_arg_2387_);
lean_dec_ref(v_arg_2379_);
lean_del_object(v___x_2368_);
lean_del_object(v___x_2363_);
v___x_2390_ = lean_box(0);
v___x_2391_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2365_, v_snd_2366_, v___x_2390_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
v___y_2341_ = v___x_2391_;
goto v___jp_2340_;
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2392_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2388_);
v___x_2393_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4));
v___x_2394_ = l_Lean_Expr_isConstOf(v___x_2392_, v___x_2393_);
lean_dec_ref(v___x_2392_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
lean_dec_ref(v_arg_2387_);
lean_dec_ref(v_arg_2379_);
lean_del_object(v___x_2368_);
lean_del_object(v___x_2363_);
v___x_2395_ = lean_box(0);
v___x_2396_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_2365_, v_snd_2366_, v___x_2395_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
v___y_2341_ = v___x_2396_;
goto v___jp_2340_;
}
else
{
lean_object* v___x_2397_; 
lean_inc_ref(v_f_2333_);
lean_inc(v___y_2338_);
lean_inc_ref(v___y_2337_);
lean_inc(v___y_2336_);
lean_inc_ref(v___y_2335_);
v___x_2397_ = lean_apply_6(v_f_2333_, v_arg_2387_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, lean_box(0));
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2421_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2421_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2421_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
if (lean_obj_tag(v_a_2398_) == 1)
{
lean_object* v_val_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
lean_del_object(v___x_2400_);
lean_dec(v_fst_2365_);
v_val_2402_ = lean_ctor_get(v_a_2398_, 0);
lean_inc(v_val_2402_);
lean_dec_ref_known(v_a_2398_, 1);
v___x_2403_ = lean_array_push(v_snd_2366_, v_val_2402_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 1, v___x_2403_);
lean_ctor_set(v___x_2368_, 0, v_arg_2379_);
v___x_2405_ = v___x_2368_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_arg_2379_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2407_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 1, v___x_2405_);
lean_ctor_set(v___x_2363_, 0, v___x_2380_);
v___x_2407_ = v___x_2363_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
v_a_2334_ = v___x_2407_;
goto _start;
}
}
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
lean_dec(v_a_2398_);
lean_dec_ref(v_arg_2379_);
lean_dec_ref(v_f_2333_);
v___x_2411_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5));
if (v_isShared_2369_ == 0)
{
v___x_2413_ = v___x_2368_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_fst_2365_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_snd_2366_);
v___x_2413_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2415_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 1, v___x_2413_);
lean_ctor_set(v___x_2363_, 0, v___x_2411_);
v___x_2415_ = v___x_2363_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2417_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2415_);
v___x_2417_ = v___x_2400_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec_ref(v_arg_2379_);
lean_del_object(v___x_2368_);
lean_dec(v_snd_2366_);
lean_dec(v_fst_2365_);
lean_del_object(v___x_2363_);
lean_dec_ref(v_f_2333_);
v_a_2422_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2397_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2397_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2431_; 
lean_dec_ref(v___x_2381_);
lean_dec_ref(v_arg_2379_);
lean_dec_ref(v_f_2333_);
if (v_isShared_2369_ == 0)
{
v___x_2431_ = v___x_2368_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_fst_2365_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_snd_2366_);
v___x_2431_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2433_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 1, v___x_2431_);
lean_ctor_set(v___x_2363_, 0, v___x_2380_);
v___x_2433_ = v___x_2363_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2435_; 
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2433_);
v___x_2435_ = v___x_2373_;
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
}
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_del_object(v___x_2368_);
lean_dec(v_snd_2366_);
lean_dec(v_fst_2365_);
lean_del_object(v___x_2363_);
lean_dec_ref(v_f_2333_);
v_a_2440_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2370_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2370_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___boxed(lean_object* v_f_2451_, lean_object* v_a_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_2451_, v_a_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg(lean_object* v_e_2461_, lean_object* v_f_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2505_; 
v___x_2468_ = l_Lean_Expr_consumeMData(v_e_2461_);
v___x_2469_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_2468_, v_a_2464_);
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2472_ = v___x_2469_;
v_isShared_2473_ = v_isSharedCheck_2505_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2469_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2505_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2474_ = ((lean_object*)(l_Lean_Meta_getListLitOf_x3f___redArg___closed__0));
v___x_2475_ = lean_box(0);
v___x_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2476_, 0, v_a_2470_);
lean_ctor_set(v___x_2476_, 1, v___x_2474_);
v___x_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_2462_, v___x_2477_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2496_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2496_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2496_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v_fst_2483_; 
v_fst_2483_ = lean_ctor_get(v_a_2479_, 0);
if (lean_obj_tag(v_fst_2483_) == 0)
{
lean_object* v_snd_2484_; lean_object* v_snd_2485_; lean_object* v___x_2487_; 
v_snd_2484_ = lean_ctor_get(v_a_2479_, 1);
lean_inc(v_snd_2484_);
lean_dec(v_a_2479_);
v_snd_2485_ = lean_ctor_get(v_snd_2484_, 1);
lean_inc(v_snd_2485_);
lean_dec(v_snd_2484_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set_tag(v___x_2472_, 1);
lean_ctor_set(v___x_2472_, 0, v_snd_2485_);
v___x_2487_ = v___x_2472_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_snd_2485_);
v___x_2487_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2489_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2487_);
v___x_2489_ = v___x_2481_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
else
{
lean_object* v_val_2492_; lean_object* v___x_2494_; 
lean_inc_ref(v_fst_2483_);
lean_dec(v_a_2479_);
lean_del_object(v___x_2472_);
v_val_2492_ = lean_ctor_get(v_fst_2483_, 0);
lean_inc(v_val_2492_);
lean_dec_ref_known(v_fst_2483_, 1);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v_val_2492_);
v___x_2494_ = v___x_2481_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_val_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_del_object(v___x_2472_);
v_a_2497_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2478_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2478_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___boxed(lean_object* v_e_2506_, lean_object* v_f_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_2506_, v_f_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec_ref(v_e_2506_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f(lean_object* v_00_u03b1_2514_, lean_object* v_e_2515_, lean_object* v_f_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_2515_, v_f_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___boxed(lean_object* v_00_u03b1_2523_, lean_object* v_e_2524_, lean_object* v_f_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_Meta_getListLitOf_x3f(v_00_u03b1_2523_, v_e_2524_, v_f_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec_ref(v_e_2524_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(lean_object* v_00_u03b1_2532_, lean_object* v_f_2533_, lean_object* v_inst_2534_, lean_object* v_a_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_2533_, v_a_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___boxed(lean_object* v_00_u03b1_2542_, lean_object* v_f_2543_, lean_object* v_inst_2544_, lean_object* v_a_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(v_00_u03b1_2542_, v_f_2543_, v_inst_2544_, v_a_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0(lean_object* v_s_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v_s_2552_);
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0___boxed(lean_object* v_s_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Meta_getListLit_x3f___lam__0(v_s_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f(lean_object* v_e_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v___f_2574_; lean_object* v___x_2575_; 
v___f_2574_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_2575_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_2568_, v___f_2574_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___boxed(lean_object* v_e_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Meta_getListLit_x3f(v_e_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec_ref(v_e_2576_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg(lean_object* v_e_2587_, lean_object* v_f_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v_a_2596_; lean_object* v___x_2597_; 
v___x_2594_ = l_Lean_Expr_consumeMData(v_e_2587_);
v___x_2595_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_2594_, v_a_2590_);
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref(v___x_2595_);
v___x_2597_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2596_, v_a_2590_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2616_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2616_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2616_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = l_Lean_Expr_cleanupAnnotations(v_a_2598_);
v___x_2608_ = l_Lean_Expr_isApp(v___x_2607_);
if (v___x_2608_ == 0)
{
lean_dec_ref(v___x_2607_);
lean_dec_ref(v_f_2588_);
goto v___jp_2602_;
}
else
{
lean_object* v_arg_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v_arg_2609_ = lean_ctor_get(v___x_2607_, 1);
lean_inc_ref(v_arg_2609_);
v___x_2610_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2607_);
v___x_2611_ = l_Lean_Expr_isApp(v___x_2610_);
if (v___x_2611_ == 0)
{
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_arg_2609_);
lean_dec_ref(v_f_2588_);
goto v___jp_2602_;
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2610_);
v___x_2613_ = ((lean_object*)(l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1));
v___x_2614_ = l_Lean_Expr_isConstOf(v___x_2612_, v___x_2613_);
lean_dec_ref(v___x_2612_);
if (v___x_2614_ == 0)
{
lean_dec_ref(v_arg_2609_);
lean_dec_ref(v_f_2588_);
goto v___jp_2602_;
}
else
{
lean_object* v___x_2615_; 
lean_del_object(v___x_2600_);
v___x_2615_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_arg_2609_, v_f_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
lean_dec_ref(v_arg_2609_);
return v___x_2615_;
}
}
}
v___jp_2602_:
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2603_ = lean_box(0);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2603_);
v___x_2605_ = v___x_2600_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v_f_2588_);
v_a_2617_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2597_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2597_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___boxed(lean_object* v_e_2625_, lean_object* v_f_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2625_, v_f_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec_ref(v_e_2625_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f(lean_object* v_00_u03b1_2633_, lean_object* v_e_2634_, lean_object* v_f_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2634_, v_f_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___boxed(lean_object* v_00_u03b1_2642_, lean_object* v_e_2643_, lean_object* v_f_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_Meta_getArrayLitOf_x3f(v_00_u03b1_2642_, v_e_2643_, v_f_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec_ref(v_e_2643_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object* v_e_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v___f_2657_; lean_object* v___x_2658_; 
v___f_2657_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_2658_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2651_, v___f_2657_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f___boxed(lean_object* v_e_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Meta_getArrayLit_x3f(v_e_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec_ref(v_e_2659_);
return v_res_2665_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
