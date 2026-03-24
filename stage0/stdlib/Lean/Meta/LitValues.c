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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_getListLitOf_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_getListLitOf_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_getListLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getListLit_x3f___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_getListLit_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getListLit_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
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
lean_dec_ref(v___x_2_);
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
lean_dec_ref(v___x_63_);
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
lean_dec_ref(v___x_384_);
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
lean_dec_ref(v_a_411_);
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
lean_dec_ref(v_e_542_);
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
lean_dec_ref(v_a_565_);
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
lean_dec_ref(v___x_580_);
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
lean_dec_ref(v___x_722_);
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
lean_dec_ref(v_a_731_);
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
lean_dec_ref(v___x_746_);
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
lean_dec_ref(v_a_673_);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(lean_object* v_e_1024_, lean_object* v___y_1025_){
_start:
{
uint8_t v___x_1027_; 
v___x_1027_ = l_Lean_Expr_hasMVar(v_e_1024_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v_e_1024_);
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; lean_object* v_mctx_1030_; lean_object* v___x_1031_; lean_object* v_fst_1032_; lean_object* v_snd_1033_; lean_object* v___x_1034_; lean_object* v_cache_1035_; lean_object* v_zetaDeltaFVarIds_1036_; lean_object* v_postponed_1037_; lean_object* v_diag_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1047_; 
v___x_1029_ = lean_st_ref_get(v___y_1025_);
v_mctx_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_ref(v_mctx_1030_);
lean_dec(v___x_1029_);
v___x_1031_ = l_Lean_instantiateMVarsCore(v_mctx_1030_, v_e_1024_);
v_fst_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_fst_1032_);
v_snd_1033_ = lean_ctor_get(v___x_1031_, 1);
lean_inc(v_snd_1033_);
lean_dec_ref(v___x_1031_);
v___x_1034_ = lean_st_ref_take(v___y_1025_);
v_cache_1035_ = lean_ctor_get(v___x_1034_, 1);
v_zetaDeltaFVarIds_1036_ = lean_ctor_get(v___x_1034_, 2);
v_postponed_1037_ = lean_ctor_get(v___x_1034_, 3);
v_diag_1038_ = lean_ctor_get(v___x_1034_, 4);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v___x_1034_, 0);
lean_dec(v_unused_1048_);
v___x_1040_ = v___x_1034_;
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_diag_1038_);
lean_inc(v_postponed_1037_);
lean_inc(v_zetaDeltaFVarIds_1036_);
lean_inc(v_cache_1035_);
lean_dec(v___x_1034_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v_snd_1033_);
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_snd_1033_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_cache_1035_);
lean_ctor_set(v_reuseFailAlloc_1046_, 2, v_zetaDeltaFVarIds_1036_);
lean_ctor_set(v_reuseFailAlloc_1046_, 3, v_postponed_1037_);
lean_ctor_set(v_reuseFailAlloc_1046_, 4, v_diag_1038_);
v___x_1043_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_st_ref_set(v___y_1025_, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_fst_1032_);
return v___x_1045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg___boxed(lean_object* v_e_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1049_, v___y_1050_);
lean_dec(v___y_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(lean_object* v_e_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1053_, v___y_1055_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___boxed(lean_object* v_e_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(v_e_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1066_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__0(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = lean_nat_to_int(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__1(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = l_Lean_Level_ofNat(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__2(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__1, &l_Lean_Meta_normLitValue___closed__1_once, _init_l_Lean_Meta_normLitValue___closed__1);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__3(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_1075_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__4));
v___x_1076_ = l_Lean_Expr_const___override(v___x_1075_, v___x_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__4(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_box(0);
v___x_1078_ = ((lean_object*)(l_Lean_Meta_getIntValue_x3f___closed__1));
v___x_1079_ = l_Lean_Expr_const___override(v___x_1078_, v___x_1077_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__7(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__6));
v___x_1086_ = l_Lean_Expr_const___override(v___x_1085_, v___x_1084_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__8(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_1088_ = ((lean_object*)(l_Lean_Meta_getOfNatValue_x3f___closed__2));
v___x_1089_ = l_Lean_Expr_const___override(v___x_1088_, v___x_1087_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__9(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = lean_box(0);
v___x_1091_ = ((lean_object*)(l_Lean_Meta_getFinValue_x3f___closed__1));
v___x_1092_ = l_Lean_mkConst(v___x_1091_, v___x_1090_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__12(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_box(0);
v___x_1098_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__11));
v___x_1099_ = l_Lean_Expr_const___override(v___x_1098_, v___x_1097_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__15(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_box(0);
v___x_1105_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__14));
v___x_1106_ = l_Lean_Expr_const___override(v___x_1105_, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__16(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_box(0);
v___x_1108_ = ((lean_object*)(l_Lean_Meta_getBitVecValue_x3f___closed__2));
v___x_1109_ = l_Lean_Expr_const___override(v___x_1108_, v___x_1107_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__17(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = ((lean_object*)(l_Lean_Meta_getCharValue_x3f___closed__1));
v___x_1112_ = l_Lean_mkConst(v___x_1111_, v___x_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__18(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = ((lean_object*)(l_Lean_Meta_getUInt8Value_x3f___closed__1));
v___x_1115_ = l_Lean_mkConst(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__20(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_box(0);
v___x_1120_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__19));
v___x_1121_ = l_Lean_Expr_const___override(v___x_1120_, v___x_1119_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__21(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_box(0);
v___x_1123_ = ((lean_object*)(l_Lean_Meta_getUInt16Value_x3f___closed__1));
v___x_1124_ = l_Lean_mkConst(v___x_1123_, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__23(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__22));
v___x_1130_ = l_Lean_Expr_const___override(v___x_1129_, v___x_1128_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__24(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_box(0);
v___x_1132_ = ((lean_object*)(l_Lean_Meta_getUInt32Value_x3f___closed__1));
v___x_1133_ = l_Lean_mkConst(v___x_1132_, v___x_1131_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__26(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__25));
v___x_1139_ = l_Lean_Expr_const___override(v___x_1138_, v___x_1137_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__27(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = ((lean_object*)(l_Lean_Meta_getUInt64Value_x3f___closed__1));
v___x_1142_ = l_Lean_mkConst(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Meta_normLitValue___closed__29(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = lean_box(0);
v___x_1147_ = ((lean_object*)(l_Lean_Meta_normLitValue___closed__28));
v___x_1148_ = l_Lean_Expr_const___override(v___x_1147_, v___x_1146_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue(lean_object* v_e_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v___x_1155_; lean_object* v_a_1156_; lean_object* v___x_1157_; 
v___x_1155_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1149_, v_a_1151_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref(v___x_1155_);
v___x_1157_ = l_Lean_Meta_getNatValue_x3f(v_a_1156_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1392_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1392_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1392_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
if (lean_obj_tag(v_a_1158_) == 1)
{
lean_object* v_val_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_dec(v_a_1156_);
v_val_1162_ = lean_ctor_get(v_a_1158_, 0);
lean_inc(v_val_1162_);
lean_dec_ref(v_a_1158_);
v___x_1163_ = l_Lean_mkNatLit(v_val_1162_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1163_);
v___x_1165_ = v___x_1160_;
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
else
{
lean_object* v___x_1167_; 
lean_del_object(v___x_1160_);
lean_dec(v_a_1158_);
lean_inc(v_a_1156_);
v___x_1167_ = l_Lean_Meta_getIntValue_x3f(v_a_1156_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1383_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1383_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1383_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
if (lean_obj_tag(v_a_1168_) == 1)
{
lean_object* v_val_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
lean_dec(v_a_1156_);
v_val_1172_ = lean_ctor_get(v_a_1168_, 0);
lean_inc(v_val_1172_);
lean_dec_ref(v_a_1168_);
v___x_1173_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_1174_ = lean_int_dec_le(v___x_1173_, v_val_1172_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1175_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__3, &l_Lean_Meta_normLitValue___closed__3_once, _init_l_Lean_Meta_normLitValue___closed__3);
v___x_1176_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__4, &l_Lean_Meta_normLitValue___closed__4_once, _init_l_Lean_Meta_normLitValue___closed__4);
v___x_1177_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__7, &l_Lean_Meta_normLitValue___closed__7_once, _init_l_Lean_Meta_normLitValue___closed__7);
v___x_1178_ = lean_int_neg(v_val_1172_);
lean_dec(v_val_1172_);
v___x_1179_ = l_Int_toNat(v___x_1178_);
lean_dec(v___x_1178_);
v___x_1180_ = l_Lean_instToExprInt_mkNat(v___x_1179_);
v___x_1181_ = l_Lean_mkApp3(v___x_1175_, v___x_1176_, v___x_1177_, v___x_1180_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1181_);
v___x_1183_ = v___x_1170_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1185_ = l_Int_toNat(v_val_1172_);
lean_dec(v_val_1172_);
v___x_1186_ = l_Lean_instToExprInt_mkNat(v___x_1185_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1186_);
v___x_1188_ = v___x_1170_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v___x_1190_; 
lean_del_object(v___x_1170_);
lean_dec(v_a_1168_);
lean_inc(v_a_1156_);
v___x_1190_ = l_Lean_Meta_getFinValue_x3f(v_a_1156_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1374_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1374_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1374_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
if (lean_obj_tag(v_a_1191_) == 1)
{
lean_object* v_val_1195_; lean_object* v_fst_1196_; lean_object* v_snd_1197_; lean_object* v_r_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
lean_dec(v_a_1156_);
v_val_1195_ = lean_ctor_get(v_a_1191_, 0);
lean_inc(v_val_1195_);
lean_dec_ref(v_a_1191_);
v_fst_1196_ = lean_ctor_get(v_val_1195_, 0);
lean_inc(v_fst_1196_);
v_snd_1197_ = lean_ctor_get(v_val_1195_, 1);
lean_inc(v_snd_1197_);
lean_dec(v_val_1195_);
v_r_1198_ = l_Lean_mkRawNatLit(v_snd_1197_);
v___x_1199_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1200_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__9, &l_Lean_Meta_normLitValue___closed__9_once, _init_l_Lean_Meta_normLitValue___closed__9);
lean_inc(v_fst_1196_);
v___x_1201_ = l_Lean_mkNatLit(v_fst_1196_);
lean_inc_ref(v___x_1201_);
v___x_1202_ = l_Lean_Expr_app___override(v___x_1200_, v___x_1201_);
v___x_1203_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__12, &l_Lean_Meta_normLitValue___closed__12_once, _init_l_Lean_Meta_normLitValue___closed__12);
v___x_1204_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__15, &l_Lean_Meta_normLitValue___closed__15_once, _init_l_Lean_Meta_normLitValue___closed__15);
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_nat_sub(v_fst_1196_, v___x_1205_);
lean_dec(v_fst_1196_);
v___x_1207_ = l_Lean_mkNatLit(v___x_1206_);
v___x_1208_ = l_Lean_Expr_app___override(v___x_1204_, v___x_1207_);
lean_inc_ref(v_r_1198_);
v___x_1209_ = l_Lean_mkApp3(v___x_1203_, v___x_1201_, v___x_1208_, v_r_1198_);
v___x_1210_ = l_Lean_mkApp3(v___x_1199_, v___x_1202_, v_r_1198_, v___x_1209_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1210_);
v___x_1212_ = v___x_1193_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
else
{
lean_object* v___x_1214_; 
lean_del_object(v___x_1193_);
lean_dec(v_a_1191_);
lean_inc(v_a_1156_);
v___x_1214_ = l_Lean_Meta_getBitVecValue_x3f(v_a_1156_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1365_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1365_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1365_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
if (lean_obj_tag(v_a_1215_) == 1)
{
lean_object* v_val_1219_; lean_object* v_fst_1220_; lean_object* v_snd_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
lean_dec(v_a_1156_);
v_val_1219_ = lean_ctor_get(v_a_1215_, 0);
lean_inc(v_val_1219_);
lean_dec_ref(v_a_1215_);
v_fst_1220_ = lean_ctor_get(v_val_1219_, 0);
lean_inc(v_fst_1220_);
v_snd_1221_ = lean_ctor_get(v_val_1219_, 1);
lean_inc(v_snd_1221_);
lean_dec(v_val_1219_);
v___x_1222_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__16, &l_Lean_Meta_normLitValue___closed__16_once, _init_l_Lean_Meta_normLitValue___closed__16);
v___x_1223_ = l_Lean_mkNatLit(v_fst_1220_);
v___x_1224_ = l_Lean_mkNatLit(v_snd_1221_);
v___x_1225_ = l_Lean_mkAppB(v___x_1222_, v___x_1223_, v___x_1224_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1225_);
v___x_1227_ = v___x_1217_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
else
{
lean_object* v___x_1229_; 
lean_dec(v_a_1215_);
lean_inc(v_a_1156_);
v___x_1229_ = l_Lean_Meta_getStringValue_x3f(v_a_1156_);
if (lean_obj_tag(v___x_1229_) == 1)
{
lean_object* v_val_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
lean_dec(v_a_1156_);
v_val_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1230_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = l_Lean_mkStrLit(v_val_1230_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1231_);
v___x_1233_ = v___x_1217_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
else
{
lean_object* v___x_1235_; 
lean_dec(v___x_1229_);
lean_del_object(v___x_1217_);
lean_inc(v_a_1156_);
v___x_1235_ = l_Lean_Meta_getCharValue_x3f(v_a_1156_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1356_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1356_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1356_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
if (lean_obj_tag(v_a_1236_) == 1)
{
lean_object* v_val_1240_; lean_object* v___x_1241_; uint32_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
lean_dec(v_a_1156_);
v_val_1240_ = lean_ctor_get(v_a_1236_, 0);
lean_inc(v_val_1240_);
lean_dec_ref(v_a_1236_);
v___x_1241_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__17, &l_Lean_Meta_normLitValue___closed__17_once, _init_l_Lean_Meta_normLitValue___closed__17);
v___x_1242_ = lean_unbox_uint32(v_val_1240_);
lean_dec(v_val_1240_);
v___x_1243_ = lean_uint32_to_nat(v___x_1242_);
v___x_1244_ = l_Lean_mkRawNatLit(v___x_1243_);
v___x_1245_ = l_Lean_Expr_app___override(v___x_1241_, v___x_1244_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1245_);
v___x_1247_ = v___x_1238_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
else
{
lean_object* v___x_1249_; 
lean_del_object(v___x_1238_);
lean_dec(v_a_1236_);
lean_inc(v_a_1156_);
v___x_1249_ = l_Lean_Meta_getUInt8Value_x3f(v_a_1156_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1347_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1347_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1347_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
if (lean_obj_tag(v_a_1250_) == 1)
{
lean_object* v_val_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v_r_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
lean_dec(v_a_1156_);
v_val_1254_ = lean_ctor_get(v_a_1250_, 0);
lean_inc(v_val_1254_);
lean_dec_ref(v_a_1250_);
v___x_1255_ = lean_unbox(v_val_1254_);
lean_dec(v_val_1254_);
v___x_1256_ = lean_uint8_to_nat(v___x_1255_);
v_r_1257_ = l_Lean_mkRawNatLit(v___x_1256_);
v___x_1258_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1259_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__18, &l_Lean_Meta_normLitValue___closed__18_once, _init_l_Lean_Meta_normLitValue___closed__18);
v___x_1260_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__20, &l_Lean_Meta_normLitValue___closed__20_once, _init_l_Lean_Meta_normLitValue___closed__20);
lean_inc_ref(v_r_1257_);
v___x_1261_ = l_Lean_Expr_app___override(v___x_1260_, v_r_1257_);
v___x_1262_ = l_Lean_mkApp3(v___x_1258_, v___x_1259_, v_r_1257_, v___x_1261_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1262_);
v___x_1264_ = v___x_1252_;
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
else
{
lean_object* v___x_1266_; 
lean_del_object(v___x_1252_);
lean_dec(v_a_1250_);
lean_inc(v_a_1156_);
v___x_1266_ = l_Lean_Meta_getUInt16Value_x3f(v_a_1156_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1338_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1338_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1338_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
if (lean_obj_tag(v_a_1267_) == 1)
{
lean_object* v_val_1271_; uint16_t v___x_1272_; lean_object* v___x_1273_; lean_object* v_r_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
lean_dec(v_a_1156_);
v_val_1271_ = lean_ctor_get(v_a_1267_, 0);
lean_inc(v_val_1271_);
lean_dec_ref(v_a_1267_);
v___x_1272_ = lean_unbox(v_val_1271_);
lean_dec(v_val_1271_);
v___x_1273_ = lean_uint16_to_nat(v___x_1272_);
v_r_1274_ = l_Lean_mkRawNatLit(v___x_1273_);
v___x_1275_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1276_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__21, &l_Lean_Meta_normLitValue___closed__21_once, _init_l_Lean_Meta_normLitValue___closed__21);
v___x_1277_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__23, &l_Lean_Meta_normLitValue___closed__23_once, _init_l_Lean_Meta_normLitValue___closed__23);
lean_inc_ref(v_r_1274_);
v___x_1278_ = l_Lean_Expr_app___override(v___x_1277_, v_r_1274_);
v___x_1279_ = l_Lean_mkApp3(v___x_1275_, v___x_1276_, v_r_1274_, v___x_1278_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1279_);
v___x_1281_ = v___x_1269_;
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
else
{
lean_object* v___x_1283_; 
lean_del_object(v___x_1269_);
lean_dec(v_a_1267_);
lean_inc(v_a_1156_);
v___x_1283_ = l_Lean_Meta_getUInt32Value_x3f(v_a_1156_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1329_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1329_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1329_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
if (lean_obj_tag(v_a_1284_) == 1)
{
lean_object* v_val_1288_; uint32_t v___x_1289_; lean_object* v___x_1290_; lean_object* v_r_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
lean_dec(v_a_1156_);
v_val_1288_ = lean_ctor_get(v_a_1284_, 0);
lean_inc(v_val_1288_);
lean_dec_ref(v_a_1284_);
v___x_1289_ = lean_unbox_uint32(v_val_1288_);
lean_dec(v_val_1288_);
v___x_1290_ = lean_uint32_to_nat(v___x_1289_);
v_r_1291_ = l_Lean_mkRawNatLit(v___x_1290_);
v___x_1292_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1293_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__24, &l_Lean_Meta_normLitValue___closed__24_once, _init_l_Lean_Meta_normLitValue___closed__24);
v___x_1294_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__26, &l_Lean_Meta_normLitValue___closed__26_once, _init_l_Lean_Meta_normLitValue___closed__26);
lean_inc_ref(v_r_1291_);
v___x_1295_ = l_Lean_Expr_app___override(v___x_1294_, v_r_1291_);
v___x_1296_ = l_Lean_mkApp3(v___x_1292_, v___x_1293_, v_r_1291_, v___x_1295_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1296_);
v___x_1298_ = v___x_1286_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
else
{
lean_object* v___x_1300_; 
lean_del_object(v___x_1286_);
lean_dec(v_a_1284_);
lean_inc(v_a_1156_);
v___x_1300_ = l_Lean_Meta_getUInt64Value_x3f(v_a_1156_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1320_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1320_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1320_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
if (lean_obj_tag(v_a_1301_) == 1)
{
lean_object* v_val_1305_; uint64_t v___x_1306_; lean_object* v___x_1307_; lean_object* v_r_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
lean_dec(v_a_1156_);
v_val_1305_ = lean_ctor_get(v_a_1301_, 0);
lean_inc(v_val_1305_);
lean_dec_ref(v_a_1301_);
v___x_1306_ = lean_unbox_uint64(v_val_1305_);
lean_dec(v_val_1305_);
v___x_1307_ = lean_uint64_to_nat(v___x_1306_);
v_r_1308_ = l_Lean_mkRawNatLit(v___x_1307_);
v___x_1309_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__8, &l_Lean_Meta_normLitValue___closed__8_once, _init_l_Lean_Meta_normLitValue___closed__8);
v___x_1310_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__27, &l_Lean_Meta_normLitValue___closed__27_once, _init_l_Lean_Meta_normLitValue___closed__27);
v___x_1311_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__29, &l_Lean_Meta_normLitValue___closed__29_once, _init_l_Lean_Meta_normLitValue___closed__29);
lean_inc_ref(v_r_1308_);
v___x_1312_ = l_Lean_Expr_app___override(v___x_1311_, v_r_1308_);
v___x_1313_ = l_Lean_mkApp3(v___x_1309_, v___x_1310_, v_r_1308_, v___x_1312_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1313_);
v___x_1315_ = v___x_1303_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
else
{
lean_object* v___x_1318_; 
lean_dec(v_a_1301_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v_a_1156_);
v___x_1318_ = v___x_1303_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1156_);
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
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v_a_1156_);
v_a_1321_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1300_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1300_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v_a_1156_);
v_a_1330_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1283_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1283_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
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
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_a_1156_);
v_a_1339_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1266_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1266_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
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
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec(v_a_1156_);
v_a_1348_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1249_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1249_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_a_1156_);
v_a_1357_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1235_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1235_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v_a_1156_);
v_a_1366_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1214_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1214_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
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
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec(v_a_1156_);
v_a_1375_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1190_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1190_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v_a_1156_);
v_a_1384_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1167_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1167_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_a_1156_);
v_a_1393_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1157_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1157_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue___boxed(lean_object* v_e_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Meta_normLitValue(v_e_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue(lean_object* v_e_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v___x_1414_; lean_object* v_a_1415_; lean_object* v___x_1416_; 
v___x_1414_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1408_, v_a_1410_);
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref(v___x_1414_);
v___x_1416_ = l_Lean_Meta_getNatValue_x3f(v_a_1415_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1581_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1581_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1581_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
if (lean_obj_tag(v_a_1417_) == 0)
{
lean_object* v___x_1421_; 
lean_del_object(v___x_1419_);
lean_inc(v_a_1415_);
v___x_1421_ = l_Lean_Meta_getIntValue_x3f(v_a_1415_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1567_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1567_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1567_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
uint8_t v___x_1426_; 
v___x_1426_ = 1;
if (lean_obj_tag(v_a_1422_) == 0)
{
lean_object* v___x_1427_; 
lean_del_object(v___x_1424_);
lean_inc(v_a_1415_);
v___x_1427_ = l_Lean_Meta_getFinValue_x3f(v_a_1415_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1554_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1554_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1554_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
if (lean_obj_tag(v_a_1428_) == 0)
{
lean_object* v___x_1432_; 
lean_del_object(v___x_1430_);
lean_inc(v_a_1415_);
v___x_1432_ = l_Lean_Meta_getBitVecValue_x3f(v_a_1415_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1541_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1541_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1541_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
if (lean_obj_tag(v_a_1433_) == 0)
{
lean_object* v___x_1437_; 
lean_inc(v_a_1415_);
v___x_1437_ = l_Lean_Meta_getStringValue_x3f(v_a_1415_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v___x_1438_; 
lean_del_object(v___x_1435_);
lean_inc(v_a_1415_);
v___x_1438_ = l_Lean_Meta_getCharValue_x3f(v_a_1415_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1524_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1524_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1524_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
if (lean_obj_tag(v_a_1439_) == 0)
{
lean_object* v___x_1443_; 
lean_del_object(v___x_1441_);
lean_inc(v_a_1415_);
v___x_1443_ = l_Lean_Meta_getUInt8Value_x3f(v_a_1415_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1511_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1446_ = v___x_1443_;
v_isShared_1447_ = v_isSharedCheck_1511_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1443_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1511_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
if (lean_obj_tag(v_a_1444_) == 0)
{
lean_object* v___x_1448_; 
lean_del_object(v___x_1446_);
lean_inc(v_a_1415_);
v___x_1448_ = l_Lean_Meta_getUInt16Value_x3f(v_a_1415_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1498_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1498_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1498_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
if (lean_obj_tag(v_a_1449_) == 0)
{
lean_object* v___x_1453_; 
lean_del_object(v___x_1451_);
lean_inc(v_a_1415_);
v___x_1453_ = l_Lean_Meta_getUInt32Value_x3f(v_a_1415_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1485_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1485_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1485_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
if (lean_obj_tag(v_a_1454_) == 0)
{
lean_object* v___x_1458_; 
lean_del_object(v___x_1456_);
v___x_1458_ = l_Lean_Meta_getUInt64Value_x3f(v_a_1415_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1472_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1472_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1472_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
if (lean_obj_tag(v_a_1459_) == 0)
{
uint8_t v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1463_ = 0;
v___x_1464_ = lean_box(v___x_1463_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1464_);
v___x_1466_ = v___x_1461_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_dec_ref(v_a_1459_);
v___x_1468_ = lean_box(v___x_1426_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1468_);
v___x_1470_ = v___x_1461_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1473_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1458_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1458_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1483_; 
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1415_);
v___x_1481_ = lean_box(v___x_1426_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1481_);
v___x_1483_ = v___x_1456_;
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
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v_a_1415_);
v_a_1486_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1453_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1453_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
lean_dec_ref(v_a_1449_);
lean_dec(v_a_1415_);
v___x_1494_ = lean_box(v___x_1426_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1494_);
v___x_1496_ = v___x_1451_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_a_1415_);
v_a_1499_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1448_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1448_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
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
else
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1415_);
v___x_1507_ = lean_box(v___x_1426_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1507_);
v___x_1509_ = v___x_1446_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec(v_a_1415_);
v_a_1512_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1443_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1443_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1415_);
v___x_1520_ = lean_box(v___x_1426_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1520_);
v___x_1522_ = v___x_1441_;
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
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_a_1415_);
v_a_1525_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1438_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1438_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
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
else
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
lean_dec_ref(v___x_1437_);
lean_dec(v_a_1415_);
v___x_1533_ = lean_box(v___x_1426_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1533_);
v___x_1535_ = v___x_1435_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1415_);
v___x_1537_ = lean_box(v___x_1426_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1537_);
v___x_1539_ = v___x_1435_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec(v_a_1415_);
v_a_1542_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1432_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1432_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_dec_ref(v_a_1428_);
lean_dec(v_a_1415_);
v___x_1550_ = lean_box(v___x_1426_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1550_);
v___x_1552_ = v___x_1430_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_a_1415_);
v_a_1555_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1427_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1427_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1415_);
v___x_1563_ = lean_box(v___x_1426_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1563_);
v___x_1565_ = v___x_1424_;
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
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v_a_1415_);
v_a_1568_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1421_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1421_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
lean_dec_ref(v_a_1417_);
lean_dec(v_a_1415_);
v___x_1576_ = 1;
v___x_1577_ = lean_box(v___x_1576_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1577_);
v___x_1579_ = v___x_1419_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_a_1415_);
v_a_1582_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1416_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1416_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue___boxed(lean_object* v_e_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Meta_isLitValue(v_e_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1596_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__2(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = lean_box(0);
v___x_1602_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__1));
v___x_1603_ = l_Lean_mkConst(v___x_1602_, v___x_1601_);
return v___x_1603_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__5(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1608_ = lean_box(0);
v___x_1609_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__4));
v___x_1610_ = l_Lean_mkConst(v___x_1609_, v___x_1608_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__7(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1614_ = lean_box(0);
v___x_1615_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__6));
v___x_1616_ = l_Lean_mkConst(v___x_1615_, v___x_1614_);
return v___x_1616_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__10(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = lean_box(0);
v___x_1622_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__9));
v___x_1623_ = l_Lean_mkConst(v___x_1622_, v___x_1621_);
return v___x_1623_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__11(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_unsigned_to_nat(1u);
v___x_1625_ = lean_nat_to_int(v___x_1624_);
return v___x_1625_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__15(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__2, &l_Lean_Meta_normLitValue___closed__2_once, _init_l_Lean_Meta_normLitValue___closed__2);
v___x_1632_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__14));
v___x_1633_ = l_Lean_mkConst(v___x_1632_, v___x_1631_);
return v___x_1633_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__16(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = lean_box(0);
v___x_1635_ = ((lean_object*)(l_Lean_Meta_getNatValue_x3f___closed__1));
v___x_1636_ = l_Lean_mkConst(v___x_1635_, v___x_1634_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__19(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = lean_box(0);
v___x_1641_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__18));
v___x_1642_ = l_Lean_mkConst(v___x_1641_, v___x_1640_);
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__22(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_box(0);
v___x_1647_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__21));
v___x_1648_ = l_Lean_mkConst(v___x_1647_, v___x_1646_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__25(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = lean_box(0);
v___x_1654_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__24));
v___x_1655_ = l_Lean_mkConst(v___x_1654_, v___x_1653_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_Meta_litToCtor___closed__28(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1660_ = lean_box(0);
v___x_1661_ = ((lean_object*)(l_Lean_Meta_litToCtor___closed__27));
v___x_1662_ = l_Lean_mkConst(v___x_1661_, v___x_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor(lean_object* v_e_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v___x_1669_; lean_object* v_a_1670_; lean_object* v___x_1671_; 
v___x_1669_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v_e_1663_, v_a_1665_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref(v___x_1669_);
v___x_1671_ = l_Lean_Meta_getNatValue_x3f(v_a_1670_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1761_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1761_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1761_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
if (lean_obj_tag(v_a_1672_) == 1)
{
lean_object* v_val_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
lean_dec(v_a_1670_);
v_val_1676_ = lean_ctor_get(v_a_1672_, 0);
lean_inc(v_val_1676_);
lean_dec_ref(v_a_1672_);
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_nat_dec_eq(v_val_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1679_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__2, &l_Lean_Meta_litToCtor___closed__2_once, _init_l_Lean_Meta_litToCtor___closed__2);
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = lean_nat_sub(v_val_1676_, v___x_1680_);
lean_dec(v_val_1676_);
v___x_1682_ = l_Lean_mkNatLit(v___x_1681_);
v___x_1683_ = l_Lean_Expr_app___override(v___x_1679_, v___x_1682_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1683_);
v___x_1685_ = v___x_1674_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
lean_dec(v_val_1676_);
v___x_1687_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__5, &l_Lean_Meta_litToCtor___closed__5_once, _init_l_Lean_Meta_litToCtor___closed__5);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1687_);
v___x_1689_ = v___x_1674_;
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
}
else
{
lean_object* v___x_1691_; 
lean_del_object(v___x_1674_);
lean_dec(v_a_1672_);
lean_inc(v_a_1670_);
v___x_1691_ = l_Lean_Meta_getIntValue_x3f(v_a_1670_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1752_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1752_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1752_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
if (lean_obj_tag(v_a_1692_) == 1)
{
lean_object* v_val_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
lean_dec(v_a_1670_);
v_val_1696_ = lean_ctor_get(v_a_1692_, 0);
lean_inc(v_val_1696_);
lean_dec_ref(v_a_1692_);
v___x_1697_ = lean_obj_once(&l_Lean_Meta_normLitValue___closed__0, &l_Lean_Meta_normLitValue___closed__0_once, _init_l_Lean_Meta_normLitValue___closed__0);
v___x_1698_ = lean_int_dec_lt(v_val_1696_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1699_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__7, &l_Lean_Meta_litToCtor___closed__7_once, _init_l_Lean_Meta_litToCtor___closed__7);
v___x_1700_ = l_Int_toNat(v_val_1696_);
lean_dec(v_val_1696_);
v___x_1701_ = l_Lean_mkNatLit(v___x_1700_);
v___x_1702_ = l_Lean_Expr_app___override(v___x_1699_, v___x_1701_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1702_);
v___x_1704_ = v___x_1694_;
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
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1706_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__10, &l_Lean_Meta_litToCtor___closed__10_once, _init_l_Lean_Meta_litToCtor___closed__10);
v___x_1707_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__11, &l_Lean_Meta_litToCtor___closed__11_once, _init_l_Lean_Meta_litToCtor___closed__11);
v___x_1708_ = lean_int_add(v_val_1696_, v___x_1707_);
lean_dec(v_val_1696_);
v___x_1709_ = lean_int_neg(v___x_1708_);
lean_dec(v___x_1708_);
v___x_1710_ = l_Int_toNat(v___x_1709_);
lean_dec(v___x_1709_);
v___x_1711_ = l_Lean_mkNatLit(v___x_1710_);
v___x_1712_ = l_Lean_Expr_app___override(v___x_1706_, v___x_1711_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1712_);
v___x_1714_ = v___x_1694_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
else
{
lean_object* v___x_1716_; 
lean_del_object(v___x_1694_);
lean_dec(v_a_1692_);
lean_inc(v_a_1670_);
v___x_1716_ = l_Lean_Meta_getFinValue_x3f(v_a_1670_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1743_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1743_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1743_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
if (lean_obj_tag(v_a_1717_) == 1)
{
lean_object* v_val_1721_; lean_object* v_fst_1722_; lean_object* v_snd_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
lean_dec(v_a_1670_);
v_val_1721_ = lean_ctor_get(v_a_1717_, 0);
lean_inc(v_val_1721_);
lean_dec_ref(v_a_1717_);
v_fst_1722_ = lean_ctor_get(v_val_1721_, 0);
lean_inc(v_fst_1722_);
v_snd_1723_ = lean_ctor_get(v_val_1721_, 1);
lean_inc(v_snd_1723_);
lean_dec(v_val_1721_);
v___x_1724_ = l_Lean_mkNatLit(v_snd_1723_);
v___x_1725_ = l_Lean_mkNatLit(v_fst_1722_);
v___x_1726_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__15, &l_Lean_Meta_litToCtor___closed__15_once, _init_l_Lean_Meta_litToCtor___closed__15);
v___x_1727_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__16, &l_Lean_Meta_litToCtor___closed__16_once, _init_l_Lean_Meta_litToCtor___closed__16);
v___x_1728_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__19, &l_Lean_Meta_litToCtor___closed__19_once, _init_l_Lean_Meta_litToCtor___closed__19);
lean_inc_ref(v___x_1725_);
lean_inc_ref(v___x_1724_);
v___x_1729_ = l_Lean_mkApp4(v___x_1726_, v___x_1727_, v___x_1728_, v___x_1724_, v___x_1725_);
v___x_1730_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__22, &l_Lean_Meta_litToCtor___closed__22_once, _init_l_Lean_Meta_litToCtor___closed__22);
v___x_1731_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__25, &l_Lean_Meta_litToCtor___closed__25_once, _init_l_Lean_Meta_litToCtor___closed__25);
lean_inc_ref(v___x_1725_);
lean_inc_ref(v___x_1724_);
v___x_1732_ = l_Lean_mkAppB(v___x_1731_, v___x_1724_, v___x_1725_);
v___x_1733_ = l_Lean_eagerReflBoolTrue;
v___x_1734_ = l_Lean_mkApp3(v___x_1730_, v___x_1729_, v___x_1732_, v___x_1733_);
v___x_1735_ = lean_obj_once(&l_Lean_Meta_litToCtor___closed__28, &l_Lean_Meta_litToCtor___closed__28_once, _init_l_Lean_Meta_litToCtor___closed__28);
v___x_1736_ = l_Lean_mkApp3(v___x_1735_, v___x_1725_, v___x_1724_, v___x_1734_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1736_);
v___x_1738_ = v___x_1719_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
else
{
lean_object* v___x_1741_; 
lean_dec(v_a_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v_a_1670_);
v___x_1741_ = v___x_1719_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1670_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v_a_1670_);
v_a_1744_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1716_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1716_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v_a_1670_);
v_a_1753_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1691_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1691_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1670_);
v_a_1762_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1671_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1671_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor___boxed(lean_object* v_e_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Meta_litToCtor(v_e_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(lean_object* v_f_1790_, lean_object* v_b_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_snd_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1874_; 
v_snd_1797_ = lean_ctor_get(v_b_1791_, 1);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_b_1791_);
if (v_isSharedCheck_1874_ == 0)
{
lean_object* v_unused_1875_; 
v_unused_1875_ = lean_ctor_get(v_b_1791_, 0);
lean_dec(v_unused_1875_);
v___x_1799_ = v_b_1791_;
v_isShared_1800_ = v_isSharedCheck_1874_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_snd_1797_);
lean_dec(v_b_1791_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1874_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_fst_1801_; lean_object* v_snd_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1873_; 
v_fst_1801_ = lean_ctor_get(v_snd_1797_, 0);
v_snd_1802_ = lean_ctor_get(v_snd_1797_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_snd_1797_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1804_ = v_snd_1797_;
v_isShared_1805_ = v_isSharedCheck_1873_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_snd_1802_);
lean_inc(v_fst_1801_);
lean_dec(v_snd_1797_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1873_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; 
lean_inc(v_fst_1801_);
v___x_1806_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_fst_1801_, v___y_1793_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1864_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1864_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1864_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1822_ = l_Lean_Expr_cleanupAnnotations(v_a_1807_);
v___x_1823_ = l_Lean_Expr_isApp(v___x_1822_);
if (v___x_1823_ == 0)
{
lean_dec_ref(v___x_1822_);
lean_dec_ref(v_f_1790_);
goto v___jp_1811_;
}
else
{
lean_object* v_arg_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_arg_1824_ = lean_ctor_get(v___x_1822_, 1);
lean_inc_ref(v_arg_1824_);
v___x_1825_ = lean_box(0);
v___x_1826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1822_);
v___x_1827_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3));
v___x_1828_ = l_Lean_Expr_isConstOf(v___x_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
uint8_t v___x_1829_; 
v___x_1829_ = l_Lean_Expr_isApp(v___x_1826_);
if (v___x_1829_ == 0)
{
lean_dec_ref(v___x_1826_);
lean_dec_ref(v_arg_1824_);
lean_dec_ref(v_f_1790_);
goto v___jp_1811_;
}
else
{
lean_object* v_arg_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v_arg_1830_ = lean_ctor_get(v___x_1826_, 1);
lean_inc_ref(v_arg_1830_);
v___x_1831_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1826_);
v___x_1832_ = l_Lean_Expr_isApp(v___x_1831_);
if (v___x_1832_ == 0)
{
lean_dec_ref(v___x_1831_);
lean_dec_ref(v_arg_1830_);
lean_dec_ref(v_arg_1824_);
lean_dec_ref(v_f_1790_);
goto v___jp_1811_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1833_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1831_);
v___x_1834_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5));
v___x_1835_ = l_Lean_Expr_isConstOf(v___x_1833_, v___x_1834_);
lean_dec_ref(v___x_1833_);
if (v___x_1835_ == 0)
{
lean_dec_ref(v_arg_1830_);
lean_dec_ref(v_arg_1824_);
lean_dec_ref(v_f_1790_);
goto v___jp_1811_;
}
else
{
lean_object* v___x_1836_; 
lean_del_object(v___x_1809_);
lean_del_object(v___x_1804_);
lean_del_object(v___x_1799_);
lean_inc_ref(v_f_1790_);
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
lean_inc(v___y_1793_);
lean_inc_ref(v___y_1792_);
v___x_1836_ = lean_apply_6(v_f_1790_, v_arg_1830_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, lean_box(0));
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1852_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1852_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1852_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
if (lean_obj_tag(v_a_1837_) == 1)
{
lean_object* v_val_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_del_object(v___x_1839_);
lean_dec(v_fst_1801_);
v_val_1841_ = lean_ctor_get(v_a_1837_, 0);
lean_inc(v_val_1841_);
lean_dec_ref(v_a_1837_);
v___x_1842_ = lean_array_push(v_snd_1802_, v_val_1841_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_arg_1824_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1825_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v_b_1791_ = v___x_1844_;
goto _start;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
lean_dec(v_a_1837_);
lean_dec_ref(v_arg_1824_);
lean_dec_ref(v_f_1790_);
v___x_1846_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__6));
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_fst_1801_);
lean_ctor_set(v___x_1847_, 1, v_snd_1802_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1848_);
v___x_1850_ = v___x_1839_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v_arg_1824_);
lean_dec(v_snd_1802_);
lean_dec(v_fst_1801_);
lean_dec_ref(v_f_1790_);
v_a_1853_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1836_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1836_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec_ref(v___x_1826_);
lean_dec_ref(v_arg_1824_);
lean_del_object(v___x_1809_);
lean_del_object(v___x_1804_);
lean_del_object(v___x_1799_);
lean_dec_ref(v_f_1790_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v_fst_1801_);
lean_ctor_set(v___x_1861_, 1, v_snd_1802_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1825_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
}
v___jp_1811_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0));
if (v_isShared_1805_ == 0)
{
v___x_1814_ = v___x_1804_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_fst_1801_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_snd_1802_);
v___x_1814_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1816_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1814_);
lean_ctor_set(v___x_1799_, 0, v___x_1812_);
v___x_1816_ = v___x_1799_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1818_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1816_);
v___x_1818_ = v___x_1809_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_del_object(v___x_1804_);
lean_dec(v_snd_1802_);
lean_dec(v_fst_1801_);
lean_del_object(v___x_1799_);
lean_dec_ref(v_f_1790_);
v_a_1865_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1806_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1806_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___boxed(lean_object* v_f_1876_, lean_object* v_b_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_1876_, v_b_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg(lean_object* v_e_1886_, lean_object* v_f_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1930_; 
v___x_1893_ = l_Lean_Expr_consumeMData(v_e_1886_);
v___x_1894_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_1893_, v_a_1889_);
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1930_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1930_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1899_ = ((lean_object*)(l_Lean_Meta_getListLitOf_x3f___redArg___closed__0));
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v_a_1895_);
lean_ctor_set(v___x_1901_, 1, v___x_1899_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_1887_, v___x_1902_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1921_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1921_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1921_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v_fst_1908_; 
v_fst_1908_ = lean_ctor_get(v_a_1904_, 0);
if (lean_obj_tag(v_fst_1908_) == 0)
{
lean_object* v_snd_1909_; lean_object* v_snd_1910_; lean_object* v___x_1912_; 
v_snd_1909_ = lean_ctor_get(v_a_1904_, 1);
lean_inc(v_snd_1909_);
lean_dec(v_a_1904_);
v_snd_1910_ = lean_ctor_get(v_snd_1909_, 1);
lean_inc(v_snd_1910_);
lean_dec(v_snd_1909_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set_tag(v___x_1897_, 1);
lean_ctor_set(v___x_1897_, 0, v_snd_1910_);
v___x_1912_ = v___x_1897_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_snd_1910_);
v___x_1912_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1914_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1912_);
v___x_1914_ = v___x_1906_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
lean_object* v_val_1917_; lean_object* v___x_1919_; 
lean_inc_ref(v_fst_1908_);
lean_dec(v_a_1904_);
lean_del_object(v___x_1897_);
v_val_1917_ = lean_ctor_get(v_fst_1908_, 0);
lean_inc(v_val_1917_);
lean_dec_ref(v_fst_1908_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v_val_1917_);
v___x_1919_ = v___x_1906_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_val_1917_);
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
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_del_object(v___x_1897_);
v_a_1922_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1903_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1903_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___boxed(lean_object* v_e_1931_, lean_object* v_f_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_1931_, v_f_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec_ref(v_e_1931_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f(lean_object* v_00_u03b1_1939_, lean_object* v_e_1940_, lean_object* v_f_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_1940_, v_f_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___boxed(lean_object* v_00_u03b1_1948_, lean_object* v_e_1949_, lean_object* v_f_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Meta_getListLitOf_x3f(v_00_u03b1_1948_, v_e_1949_, v_f_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec_ref(v_e_1949_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0(lean_object* v_00_u03b1_1957_, lean_object* v_f_1958_, lean_object* v_b_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_1958_, v_b_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0___boxed(lean_object* v_00_u03b1_1966_, lean_object* v_f_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_getListLitOf_x3f_spec__0(v_00_u03b1_1966_, v_f_1967_, v_b_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0(lean_object* v_s_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_s_1975_);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0___boxed(lean_object* v_s_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Meta_getListLit_x3f___lam__0(v_s_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f(lean_object* v_e_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v___f_1997_; lean_object* v___x_1998_; 
v___f_1997_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_1998_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_e_1991_, v___f_1997_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___boxed(lean_object* v_e_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Meta_getListLit_x3f(v_e_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec_ref(v_e_1999_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg(lean_object* v_e_2010_, lean_object* v_f_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v_a_2019_; lean_object* v___x_2020_; 
v___x_2017_ = l_Lean_Expr_consumeMData(v_e_2010_);
v___x_2018_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(v___x_2017_, v_a_2013_);
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref(v___x_2018_);
v___x_2020_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2019_, v_a_2013_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2039_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2039_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2039_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = l_Lean_Expr_cleanupAnnotations(v_a_2021_);
v___x_2031_ = l_Lean_Expr_isApp(v___x_2030_);
if (v___x_2031_ == 0)
{
lean_dec_ref(v___x_2030_);
lean_dec_ref(v_f_2011_);
goto v___jp_2025_;
}
else
{
lean_object* v_arg_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_arg_2032_ = lean_ctor_get(v___x_2030_, 1);
lean_inc_ref(v_arg_2032_);
v___x_2033_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2030_);
v___x_2034_ = l_Lean_Expr_isApp(v___x_2033_);
if (v___x_2034_ == 0)
{
lean_dec_ref(v___x_2033_);
lean_dec_ref(v_arg_2032_);
lean_dec_ref(v_f_2011_);
goto v___jp_2025_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2035_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2033_);
v___x_2036_ = ((lean_object*)(l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1));
v___x_2037_ = l_Lean_Expr_isConstOf(v___x_2035_, v___x_2036_);
lean_dec_ref(v___x_2035_);
if (v___x_2037_ == 0)
{
lean_dec_ref(v_arg_2032_);
lean_dec_ref(v_f_2011_);
goto v___jp_2025_;
}
else
{
lean_object* v___x_2038_; 
lean_del_object(v___x_2023_);
v___x_2038_ = l_Lean_Meta_getListLitOf_x3f___redArg(v_arg_2032_, v_f_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_);
lean_dec_ref(v_arg_2032_);
return v___x_2038_;
}
}
}
v___jp_2025_:
{
lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2026_ = lean_box(0);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2026_);
v___x_2028_ = v___x_2023_;
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
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v_f_2011_);
v_a_2040_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2020_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2020_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___boxed(lean_object* v_e_2048_, lean_object* v_f_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2048_, v_f_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec_ref(v_e_2048_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f(lean_object* v_00_u03b1_2056_, lean_object* v_e_2057_, lean_object* v_f_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2057_, v_f_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___boxed(lean_object* v_00_u03b1_2065_, lean_object* v_e_2066_, lean_object* v_f_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Meta_getArrayLitOf_x3f(v_00_u03b1_2065_, v_e_2066_, v_f_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec_ref(v_e_2066_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object* v_e_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___f_2080_; lean_object* v___x_2081_; 
v___f_2080_ = ((lean_object*)(l_Lean_Meta_getListLit_x3f___closed__0));
v___x_2081_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(v_e_2074_, v___f_2080_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f___boxed(lean_object* v_e_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_Meta_getArrayLit_x3f(v_e_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec_ref(v_e_2082_);
return v_res_2088_;
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
