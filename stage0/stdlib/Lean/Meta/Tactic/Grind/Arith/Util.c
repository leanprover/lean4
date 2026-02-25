// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Util
// Imports: public import Init.Grind.Ring.Basic public import Lean.Meta.SynthInstance
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
static const lean_string_object l_Lean_Meta_Grind_Arith_isNatNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatNum___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isNatNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatNum___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatNum___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isNatNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instOfNatNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatNum___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__3_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isNatNum___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__3_value),LEAN_SCALAR_PTR_LITERAL(217, 8, 172, 44, 179, 254, 147, 95)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatNum___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__4_value;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 253, 199, 38, 151, 242, 146)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNonnegIntNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNonnegIntNum___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_isIntNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_isIntNum___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isIntNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_isIntNum___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isIntNum___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isIntNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isIntNum___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isIntNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_isIntNum___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isIntNum___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_isIntNum___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isIntNum___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isIntNum___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__4_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isIntNum___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntNum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNum___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_isNatType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatType___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatType___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isNatType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isNatType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatType___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatType___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatType___boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isIntType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isIntNum___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isIntType___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isIntType___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntType___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInstAddNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instAddNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(228, 164, 175, 25, 228, 165, 175, 183)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstAddNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_isInstLENat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLENat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInstLENat___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInstLENat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInstLENat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 47, 64, 46, 87, 101, 57, 105)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInstLENat___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstLENat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatAdd(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(190, 203, 124, 26, 63, 107, 241, 61)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__4_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__7_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__9_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__10_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__12_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__13_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__16_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__18_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__19_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__21_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isArithTerm___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__22_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isArithTerm___closed__23_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isArithTerm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_aquote(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_gcdExt_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_gcdExt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_gcdExt___closed__0;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink___boxed(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go_spec__0(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize___boxed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___boxed(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________;
static const lean_string_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__1_value),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__5_value),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__6_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8_value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Arith"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__9_value),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10_value),LEAN_SCALAR_PTR_LITERAL(49, 133, 41, 173, 115, 110, 60, 106)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__11_value),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__12_value),LEAN_SCALAR_PTR_LITERAL(99, 47, 13, 60, 197, 193, 165, 45)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(46, 179, 107, 69, 12, 52, 148, 180)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__14_value),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 132, 21, 175, 156, 33, 72, 31)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__15_value),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__4_value),LEAN_SCALAR_PTR_LITERAL(7, 2, 95, 171, 203, 101, 100, 29)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__16_value),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__8_value),LEAN_SCALAR_PTR_LITERAL(73, 168, 118, 35, 214, 136, 0, 211)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__17_value),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__10_value),LEAN_SCALAR_PTR_LITERAL(37, 50, 242, 4, 225, 57, 207, 233)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "____intModuleMarker____"};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__18_value),((lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__19_value),LEAN_SCALAR_PTR_LITERAL(198, 144, 62, 201, 130, 207, 89, 184)}};
static const lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_split___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_split___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_split___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__8_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__9_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__11;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__12;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__13;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__14;
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatNum(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_8 = l_Lean_Expr_isApp(x_7);
if (x_8 == 0)
{
lean_dec_ref(x_7);
lean_dec_ref(x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_7);
x_10 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__2));
x_11 = l_Lean_Expr_isConstOf(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_dec_ref(x_4);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Expr_cleanupAnnotations(x_4);
x_13 = l_Lean_Expr_isApp(x_12);
if (x_13 == 0)
{
lean_dec_ref(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_15 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__4));
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
lean_dec_ref(x_14);
return x_16;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNatNum(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNonnegIntNum(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_8 = l_Lean_Expr_isApp(x_7);
if (x_8 == 0)
{
lean_dec_ref(x_7);
lean_dec_ref(x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_7);
x_10 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__2));
x_11 = l_Lean_Expr_isConstOf(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_dec_ref(x_4);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Expr_cleanupAnnotations(x_4);
x_13 = l_Lean_Expr_isApp(x_12);
if (x_13 == 0)
{
lean_dec_ref(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_15 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__1));
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
lean_dec_ref(x_14);
return x_16;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNonnegIntNum___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNonnegIntNum(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntNum(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
lean_inc_ref(x_1);
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = l_Lean_Meta_Grind_Arith_isNonnegIntNum(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_8 = l_Lean_Meta_Grind_Arith_isNonnegIntNum(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
x_10 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_11 = l_Lean_Expr_isApp(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_12 = l_Lean_Meta_Grind_Arith_isNonnegIntNum(x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_10);
x_14 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntNum___closed__2));
x_15 = l_Lean_Expr_isConstOf(x_13, x_14);
lean_dec_ref(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_16 = l_Lean_Meta_Grind_Arith_isNonnegIntNum(x_1);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_9);
x_18 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntNum___closed__5));
x_19 = l_Lean_Expr_isConstOf(x_17, x_18);
lean_dec_ref(x_17);
if (x_19 == 0)
{
lean_dec_ref(x_5);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = l_Lean_Meta_Grind_Arith_isNonnegIntNum(x_5);
return x_20;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntNum___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isIntNum(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNum(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc_ref(x_1);
x_2 = l_Lean_Meta_Grind_Arith_isNatNum(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Meta_Grind_Arith_isIntNum(x_1);
return x_3;
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNum___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNum(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatType___closed__1));
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNatType(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntType___closed__0));
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isIntType(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstAddNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_7);
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_9 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1));
x_10 = l_Lean_Expr_isConstOf(x_8, x_9);
lean_dec_ref(x_8);
if (x_10 == 0)
{
lean_dec_ref(x_7);
lean_dec_ref(x_4);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Lean_Meta_Grind_Arith_isNatType(x_7);
lean_dec_ref(x_7);
if (x_11 == 0)
{
lean_dec_ref(x_4);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3));
x_13 = l_Lean_Expr_isConstOf(x_4, x_12);
lean_dec_ref(x_4);
return x_13;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstLENat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInstLENat___closed__1));
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isInstLENat(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
x_10 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_11 = l_Lean_Expr_isApp(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_13);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_10);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_20);
lean_dec_ref(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2));
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec_ref(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_26 = lean_box(0);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_13);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
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
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_5 = l_Lean_Expr_isApp(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_4);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_8);
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_dec_ref(x_9);
lean_dec_ref(x_8);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec_ref(x_11);
lean_dec_ref(x_8);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_14 = l_Lean_Expr_isApp(x_13);
if (x_14 == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Expr_appFnCleanup___redArg(x_13);
x_16 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2));
x_17 = l_Lean_Expr_isConstOf(x_15, x_16);
lean_dec_ref(x_15);
if (x_17 == 0)
{
lean_dec_ref(x_8);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_8);
return x_18;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNatAdd(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_13 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__2));
x_14 = l_Lean_Expr_isConstOf(x_12, x_13);
lean_dec_ref(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_5);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_cleanupAnnotations(x_5);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_16);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_21 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__4));
x_22 = l_Lean_Expr_isConstOf(x_20, x_21);
lean_dec_ref(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_19);
x_23 = lean_box(0);
return x_23;
}
else
{
if (lean_obj_tag(x_19) == 9)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_19);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_ctor_set_tag(x_24, 1);
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec_ref(x_24);
x_28 = lean_box(0);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec_ref(x_19);
x_29 = lean_box(0);
return x_29;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isArithTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_5 = l_Lean_Expr_isApp(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_4);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_9 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__2));
x_10 = l_Lean_Expr_isConstOf(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__5));
x_12 = l_Lean_Expr_isConstOf(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__2));
x_14 = l_Lean_Expr_isConstOf(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntNum___closed__2));
x_16 = l_Lean_Expr_isConstOf(x_8, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Expr_isApp(x_8);
if (x_17 == 0)
{
lean_dec_ref(x_8);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_23 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__8));
x_24 = l_Lean_Expr_isConstOf(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__11));
x_26 = l_Lean_Expr_isConstOf(x_22, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__14));
x_28 = l_Lean_Expr_isConstOf(x_22, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__17));
x_30 = l_Lean_Expr_isConstOf(x_22, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__20));
x_32 = l_Lean_Expr_isConstOf(x_22, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__23));
x_34 = l_Lean_Expr_isConstOf(x_22, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2));
x_36 = l_Lean_Expr_isConstOf(x_22, x_35);
lean_dec_ref(x_22);
return x_36;
}
else
{
lean_dec_ref(x_22);
return x_34;
}
}
else
{
lean_dec_ref(x_22);
return x_32;
}
}
else
{
lean_dec_ref(x_22);
return x_30;
}
}
else
{
lean_dec_ref(x_22);
return x_28;
}
}
else
{
lean_dec_ref(x_22);
return x_26;
}
}
else
{
lean_dec_ref(x_22);
return x_24;
}
}
}
}
}
else
{
lean_dec_ref(x_8);
return x_16;
}
}
else
{
lean_dec_ref(x_8);
return x_14;
}
}
else
{
lean_dec_ref(x_8);
return x_12;
}
}
else
{
lean_dec_ref(x_8);
return x_10;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc_ref(x_1);
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ofExpr(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_MessageData_ofExpr(x_1);
x_5 = l_Lean_aquote(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_gcdExt_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_gcdExt___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_obj_once(&l_Lean_Meta_Grind_Arith_gcdExt___closed__0, &l_Lean_Meta_Grind_Arith_gcdExt___closed__0_once, _init_l_Lean_Meta_Grind_Arith_gcdExt___closed__0);
x_4 = lean_int_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_int_emod(x_1, x_2);
x_6 = l_Lean_Meta_Grind_Arith_gcdExt(x_2, x_5);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_int_ediv(x_1, x_2);
x_13 = lean_int_mul(x_12, x_11);
lean_dec(x_12);
x_14 = lean_int_sub(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_11);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_int_ediv(x_1, x_2);
x_18 = lean_int_mul(x_17, x_16);
lean_dec(x_17);
x_19 = lean_int_sub(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_6, 1, x_20);
return x_6;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_26 = lean_int_ediv(x_1, x_2);
x_27 = lean_int_mul(x_26, x_24);
lean_dec(x_26);
x_28 = lean_int_sub(x_23, x_27);
lean_dec(x_27);
lean_dec(x_23);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_37; 
x_31 = lean_nat_abs(x_1);
x_32 = lean_nat_to_int(x_31);
x_37 = lean_int_dec_eq(x_1, x_3);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_int_ediv(x_1, x_32);
x_33 = x_38;
goto block_36;
}
else
{
x_33 = x_3;
goto block_36;
}
block_36:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_gcdExt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_pop___redArg(x_1);
x_1 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_shrink(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_nat_to_int(x_1);
x_3 = l_Rat_ofInt(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_nat_dec_lt(x_3, x_1);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0);
x_6 = l_Lean_PersistentArray_push___redArg(x_2, x_5);
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(x_2, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_shrink(x_1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_resize(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ptr_addr(x_1);
x_3 = lean_usize_to_uint64(x_2);
x_4 = 2;
x_5 = lean_uint64_shift_right(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unbox_uint64(x_4);
x_7 = lean_uint64_dec_eq(x_6, x_1);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; uint8_t x_17; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = 32;
x_6 = lean_uint64_shift_right(x_2, x_5);
x_7 = lean_uint64_xor(x_2, x_6);
x_8 = 16;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = lean_uint64_to_usize(x_10);
x_12 = lean_usize_of_nat(x_4);
x_13 = 1;
x_14 = lean_usize_sub(x_12, x_13);
x_15 = lean_usize_land(x_11, x_14);
x_16 = lean_array_uget_borrowed(x_3, x_15);
x_17 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(x_2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(x_1, x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = 32;
x_8 = lean_unbox_uint64(x_4);
x_9 = lean_uint64_shift_right(x_8, x_7);
x_10 = lean_unbox_uint64(x_4);
x_11 = lean_uint64_xor(x_10, x_9);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_6);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget_borrowed(x_1, x_19);
lean_inc(x_20);
lean_ctor_set(x_2, 2, x_20);
x_21 = lean_array_uset(x_1, x_19, x_2);
x_1 = x_21;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_26 = lean_array_get_size(x_1);
x_27 = 32;
x_28 = lean_unbox_uint64(x_23);
x_29 = lean_uint64_shift_right(x_28, x_27);
x_30 = lean_unbox_uint64(x_23);
x_31 = lean_uint64_xor(x_30, x_29);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_26);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget_borrowed(x_1, x_39);
lean_inc(x_40);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_array_uset(x_1, x_39, x_41);
x_1 = x_42;
x_2 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_2, x_7);
x_9 = lean_uint64_xor(x_2, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_6);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget_borrowed(x_5, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(x_2, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_25 = lean_box_uint64(x_2);
lean_inc(x_18);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_18);
x_27 = lean_array_uset(x_5, x_17, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_24, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_box_uint64(x_2);
lean_inc(x_18);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_18);
x_39 = lean_array_uset(x_5, x_17, x_38);
x_40 = lean_unsigned_to_nat(4u);
x_41 = lean_nat_mul(x_36, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_39);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(x_39);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
}
}
else
{
lean_dec(x_3);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(x_1);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(x_3, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_4);
lean_inc_ref(x_3);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = lean_box(0);
x_11 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(x_3, x_5, x_10);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_box(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(x_3, x_5, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = lean_box(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(lean_object* x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_3);
lean_dec_ref(x_3);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(x_1, x_2, x_4);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec_ref(x_3);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_box(0);
x_6 = l_Lean_FVarIdSet_insert(x_4, x_1);
lean_ctor_set(x_2, 1, x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = l_Lean_FVarIdSet_insert(x_9, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________(void) {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21, &l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21_once, _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
x_5 = lean_expr_eqv(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
x_8 = lean_apply_1(x_1, x_3);
x_9 = lean_nat_to_int(x_2);
x_10 = lean_int_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_3);
x_12 = lean_array_push(x_7, x_11);
lean_ctor_set(x_4, 1, x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
x_14 = l_Lean_PersistentArray_push___redArg(x_6, x_3);
lean_ctor_set(x_4, 0, x_14);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_3);
x_18 = lean_apply_1(x_1, x_3);
x_19 = lean_nat_to_int(x_2);
x_20 = lean_int_dec_eq(x_18, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_3);
x_22 = lean_array_push(x_17, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
x_25 = l_Lean_PersistentArray_push___redArg(x_16, x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__10, &l_Lean_Meta_Grind_Arith_split___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__12(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__10, &l_Lean_Meta_Grind_Arith_split___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10);
x_4 = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__11, &l_Lean_Meta_Grind_Arith_split___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__13, &l_Lean_Meta_Grind_Arith_split___redArg___closed__13_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13);
x_2 = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__12, &l_Lean_Meta_Grind_Arith_split___redArg___closed__12_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__12);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___redArg___closed__9));
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_split___redArg___lam__0), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__14, &l_Lean_Meta_Grind_Arith_split___redArg___closed__14_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__14);
x_7 = l_Lean_PersistentArray_forIn___redArg(x_3, x_1, x_6, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_split___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________ = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________();
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
