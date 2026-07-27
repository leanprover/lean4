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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_aquote(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_isNatNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatNum___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isNatNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatNum___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatNum___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isNatNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instOfNatNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatNum___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isNatNum___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__3_value),LEAN_SCALAR_PTR_LITERAL(217, 8, 172, 44, 179, 254, 147, 95)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isNatNum___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isNatNum___closed__4_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_gcdExt_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_gcdExt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_gcdExt___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go_spec__0(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_split___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_split___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_split___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_split___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__8_value),((lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__11;
static const lean_array_object l_Lean_Meta_Grind_Arith_split___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_split___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_split___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_split___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatNum(lean_object* v_e_9_){
_start:
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = l_Lean_Expr_cleanupAnnotations(v_e_9_);
v___x_11_ = l_Lean_Expr_isApp(v___x_10_);
if (v___x_11_ == 0)
{
lean_dec_ref(v___x_10_);
return v___x_11_;
}
else
{
lean_object* v_arg_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v_arg_12_ = lean_ctor_get(v___x_10_, 1);
lean_inc_ref(v_arg_12_);
v___x_13_ = l_Lean_Expr_appFnCleanup___redArg(v___x_10_);
v___x_14_ = l_Lean_Expr_isApp(v___x_13_);
if (v___x_14_ == 0)
{
lean_dec_ref(v___x_13_);
lean_dec_ref(v_arg_12_);
return v___x_14_;
}
else
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = l_Lean_Expr_appFnCleanup___redArg(v___x_13_);
v___x_16_ = l_Lean_Expr_isApp(v___x_15_);
if (v___x_16_ == 0)
{
lean_dec_ref(v___x_15_);
lean_dec_ref(v_arg_12_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_17_ = l_Lean_Expr_appFnCleanup___redArg(v___x_15_);
v___x_18_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__2));
v___x_19_ = l_Lean_Expr_isConstOf(v___x_17_, v___x_18_);
lean_dec_ref(v___x_17_);
if (v___x_19_ == 0)
{
lean_dec_ref(v_arg_12_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = l_Lean_Expr_cleanupAnnotations(v_arg_12_);
v___x_21_ = l_Lean_Expr_isApp(v___x_20_);
if (v___x_21_ == 0)
{
lean_dec_ref(v___x_20_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_22_ = l_Lean_Expr_appFnCleanup___redArg(v___x_20_);
v___x_23_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__4));
v___x_24_ = l_Lean_Expr_isConstOf(v___x_22_, v___x_23_);
lean_dec_ref(v___x_22_);
return v___x_24_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum___boxed(lean_object* v_e_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_25_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNonnegIntNum(lean_object* v_e_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = l_Lean_Expr_cleanupAnnotations(v_e_31_);
v___x_33_ = l_Lean_Expr_isApp(v___x_32_);
if (v___x_33_ == 0)
{
lean_dec_ref(v___x_32_);
return v___x_33_;
}
else
{
lean_object* v_arg_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_arg_34_ = lean_ctor_get(v___x_32_, 1);
lean_inc_ref(v_arg_34_);
v___x_35_ = l_Lean_Expr_appFnCleanup___redArg(v___x_32_);
v___x_36_ = l_Lean_Expr_isApp(v___x_35_);
if (v___x_36_ == 0)
{
lean_dec_ref(v___x_35_);
lean_dec_ref(v_arg_34_);
return v___x_36_;
}
else
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = l_Lean_Expr_appFnCleanup___redArg(v___x_35_);
v___x_38_ = l_Lean_Expr_isApp(v___x_37_);
if (v___x_38_ == 0)
{
lean_dec_ref(v___x_37_);
lean_dec_ref(v_arg_34_);
return v___x_38_;
}
else
{
lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_39_ = l_Lean_Expr_appFnCleanup___redArg(v___x_37_);
v___x_40_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__2));
v___x_41_ = l_Lean_Expr_isConstOf(v___x_39_, v___x_40_);
lean_dec_ref(v___x_39_);
if (v___x_41_ == 0)
{
lean_dec_ref(v_arg_34_);
return v___x_41_;
}
else
{
lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_42_ = l_Lean_Expr_cleanupAnnotations(v_arg_34_);
v___x_43_ = l_Lean_Expr_isApp(v___x_42_);
if (v___x_43_ == 0)
{
lean_dec_ref(v___x_42_);
return v___x_43_;
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_44_ = l_Lean_Expr_appFnCleanup___redArg(v___x_42_);
v___x_45_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__1));
v___x_46_ = l_Lean_Expr_isConstOf(v___x_44_, v___x_45_);
lean_dec_ref(v___x_44_);
return v___x_46_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNonnegIntNum___boxed(lean_object* v_e_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntNum(lean_object* v_e_60_){
_start:
{
lean_object* v___x_61_; uint8_t v___x_62_; 
lean_inc_ref(v_e_60_);
v___x_61_ = l_Lean_Expr_cleanupAnnotations(v_e_60_);
v___x_62_ = l_Lean_Expr_isApp(v___x_61_);
if (v___x_62_ == 0)
{
uint8_t v___x_63_; 
lean_dec_ref(v___x_61_);
v___x_63_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_60_);
return v___x_63_;
}
else
{
lean_object* v_arg_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v_arg_64_ = lean_ctor_get(v___x_61_, 1);
lean_inc_ref(v_arg_64_);
v___x_65_ = l_Lean_Expr_appFnCleanup___redArg(v___x_61_);
v___x_66_ = l_Lean_Expr_isApp(v___x_65_);
if (v___x_66_ == 0)
{
uint8_t v___x_67_; 
lean_dec_ref(v___x_65_);
lean_dec_ref(v_arg_64_);
v___x_67_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_60_);
return v___x_67_;
}
else
{
lean_object* v_arg_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_arg_68_ = lean_ctor_get(v___x_65_, 1);
lean_inc_ref(v_arg_68_);
v___x_69_ = l_Lean_Expr_appFnCleanup___redArg(v___x_65_);
v___x_70_ = l_Lean_Expr_isApp(v___x_69_);
if (v___x_70_ == 0)
{
uint8_t v___x_71_; 
lean_dec_ref(v___x_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_64_);
v___x_71_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_60_);
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_72_ = l_Lean_Expr_appFnCleanup___redArg(v___x_69_);
v___x_73_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntNum___closed__2));
v___x_74_ = l_Lean_Expr_isConstOf(v___x_72_, v___x_73_);
lean_dec_ref(v___x_72_);
if (v___x_74_ == 0)
{
uint8_t v___x_75_; 
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_64_);
v___x_75_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_60_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
lean_dec_ref(v_e_60_);
v___x_76_ = l_Lean_Expr_cleanupAnnotations(v_arg_68_);
v___x_77_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntNum___closed__5));
v___x_78_ = l_Lean_Expr_isConstOf(v___x_76_, v___x_77_);
lean_dec_ref(v___x_76_);
if (v___x_78_ == 0)
{
lean_dec_ref(v_arg_64_);
return v___x_78_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_arg_64_);
return v___x_79_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntNum___boxed(lean_object* v_e_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNum(lean_object* v_e_83_){
_start:
{
uint8_t v___x_84_; 
lean_inc_ref(v_e_83_);
v___x_84_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_83_);
if (v___x_84_ == 0)
{
uint8_t v___x_85_; 
v___x_85_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_83_);
return v___x_85_;
}
else
{
lean_dec_ref(v_e_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNum___boxed(lean_object* v_e_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Lean_Meta_Grind_Arith_isNum(v_e_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object* v_e_92_){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatType___closed__1));
v___x_94_ = l_Lean_Expr_isConstOf(v_e_92_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatType___boxed(lean_object* v_e_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_Lean_Meta_Grind_Arith_isNatType(v_e_95_);
lean_dec_ref(v_e_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object* v_e_100_){
_start:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntType___closed__0));
v___x_102_ = l_Lean_Expr_isConstOf(v_e_100_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntType___boxed(lean_object* v_e_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Lean_Meta_Grind_Arith_isIntType(v_e_103_);
lean_dec_ref(v_e_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstAddNat(lean_object* v_e_112_){
_start:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = l_Lean_Expr_cleanupAnnotations(v_e_112_);
v___x_114_ = l_Lean_Expr_isApp(v___x_113_);
if (v___x_114_ == 0)
{
lean_dec_ref(v___x_113_);
return v___x_114_;
}
else
{
lean_object* v_arg_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v_arg_115_ = lean_ctor_get(v___x_113_, 1);
lean_inc_ref(v_arg_115_);
v___x_116_ = l_Lean_Expr_appFnCleanup___redArg(v___x_113_);
v___x_117_ = l_Lean_Expr_isApp(v___x_116_);
if (v___x_117_ == 0)
{
lean_dec_ref(v___x_116_);
lean_dec_ref(v_arg_115_);
return v___x_117_;
}
else
{
lean_object* v_arg_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_arg_118_ = lean_ctor_get(v___x_116_, 1);
lean_inc_ref(v_arg_118_);
v___x_119_ = l_Lean_Expr_appFnCleanup___redArg(v___x_116_);
v___x_120_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1));
v___x_121_ = l_Lean_Expr_isConstOf(v___x_119_, v___x_120_);
lean_dec_ref(v___x_119_);
if (v___x_121_ == 0)
{
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_arg_115_);
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = l_Lean_Meta_Grind_Arith_isNatType(v_arg_118_);
lean_dec_ref(v_arg_118_);
if (v___x_122_ == 0)
{
lean_dec_ref(v_arg_115_);
return v___x_122_;
}
else
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3));
v___x_124_ = l_Lean_Expr_isConstOf(v_arg_115_, v___x_123_);
lean_dec_ref(v_arg_115_);
return v___x_124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___boxed(lean_object* v_e_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Lean_Meta_Grind_Arith_isInstAddNat(v_e_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstLENat(lean_object* v_e_131_){
_start:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInstLENat___closed__1));
v___x_133_ = l_Lean_Expr_isConstOf(v_e_131_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___boxed(lean_object* v_e_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Lean_Meta_Grind_Arith_isInstLENat(v_e_134_);
lean_dec_ref(v_e_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f(lean_object* v_e_142_){
_start:
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = l_Lean_Expr_cleanupAnnotations(v_e_142_);
v___x_144_ = l_Lean_Expr_isApp(v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
lean_dec_ref(v___x_143_);
v___x_145_ = lean_box(0);
return v___x_145_;
}
else
{
lean_object* v_arg_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_arg_146_ = lean_ctor_get(v___x_143_, 1);
lean_inc_ref(v_arg_146_);
v___x_147_ = l_Lean_Expr_appFnCleanup___redArg(v___x_143_);
v___x_148_ = l_Lean_Expr_isApp(v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; 
lean_dec_ref(v___x_147_);
lean_dec_ref(v_arg_146_);
v___x_149_ = lean_box(0);
return v___x_149_;
}
else
{
lean_object* v_arg_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_arg_150_ = lean_ctor_get(v___x_147_, 1);
lean_inc_ref(v_arg_150_);
v___x_151_ = l_Lean_Expr_appFnCleanup___redArg(v___x_147_);
v___x_152_ = l_Lean_Expr_isApp(v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
lean_dec_ref(v___x_151_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_146_);
v___x_153_ = lean_box(0);
return v___x_153_;
}
else
{
lean_object* v_arg_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v_arg_154_ = lean_ctor_get(v___x_151_, 1);
lean_inc_ref(v_arg_154_);
v___x_155_ = l_Lean_Expr_appFnCleanup___redArg(v___x_151_);
v___x_156_ = l_Lean_Expr_isApp(v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
lean_dec_ref(v___x_155_);
lean_dec_ref(v_arg_154_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_146_);
v___x_157_ = lean_box(0);
return v___x_157_;
}
else
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = l_Lean_Expr_appFnCleanup___redArg(v___x_155_);
v___x_159_ = l_Lean_Expr_isApp(v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
lean_dec_ref(v___x_158_);
lean_dec_ref(v_arg_154_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_146_);
v___x_160_ = lean_box(0);
return v___x_160_;
}
else
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = l_Lean_Expr_appFnCleanup___redArg(v___x_158_);
v___x_162_ = l_Lean_Expr_isApp(v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
lean_dec_ref(v___x_161_);
lean_dec_ref(v_arg_154_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_146_);
v___x_163_ = lean_box(0);
return v___x_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_164_ = l_Lean_Expr_appFnCleanup___redArg(v___x_161_);
v___x_165_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2));
v___x_166_ = l_Lean_Expr_isConstOf(v___x_164_, v___x_165_);
lean_dec_ref(v___x_164_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
lean_dec_ref(v_arg_154_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_146_);
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
uint8_t v___x_168_; 
v___x_168_ = l_Lean_Meta_Grind_Arith_isInstAddNat(v_arg_154_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_146_);
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v_arg_150_);
lean_ctor_set(v___x_170_, 1, v_arg_146_);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
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
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatAdd(lean_object* v_e_172_){
_start:
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = l_Lean_Expr_cleanupAnnotations(v_e_172_);
v___x_174_ = l_Lean_Expr_isApp(v___x_173_);
if (v___x_174_ == 0)
{
lean_dec_ref(v___x_173_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = l_Lean_Expr_appFnCleanup___redArg(v___x_173_);
v___x_176_ = l_Lean_Expr_isApp(v___x_175_);
if (v___x_176_ == 0)
{
lean_dec_ref(v___x_175_);
return v___x_176_;
}
else
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = l_Lean_Expr_appFnCleanup___redArg(v___x_175_);
v___x_178_ = l_Lean_Expr_isApp(v___x_177_);
if (v___x_178_ == 0)
{
lean_dec_ref(v___x_177_);
return v___x_178_;
}
else
{
lean_object* v_arg_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_arg_179_ = lean_ctor_get(v___x_177_, 1);
lean_inc_ref(v_arg_179_);
v___x_180_ = l_Lean_Expr_appFnCleanup___redArg(v___x_177_);
v___x_181_ = l_Lean_Expr_isApp(v___x_180_);
if (v___x_181_ == 0)
{
lean_dec_ref(v___x_180_);
lean_dec_ref(v_arg_179_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = l_Lean_Expr_appFnCleanup___redArg(v___x_180_);
v___x_183_ = l_Lean_Expr_isApp(v___x_182_);
if (v___x_183_ == 0)
{
lean_dec_ref(v___x_182_);
lean_dec_ref(v_arg_179_);
return v___x_183_;
}
else
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = l_Lean_Expr_appFnCleanup___redArg(v___x_182_);
v___x_185_ = l_Lean_Expr_isApp(v___x_184_);
if (v___x_185_ == 0)
{
lean_dec_ref(v___x_184_);
lean_dec_ref(v_arg_179_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_186_ = l_Lean_Expr_appFnCleanup___redArg(v___x_184_);
v___x_187_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2));
v___x_188_ = l_Lean_Expr_isConstOf(v___x_186_, v___x_187_);
lean_dec_ref(v___x_186_);
if (v___x_188_ == 0)
{
lean_dec_ref(v_arg_179_);
return v___x_188_;
}
else
{
uint8_t v___x_189_; 
v___x_189_ = l_Lean_Meta_Grind_Arith_isInstAddNat(v_arg_179_);
return v___x_189_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd___boxed(lean_object* v_e_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Lean_Meta_Grind_Arith_isNatAdd(v_e_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f(lean_object* v_e_193_){
_start:
{
lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_194_ = l_Lean_Expr_cleanupAnnotations(v_e_193_);
v___x_195_ = l_Lean_Expr_isApp(v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_dec_ref(v___x_194_);
v___x_196_ = lean_box(0);
return v___x_196_;
}
else
{
lean_object* v_arg_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_arg_197_ = lean_ctor_get(v___x_194_, 1);
lean_inc_ref(v_arg_197_);
v___x_198_ = l_Lean_Expr_appFnCleanup___redArg(v___x_194_);
v___x_199_ = l_Lean_Expr_isApp(v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; 
lean_dec_ref(v___x_198_);
lean_dec_ref(v_arg_197_);
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = l_Lean_Expr_appFnCleanup___redArg(v___x_198_);
v___x_202_ = l_Lean_Expr_isApp(v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_dec_ref(v___x_201_);
lean_dec_ref(v_arg_197_);
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_201_);
v___x_205_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__2));
v___x_206_ = l_Lean_Expr_isConstOf(v___x_204_, v___x_205_);
lean_dec_ref(v___x_204_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
lean_dec_ref(v_arg_197_);
v___x_207_ = lean_box(0);
return v___x_207_;
}
else
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = l_Lean_Expr_cleanupAnnotations(v_arg_197_);
v___x_209_ = l_Lean_Expr_isApp(v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec_ref(v___x_208_);
v___x_210_ = lean_box(0);
return v___x_210_;
}
else
{
lean_object* v_arg_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_arg_211_ = lean_ctor_get(v___x_208_, 1);
lean_inc_ref(v_arg_211_);
v___x_212_ = l_Lean_Expr_appFnCleanup___redArg(v___x_208_);
v___x_213_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__4));
v___x_214_ = l_Lean_Expr_isConstOf(v___x_212_, v___x_213_);
lean_dec_ref(v___x_212_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
lean_dec_ref(v_arg_211_);
v___x_215_ = lean_box(0);
return v___x_215_;
}
else
{
if (lean_obj_tag(v_arg_211_) == 9)
{
lean_object* v_a_216_; 
v_a_216_ = lean_ctor_get(v_arg_211_, 0);
lean_inc_ref(v_a_216_);
lean_dec_ref_known(v_arg_211_, 1);
if (lean_obj_tag(v_a_216_) == 0)
{
lean_object* v_val_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
v_val_217_ = lean_ctor_get(v_a_216_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v_a_216_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v_a_216_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_val_217_);
lean_dec(v_a_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set_tag(v___x_219_, 1);
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_val_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
else
{
lean_object* v___x_225_; 
lean_dec_ref(v_a_216_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
}
else
{
lean_object* v___x_226_; 
lean_dec_ref(v_arg_211_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isArithTerm(lean_object* v_e_267_){
_start:
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = l_Lean_Expr_cleanupAnnotations(v_e_267_);
v___x_269_ = l_Lean_Expr_isApp(v___x_268_);
if (v___x_269_ == 0)
{
lean_dec_ref(v___x_268_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_268_);
v___x_271_ = l_Lean_Expr_isApp(v___x_270_);
if (v___x_271_ == 0)
{
lean_dec_ref(v___x_270_);
return v___x_271_;
}
else
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = l_Lean_Expr_appFnCleanup___redArg(v___x_270_);
v___x_273_ = l_Lean_Expr_isApp(v___x_272_);
if (v___x_273_ == 0)
{
lean_dec_ref(v___x_272_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = l_Lean_Expr_appFnCleanup___redArg(v___x_272_);
v___x_275_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__2));
v___x_276_ = l_Lean_Expr_isConstOf(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__5));
v___x_278_ = l_Lean_Expr_isConstOf(v___x_274_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__2));
v___x_280_ = l_Lean_Expr_isConstOf(v___x_274_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntNum___closed__2));
v___x_282_ = l_Lean_Expr_isConstOf(v___x_274_, v___x_281_);
if (v___x_282_ == 0)
{
uint8_t v___x_283_; 
v___x_283_ = l_Lean_Expr_isApp(v___x_274_);
if (v___x_283_ == 0)
{
lean_dec_ref(v___x_274_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = l_Lean_Expr_appFnCleanup___redArg(v___x_274_);
v___x_285_ = l_Lean_Expr_isApp(v___x_284_);
if (v___x_285_ == 0)
{
lean_dec_ref(v___x_284_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = l_Lean_Expr_appFnCleanup___redArg(v___x_284_);
v___x_287_ = l_Lean_Expr_isApp(v___x_286_);
if (v___x_287_ == 0)
{
lean_dec_ref(v___x_286_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = l_Lean_Expr_appFnCleanup___redArg(v___x_286_);
v___x_289_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__8));
v___x_290_ = l_Lean_Expr_isConstOf(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__11));
v___x_292_ = l_Lean_Expr_isConstOf(v___x_288_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__14));
v___x_294_ = l_Lean_Expr_isConstOf(v___x_288_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__17));
v___x_296_ = l_Lean_Expr_isConstOf(v___x_288_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__20));
v___x_298_ = l_Lean_Expr_isConstOf(v___x_288_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__23));
v___x_300_ = l_Lean_Expr_isConstOf(v___x_288_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2));
v___x_302_ = l_Lean_Expr_isConstOf(v___x_288_, v___x_301_);
lean_dec_ref(v___x_288_);
return v___x_302_;
}
else
{
lean_dec_ref(v___x_288_);
return v___x_300_;
}
}
else
{
lean_dec_ref(v___x_288_);
return v___x_298_;
}
}
else
{
lean_dec_ref(v___x_288_);
return v___x_296_;
}
}
else
{
lean_dec_ref(v___x_288_);
return v___x_294_;
}
}
else
{
lean_dec_ref(v___x_288_);
return v___x_292_;
}
}
else
{
lean_dec_ref(v___x_288_);
return v___x_290_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_274_);
return v___x_282_;
}
}
else
{
lean_dec_ref(v___x_274_);
return v___x_280_;
}
}
else
{
lean_dec_ref(v___x_274_);
return v___x_278_;
}
}
else
{
lean_dec_ref(v___x_274_);
return v___x_276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___boxed(lean_object* v_e_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Lean_Meta_Grind_Arith_isArithTerm(v_e_303_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object* v_e_306_){
_start:
{
uint8_t v___x_307_; 
lean_inc_ref(v_e_306_);
v___x_307_ = l_Lean_Meta_Grind_Arith_isArithTerm(v_e_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_MessageData_ofExpr(v_e_306_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = l_Lean_MessageData_ofExpr(v_e_306_);
v___x_310_ = l_Lean_aquote(v___x_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_gcdExt_spec__0(lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_nat_to_int(v_a_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_gcdExt___closed__0(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_nat_to_int(v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object* v_a_315_, lean_object* v_b_316_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_gcdExt___closed__0, &l_Lean_Meta_Grind_Arith_gcdExt___closed__0_once, _init_l_Lean_Meta_Grind_Arith_gcdExt___closed__0);
v___x_318_ = lean_int_dec_eq(v_b_316_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_snd_321_; lean_object* v_fst_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_341_; 
v___x_319_ = lean_int_emod(v_a_315_, v_b_316_);
v___x_320_ = l_Lean_Meta_Grind_Arith_gcdExt(v_b_316_, v___x_319_);
lean_dec(v___x_319_);
v_snd_321_ = lean_ctor_get(v___x_320_, 1);
v_fst_322_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_341_ == 0)
{
v___x_324_ = v___x_320_;
v_isShared_325_ = v_isSharedCheck_341_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_snd_321_);
lean_inc(v_fst_322_);
lean_dec(v___x_320_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_341_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v_fst_326_; lean_object* v_snd_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_340_; 
v_fst_326_ = lean_ctor_get(v_snd_321_, 0);
v_snd_327_ = lean_ctor_get(v_snd_321_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_snd_321_);
if (v_isSharedCheck_340_ == 0)
{
v___x_329_ = v_snd_321_;
v_isShared_330_ = v_isSharedCheck_340_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_snd_327_);
lean_inc(v_fst_326_);
lean_dec(v_snd_321_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_340_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_331_ = lean_int_ediv(v_a_315_, v_b_316_);
v___x_332_ = lean_int_mul(v___x_331_, v_snd_327_);
lean_dec(v___x_331_);
v___x_333_ = lean_int_sub(v_fst_326_, v___x_332_);
lean_dec(v___x_332_);
lean_dec(v_fst_326_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v___x_333_);
lean_ctor_set(v___x_329_, 0, v_snd_327_);
v___x_335_ = v___x_329_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_snd_327_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_339_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v___x_335_);
v___x_337_ = v___x_324_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_fst_322_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v___x_335_);
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
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___y_345_; uint8_t v___x_348_; 
v___x_342_ = lean_nat_abs(v_a_315_);
v___x_343_ = lean_nat_to_int(v___x_342_);
v___x_348_ = lean_int_dec_eq(v_a_315_, v___x_317_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
v___x_349_ = lean_int_ediv(v_a_315_, v___x_343_);
v___y_345_ = v___x_349_;
goto v___jp_344_;
}
else
{
v___y_345_ = v___x_317_;
goto v___jp_344_;
}
v___jp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___y_345_);
lean_ctor_set(v___x_346_, 1, v___x_317_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_343_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt___boxed(lean_object* v_a_350_, lean_object* v_b_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Meta_Grind_Arith_gcdExt(v_a_350_, v_b_351_);
lean_dec(v_b_351_);
lean_dec(v_a_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object* v_a_353_, lean_object* v_sz_354_){
_start:
{
lean_object* v_size_355_; uint8_t v___x_356_; 
v_size_355_ = lean_ctor_get(v_a_353_, 2);
v___x_356_ = lean_nat_dec_lt(v_sz_354_, v_size_355_);
if (v___x_356_ == 0)
{
return v_a_353_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_PersistentArray_pop___redArg(v_a_353_);
v_a_353_ = v___x_357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink___boxed(lean_object* v_a_359_, lean_object* v_sz_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Meta_Grind_Arith_shrink(v_a_359_, v_sz_360_);
lean_dec(v_sz_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go_spec__0(lean_object* v_a_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_nat_to_int(v_a_362_);
v___x_364_ = l_Rat_ofInt(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go_spec__0(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(lean_object* v_sz_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_size_369_; uint8_t v___x_370_; 
v_size_369_ = lean_ctor_get(v_a_368_, 2);
v___x_370_ = lean_nat_dec_lt(v_size_369_, v_sz_367_);
if (v___x_370_ == 0)
{
return v_a_368_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0);
v___x_372_ = l_Lean_PersistentArray_push___redArg(v_a_368_, v___x_371_);
v_a_368_ = v___x_372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___boxed(lean_object* v_sz_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(v_sz_374_, v_a_375_);
lean_dec(v_sz_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize(lean_object* v_a_377_, lean_object* v_sz_378_){
_start:
{
lean_object* v_size_379_; uint8_t v___x_380_; 
v_size_379_ = lean_ctor_get(v_a_377_, 2);
v___x_380_ = lean_nat_dec_lt(v_sz_378_, v_size_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
v___x_381_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(v_sz_378_, v_a_377_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_Grind_Arith_shrink(v_a_377_, v_sz_378_);
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize___boxed(lean_object* v_a_383_, lean_object* v_sz_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Meta_Grind_Arith_resize(v_a_383_, v_sz_384_);
lean_dec(v_sz_384_);
return v_res_385_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(lean_object* v_c_386_){
_start:
{
size_t v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; 
v___x_387_ = lean_ptr_addr(v_c_386_);
v___x_388_ = lean_usize_to_uint64(v___x_387_);
v___x_389_ = 2ULL;
v___x_390_ = lean_uint64_shift_right(v___x_388_, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg___boxed(lean_object* v_c_391_){
_start:
{
uint64_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(v_c_391_);
lean_dec(v_c_391_);
v_r_393_ = lean_box_uint64(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(lean_object* v_00_u03b1_394_, lean_object* v_c_395_){
_start:
{
size_t v___x_396_; uint64_t v___x_397_; uint64_t v___x_398_; uint64_t v___x_399_; 
v___x_396_ = lean_ptr_addr(v_c_395_);
v___x_397_ = lean_usize_to_uint64(v___x_396_);
v___x_398_ = 2ULL;
v___x_399_ = lean_uint64_shift_right(v___x_397_, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___boxed(lean_object* v_00_u03b1_400_, lean_object* v_c_401_){
_start:
{
uint64_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(v_00_u03b1_400_, v_c_401_);
lean_dec(v_c_401_);
v_r_403_ = lean_box_uint64(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(uint64_t v_a_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
uint8_t v___x_406_; 
v___x_406_ = 0;
return v___x_406_;
}
else
{
lean_object* v_key_407_; lean_object* v_tail_408_; uint64_t v___x_409_; uint8_t v___x_410_; 
v_key_407_ = lean_ctor_get(v_x_405_, 0);
v_tail_408_ = lean_ctor_get(v_x_405_, 2);
v___x_409_ = lean_unbox_uint64(v_key_407_);
v___x_410_ = lean_uint64_dec_eq(v___x_409_, v_a_404_);
if (v___x_410_ == 0)
{
v_x_405_ = v_tail_408_;
goto _start;
}
else
{
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg___boxed(lean_object* v_a_412_, lean_object* v_x_413_){
_start:
{
uint64_t v_a_boxed_414_; uint8_t v_res_415_; lean_object* v_r_416_; 
v_a_boxed_414_ = lean_unbox_uint64(v_a_412_);
lean_dec_ref(v_a_412_);
v_res_415_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_boxed_414_, v_x_413_);
lean_dec(v_x_413_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(lean_object* v_m_417_, uint64_t v_a_418_){
_start:
{
lean_object* v_buckets_419_; lean_object* v___x_420_; uint64_t v___x_421_; uint64_t v___x_422_; uint64_t v_fold_423_; uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_buckets_419_ = lean_ctor_get(v_m_417_, 1);
v___x_420_ = lean_array_get_size(v_buckets_419_);
v___x_421_ = 32ULL;
v___x_422_ = lean_uint64_shift_right(v_a_418_, v___x_421_);
v_fold_423_ = lean_uint64_xor(v_a_418_, v___x_422_);
v___x_424_ = 16ULL;
v___x_425_ = lean_uint64_shift_right(v_fold_423_, v___x_424_);
v___x_426_ = lean_uint64_xor(v_fold_423_, v___x_425_);
v___x_427_ = lean_uint64_to_usize(v___x_426_);
v___x_428_ = lean_usize_of_nat(v___x_420_);
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_sub(v___x_428_, v___x_429_);
v___x_431_ = lean_usize_land(v___x_427_, v___x_430_);
v___x_432_ = lean_array_uget_borrowed(v_buckets_419_, v___x_431_);
v___x_433_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_418_, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg___boxed(lean_object* v_m_434_, lean_object* v_a_435_){
_start:
{
uint64_t v_a_boxed_436_; uint8_t v_res_437_; lean_object* v_r_438_; 
v_a_boxed_436_ = lean_unbox_uint64(v_a_435_);
lean_dec_ref(v_a_435_);
v_res_437_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_m_434_, v_a_boxed_436_);
lean_dec_ref(v_m_434_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
return v_x_439_;
}
else
{
lean_object* v_key_441_; lean_object* v_value_442_; lean_object* v_tail_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_467_; 
v_key_441_ = lean_ctor_get(v_x_440_, 0);
v_value_442_ = lean_ctor_get(v_x_440_, 1);
v_tail_443_ = lean_ctor_get(v_x_440_, 2);
v_isSharedCheck_467_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_467_ == 0)
{
v___x_445_ = v_x_440_;
v_isShared_446_ = v_isSharedCheck_467_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_tail_443_);
lean_inc(v_value_442_);
lean_inc(v_key_441_);
lean_dec(v_x_440_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_467_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v_fold_452_; uint64_t v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; size_t v___x_456_; size_t v___x_457_; size_t v___x_458_; size_t v___x_459_; size_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_447_ = lean_array_get_size(v_x_439_);
v___x_448_ = 32ULL;
v___x_449_ = lean_unbox_uint64(v_key_441_);
v___x_450_ = lean_uint64_shift_right(v___x_449_, v___x_448_);
v___x_451_ = lean_unbox_uint64(v_key_441_);
v_fold_452_ = lean_uint64_xor(v___x_451_, v___x_450_);
v___x_453_ = 16ULL;
v___x_454_ = lean_uint64_shift_right(v_fold_452_, v___x_453_);
v___x_455_ = lean_uint64_xor(v_fold_452_, v___x_454_);
v___x_456_ = lean_uint64_to_usize(v___x_455_);
v___x_457_ = lean_usize_of_nat(v___x_447_);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_sub(v___x_457_, v___x_458_);
v___x_460_ = lean_usize_land(v___x_456_, v___x_459_);
v___x_461_ = lean_array_uget_borrowed(v_x_439_, v___x_460_);
lean_inc(v___x_461_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 2, v___x_461_);
v___x_463_ = v___x_445_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_key_441_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_value_442_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v___x_461_);
v___x_463_ = v_reuseFailAlloc_466_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; 
v___x_464_ = lean_array_uset(v_x_439_, v___x_460_, v___x_463_);
v_x_439_ = v___x_464_;
v_x_440_ = v_tail_443_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(lean_object* v_i_468_, lean_object* v_source_469_, lean_object* v_target_470_){
_start:
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = lean_array_get_size(v_source_469_);
v___x_472_ = lean_nat_dec_lt(v_i_468_, v___x_471_);
if (v___x_472_ == 0)
{
lean_dec_ref(v_source_469_);
lean_dec(v_i_468_);
return v_target_470_;
}
else
{
lean_object* v_es_473_; lean_object* v___x_474_; lean_object* v_source_475_; lean_object* v_target_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_es_473_ = lean_array_fget(v_source_469_, v_i_468_);
v___x_474_ = lean_box(0);
v_source_475_ = lean_array_fset(v_source_469_, v_i_468_, v___x_474_);
v_target_476_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(v_target_470_, v_es_473_);
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = lean_nat_add(v_i_468_, v___x_477_);
lean_dec(v_i_468_);
v_i_468_ = v___x_478_;
v_source_469_ = v_source_475_;
v_target_470_ = v_target_476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(lean_object* v_data_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_nbuckets_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_481_ = lean_array_get_size(v_data_480_);
v___x_482_ = lean_unsigned_to_nat(2u);
v_nbuckets_483_ = lean_nat_mul(v___x_481_, v___x_482_);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = lean_box(0);
v___x_486_ = lean_mk_array(v_nbuckets_483_, v___x_485_);
v___x_487_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(v___x_484_, v_data_480_, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(lean_object* v_m_488_, uint64_t v_a_489_, lean_object* v_b_490_){
_start:
{
lean_object* v_size_491_; lean_object* v_buckets_492_; lean_object* v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v_fold_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v_bkt_505_; uint8_t v___x_506_; 
v_size_491_ = lean_ctor_get(v_m_488_, 0);
v_buckets_492_ = lean_ctor_get(v_m_488_, 1);
v___x_493_ = lean_array_get_size(v_buckets_492_);
v___x_494_ = 32ULL;
v___x_495_ = lean_uint64_shift_right(v_a_489_, v___x_494_);
v_fold_496_ = lean_uint64_xor(v_a_489_, v___x_495_);
v___x_497_ = 16ULL;
v___x_498_ = lean_uint64_shift_right(v_fold_496_, v___x_497_);
v___x_499_ = lean_uint64_xor(v_fold_496_, v___x_498_);
v___x_500_ = lean_uint64_to_usize(v___x_499_);
v___x_501_ = lean_usize_of_nat(v___x_493_);
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_sub(v___x_501_, v___x_502_);
v___x_504_ = lean_usize_land(v___x_500_, v___x_503_);
v_bkt_505_ = lean_array_uget_borrowed(v_buckets_492_, v___x_504_);
v___x_506_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_489_, v_bkt_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_528_; 
lean_inc_ref(v_buckets_492_);
lean_inc(v_size_491_);
v_isSharedCheck_528_ = !lean_is_exclusive(v_m_488_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; lean_object* v_unused_530_; 
v_unused_529_ = lean_ctor_get(v_m_488_, 1);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_m_488_, 0);
lean_dec(v_unused_530_);
v___x_508_ = v_m_488_;
v_isShared_509_ = v_isSharedCheck_528_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_m_488_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_528_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v_size_x27_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_buckets_x27_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v_size_x27_511_ = lean_nat_add(v_size_491_, v___x_510_);
lean_dec(v_size_491_);
v___x_512_ = lean_box_uint64(v_a_489_);
lean_inc(v_bkt_505_);
v___x_513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v_b_490_);
lean_ctor_set(v___x_513_, 2, v_bkt_505_);
v_buckets_x27_514_ = lean_array_uset(v_buckets_492_, v___x_504_, v___x_513_);
v___x_515_ = lean_unsigned_to_nat(4u);
v___x_516_ = lean_nat_mul(v_size_x27_511_, v___x_515_);
v___x_517_ = lean_unsigned_to_nat(3u);
v___x_518_ = lean_nat_div(v___x_516_, v___x_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_array_get_size(v_buckets_x27_514_);
v___x_520_ = lean_nat_dec_le(v___x_518_, v___x_519_);
lean_dec(v___x_518_);
if (v___x_520_ == 0)
{
lean_object* v_val_521_; lean_object* v___x_523_; 
v_val_521_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(v_buckets_x27_514_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_val_521_);
lean_ctor_set(v___x_508_, 0, v_size_x27_511_);
v___x_523_ = v___x_508_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_size_x27_511_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_val_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
else
{
lean_object* v___x_526_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_buckets_x27_514_);
lean_ctor_set(v___x_508_, 0, v_size_x27_511_);
v___x_526_ = v___x_508_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_size_x27_511_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_buckets_x27_514_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_dec(v_b_490_);
return v_m_488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg___boxed(lean_object* v_m_531_, lean_object* v_a_532_, lean_object* v_b_533_){
_start:
{
uint64_t v_a_boxed_534_; lean_object* v_res_535_; 
v_a_boxed_534_ = lean_unbox_uint64(v_a_532_);
lean_dec_ref(v_a_532_);
v_res_535_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_m_531_, v_a_boxed_534_, v_b_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(lean_object* v_c_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_visited_538_; lean_object* v_found_539_; size_t v___x_540_; uint64_t v___x_541_; uint64_t v___x_542_; uint64_t v_addr_543_; uint8_t v___x_544_; 
v_visited_538_ = lean_ctor_get(v_a_537_, 0);
v_found_539_ = lean_ctor_get(v_a_537_, 1);
v___x_540_ = lean_ptr_addr(v_c_536_);
v___x_541_ = lean_usize_to_uint64(v___x_540_);
v___x_542_ = 2ULL;
v_addr_543_ = lean_uint64_shift_right(v___x_541_, v___x_542_);
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_visited_538_, v_addr_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_555_; 
lean_inc(v_found_539_);
lean_inc_ref(v_visited_538_);
v_isSharedCheck_555_ = !lean_is_exclusive(v_a_537_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; lean_object* v_unused_557_; 
v_unused_556_ = lean_ctor_get(v_a_537_, 1);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_a_537_, 0);
lean_dec(v_unused_557_);
v___x_546_ = v_a_537_;
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
else
{
lean_dec(v_a_537_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_548_ = lean_box(0);
v___x_549_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_visited_538_, v_addr_543_, v___x_548_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_549_);
v___x_551_ = v___x_546_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_found_539_);
v___x_551_ = v_reuseFailAlloc_554_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_box(v___x_544_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v___x_551_);
return v___x_553_;
}
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_box(v___x_544_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v_a_537_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg___boxed(lean_object* v_c_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(v_c_560_, v_a_561_);
lean_dec(v_c_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(lean_object* v_00_u03b1_563_, lean_object* v_c_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(v_c_564_, v_a_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___boxed(lean_object* v_00_u03b1_568_, lean_object* v_c_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(v_00_u03b1_568_, v_c_569_, v_a_570_, v_a_571_);
lean_dec(v_a_570_);
lean_dec(v_c_569_);
return v_res_572_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(lean_object* v_00_u03b2_573_, lean_object* v_m_574_, uint64_t v_a_575_){
_start:
{
uint8_t v___x_576_; 
v___x_576_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_m_574_, v_a_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___boxed(lean_object* v_00_u03b2_577_, lean_object* v_m_578_, lean_object* v_a_579_){
_start:
{
uint64_t v_a_boxed_580_; uint8_t v_res_581_; lean_object* v_r_582_; 
v_a_boxed_580_ = lean_unbox_uint64(v_a_579_);
lean_dec_ref(v_a_579_);
v_res_581_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(v_00_u03b2_577_, v_m_578_, v_a_boxed_580_);
lean_dec_ref(v_m_578_);
v_r_582_ = lean_box(v_res_581_);
return v_r_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(lean_object* v_00_u03b2_583_, lean_object* v_m_584_, uint64_t v_a_585_, lean_object* v_b_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_m_584_, v_a_585_, v_b_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___boxed(lean_object* v_00_u03b2_588_, lean_object* v_m_589_, lean_object* v_a_590_, lean_object* v_b_591_){
_start:
{
uint64_t v_a_boxed_592_; lean_object* v_res_593_; 
v_a_boxed_592_ = lean_unbox_uint64(v_a_590_);
lean_dec_ref(v_a_590_);
v_res_593_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(v_00_u03b2_588_, v_m_589_, v_a_boxed_592_, v_b_591_);
return v_res_593_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(lean_object* v_00_u03b2_594_, uint64_t v_a_595_, lean_object* v_x_596_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_595_, v_x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___boxed(lean_object* v_00_u03b2_598_, lean_object* v_a_599_, lean_object* v_x_600_){
_start:
{
uint64_t v_a_boxed_601_; uint8_t v_res_602_; lean_object* v_r_603_; 
v_a_boxed_601_ = lean_unbox_uint64(v_a_599_);
lean_dec_ref(v_a_599_);
v_res_602_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(v_00_u03b2_598_, v_a_boxed_601_, v_x_600_);
lean_dec(v_x_600_);
v_r_603_ = lean_box(v_res_602_);
return v_r_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2(lean_object* v_00_u03b2_604_, lean_object* v_data_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(v_data_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_607_, lean_object* v_i_608_, lean_object* v_source_609_, lean_object* v_target_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(v_i_608_, v_source_609_, v_target_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_612_, lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(v_x_613_, v_x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(lean_object* v_fvarId_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_visited_618_; lean_object* v_found_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_629_; 
v_visited_618_ = lean_ctor_get(v_a_617_, 0);
v_found_619_ = lean_ctor_get(v_a_617_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_a_617_);
if (v_isSharedCheck_629_ == 0)
{
v___x_621_ = v_a_617_;
v_isShared_622_ = v_isSharedCheck_629_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_found_619_);
lean_inc(v_visited_618_);
lean_dec(v_a_617_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_629_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_623_ = lean_box(0);
v___x_624_ = l_Lean_FVarIdSet_insert(v_found_619_, v_fvarId_616_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_624_);
v___x_626_ = v___x_621_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_visited_618_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___x_624_);
v___x_626_ = v_reuseFailAlloc_628_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_623_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(lean_object* v_fvarId_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(v_fvarId_630_, v_a_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___boxed(lean_object* v_fvarId_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(v_fvarId_634_, v_a_635_, v_a_636_);
lean_dec(v_a_635_);
return v_res_637_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_box(0);
v___x_639_ = lean_unsigned_to_nat(16u);
v___x_640_ = lean_mk_array(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_box(1);
v___x_645_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run(lean_object* v_x_647_, lean_object* v_decVars_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v_snd_651_; lean_object* v_found_652_; 
v___x_649_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2);
v___x_650_ = lean_apply_2(v_x_647_, v_decVars_648_, v___x_649_);
v_snd_651_ = lean_ctor_get(v___x_650_, 1);
lean_inc(v_snd_651_);
lean_dec_ref(v___x_650_);
v_found_652_ = lean_ctor_get(v_snd_651_, 1);
lean_inc(v_found_652_);
lean_dec(v_snd_651_);
return v_found_652_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________(void){
_start:
{
uint8_t v___x_653_; 
v___x_653_ = 1;
return v___x_653_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_box(0);
v___x_702_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20));
v___x_703_ = l_Lean_mkConst(v___x_702_, v___x_701_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent(void){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21, &l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21_once, _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21);
return v___x_704_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object* v_parent_x3f_705_){
_start:
{
if (lean_obj_tag(v_parent_x3f_705_) == 0)
{
uint8_t v___x_706_; 
v___x_706_ = 0;
return v___x_706_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_val_707_ = lean_ctor_get(v_parent_x3f_705_, 0);
v___x_708_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_709_ = lean_expr_eqv(v_val_707_, v___x_708_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent___boxed(lean_object* v_parent_x3f_710_){
_start:
{
uint8_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_710_);
lean_dec(v_parent_x3f_710_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___lam__0(lean_object* v_getCoeff_713_, lean_object* v___x_714_, lean_object* v_c_715_, lean_object* v_____s_716_){
_start:
{
lean_object* v_fst_717_; lean_object* v_snd_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_736_; 
v_fst_717_ = lean_ctor_get(v_____s_716_, 0);
v_snd_718_ = lean_ctor_get(v_____s_716_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v_____s_716_);
if (v_isSharedCheck_736_ == 0)
{
v___x_720_ = v_____s_716_;
v_isShared_721_ = v_isSharedCheck_736_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_snd_718_);
lean_inc(v_fst_717_);
lean_dec(v_____s_716_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_736_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_b_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
lean_inc(v_c_715_);
v_b_722_ = lean_apply_1(v_getCoeff_713_, v_c_715_);
v___x_723_ = lean_nat_to_int(v___x_714_);
v___x_724_ = lean_int_dec_eq(v_b_722_, v___x_723_);
lean_dec(v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_726_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v_c_715_);
lean_ctor_set(v___x_720_, 0, v_b_722_);
v___x_726_ = v___x_720_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_b_722_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_c_715_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v_todo_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_todo_727_ = lean_array_push(v_snd_718_, v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_fst_717_);
lean_ctor_set(v___x_728_, 1, v_todo_727_);
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
else
{
lean_object* v_cs_x27_731_; lean_object* v___x_733_; 
lean_dec(v_b_722_);
v_cs_x27_731_ = l_Lean_PersistentArray_push___redArg(v_fst_717_, v_c_715_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v_cs_x27_731_);
v___x_733_ = v___x_720_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_cs_x27_731_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_snd_718_);
v___x_733_ = v_reuseFailAlloc_735_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_unsigned_to_nat(32u);
v___x_757_ = lean_mk_empty_array_with_capacity(v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11(void){
_start:
{
size_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_cs_x27_764_; 
v___x_759_ = ((size_t)5ULL);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_unsigned_to_nat(32u);
v___x_762_ = lean_mk_empty_array_with_capacity(v___x_761_);
v___x_763_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__10, &l_Lean_Meta_Grind_Arith_split___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10);
v_cs_x27_764_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_764_, 0, v___x_763_);
lean_ctor_set(v_cs_x27_764_, 1, v___x_762_);
lean_ctor_set(v_cs_x27_764_, 2, v___x_760_);
lean_ctor_set(v_cs_x27_764_, 3, v___x_760_);
lean_ctor_set_usize(v_cs_x27_764_, 4, v___x_759_);
return v_cs_x27_764_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13(void){
_start:
{
lean_object* v_todo_767_; lean_object* v_cs_x27_768_; lean_object* v___x_769_; 
v_todo_767_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___redArg___closed__12));
v_cs_x27_768_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__11, &l_Lean_Meta_Grind_Arith_split___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v_cs_x27_768_);
lean_ctor_set(v___x_769_, 1, v_todo_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg(lean_object* v_cs_770_, lean_object* v_getCoeff_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v___x_772_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___redArg___closed__9));
v___x_773_ = lean_unsigned_to_nat(0u);
v___f_774_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_split___redArg___lam__0), 4, 2);
lean_closure_set(v___f_774_, 0, v_getCoeff_771_);
lean_closure_set(v___f_774_, 1, v___x_773_);
v___x_775_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__13, &l_Lean_Meta_Grind_Arith_split___redArg___closed__13_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13);
v___x_776_ = l_Lean_PersistentArray_forIn___redArg(v___x_772_, v_cs_770_, v___x_775_, v___f_774_);
v_fst_777_ = lean_ctor_get(v___x_776_, 0);
v_snd_778_ = lean_ctor_get(v___x_776_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_776_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_snd_778_);
lean_inc(v_fst_777_);
lean_dec(v___x_776_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_fst_777_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_snd_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___boxed(lean_object* v_cs_786_, lean_object* v_getCoeff_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Meta_Grind_Arith_split___redArg(v_cs_786_, v_getCoeff_787_);
lean_dec_ref(v_cs_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split(lean_object* v_00_u03b1_789_, lean_object* v_cs_790_, lean_object* v_getCoeff_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_Meta_Grind_Arith_split___redArg(v_cs_790_, v_getCoeff_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___boxed(lean_object* v_00_u03b1_793_, lean_object* v_cs_794_, lean_object* v_getCoeff_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Meta_Grind_Arith_split(v_00_u03b1_793_, v_cs_794_, v_getCoeff_795_);
lean_dec_ref(v_cs_794_);
return v_res_796_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________ = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________();
l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent = _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
}
#ifdef __cplusplus
}
#endif
