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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
uint8_t l_Lean_Meta_Grind_Arith_isNatNum(lean_object* v_e_9_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isNatNum_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_9_ = stack[0].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_9_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum___boxed(lean_object* v_e_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_isNonnegIntNum(lean_object* v_e_32_){
_start:
{
lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_33_ = l_Lean_Expr_cleanupAnnotations(v_e_32_);
v___x_34_ = l_Lean_Expr_isApp(v___x_33_);
if (v___x_34_ == 0)
{
lean_dec_ref(v___x_33_);
return v___x_34_;
}
else
{
lean_object* v_arg_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_arg_35_ = lean_ctor_get(v___x_33_, 1);
lean_inc_ref(v_arg_35_);
v___x_36_ = l_Lean_Expr_appFnCleanup___redArg(v___x_33_);
v___x_37_ = l_Lean_Expr_isApp(v___x_36_);
if (v___x_37_ == 0)
{
lean_dec_ref(v___x_36_);
lean_dec_ref(v_arg_35_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = l_Lean_Expr_appFnCleanup___redArg(v___x_36_);
v___x_39_ = l_Lean_Expr_isApp(v___x_38_);
if (v___x_39_ == 0)
{
lean_dec_ref(v___x_38_);
lean_dec_ref(v_arg_35_);
return v___x_39_;
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_40_ = l_Lean_Expr_appFnCleanup___redArg(v___x_38_);
v___x_41_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__2));
v___x_42_ = l_Lean_Expr_isConstOf(v___x_40_, v___x_41_);
lean_dec_ref(v___x_40_);
if (v___x_42_ == 0)
{
lean_dec_ref(v_arg_35_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = l_Lean_Expr_cleanupAnnotations(v_arg_35_);
v___x_44_ = l_Lean_Expr_isApp(v___x_43_);
if (v___x_44_ == 0)
{
lean_dec_ref(v___x_43_);
return v___x_44_;
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_45_ = l_Lean_Expr_appFnCleanup___redArg(v___x_43_);
v___x_46_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNonnegIntNum___closed__1));
v___x_47_ = l_Lean_Expr_isConstOf(v___x_45_, v___x_46_);
lean_dec_ref(v___x_45_);
return v___x_47_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isNonnegIntNum_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_32_ = stack[0].m_obj;
uint8_t v_res_48_;
v_res_48_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_32_);
stack->m_num = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNonnegIntNum___boxed(lean_object* v_e_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_49_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_isIntNum(lean_object* v_e_62_){
_start:
{
lean_object* v___x_63_; uint8_t v___x_64_; 
lean_inc_ref(v_e_62_);
v___x_63_ = l_Lean_Expr_cleanupAnnotations(v_e_62_);
v___x_64_ = l_Lean_Expr_isApp(v___x_63_);
if (v___x_64_ == 0)
{
uint8_t v___x_65_; 
lean_dec_ref(v___x_63_);
v___x_65_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_62_);
return v___x_65_;
}
else
{
lean_object* v_arg_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_arg_66_ = lean_ctor_get(v___x_63_, 1);
lean_inc_ref(v_arg_66_);
v___x_67_ = l_Lean_Expr_appFnCleanup___redArg(v___x_63_);
v___x_68_ = l_Lean_Expr_isApp(v___x_67_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
lean_dec_ref(v___x_67_);
lean_dec_ref(v_arg_66_);
v___x_69_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_62_);
return v___x_69_;
}
else
{
lean_object* v_arg_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v_arg_70_ = lean_ctor_get(v___x_67_, 1);
lean_inc_ref(v_arg_70_);
v___x_71_ = l_Lean_Expr_appFnCleanup___redArg(v___x_67_);
v___x_72_ = l_Lean_Expr_isApp(v___x_71_);
if (v___x_72_ == 0)
{
uint8_t v___x_73_; 
lean_dec_ref(v___x_71_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_66_);
v___x_73_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_62_);
return v___x_73_;
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = l_Lean_Expr_appFnCleanup___redArg(v___x_71_);
v___x_75_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntNum___closed__2));
v___x_76_ = l_Lean_Expr_isConstOf(v___x_74_, v___x_75_);
lean_dec_ref(v___x_74_);
if (v___x_76_ == 0)
{
uint8_t v___x_77_; 
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_66_);
v___x_77_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_e_62_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
lean_dec_ref(v_e_62_);
v___x_78_ = l_Lean_Expr_cleanupAnnotations(v_arg_70_);
v___x_79_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntNum___closed__5));
v___x_80_ = l_Lean_Expr_isConstOf(v___x_78_, v___x_79_);
lean_dec_ref(v___x_78_);
if (v___x_80_ == 0)
{
lean_dec_ref(v_arg_66_);
return v___x_80_;
}
else
{
uint8_t v___x_81_; 
v___x_81_ = l_Lean_Meta_Grind_Arith_isNonnegIntNum(v_arg_66_);
return v___x_81_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isIntNum_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_62_ = stack[0].m_obj;
uint8_t v_res_82_;
v_res_82_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_62_);
stack->m_num = v_res_82_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntNum___boxed(lean_object* v_e_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_isNum(lean_object* v_e_86_){
_start:
{
uint8_t v___x_87_; 
lean_inc_ref(v_e_86_);
v___x_87_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_86_);
if (v___x_87_ == 0)
{
uint8_t v___x_88_; 
v___x_88_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_86_);
return v___x_88_;
}
else
{
lean_dec_ref(v_e_86_);
return v___x_87_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isNum_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_86_ = stack[0].m_obj;
uint8_t v_res_89_;
v_res_89_ = l_Lean_Meta_Grind_Arith_isNum(v_e_86_);
stack->m_num = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNum___boxed(lean_object* v_e_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_Lean_Meta_Grind_Arith_isNum(v_e_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object* v_e_96_){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatType___closed__1));
v___x_98_ = l_Lean_Expr_isConstOf(v_e_96_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isNatType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_96_ = stack[0].m_obj;
uint8_t v_res_99_;
v_res_99_ = l_Lean_Meta_Grind_Arith_isNatType(v_e_96_);
stack->m_num = v_res_99_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatType___boxed(lean_object* v_e_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Lean_Meta_Grind_Arith_isNatType(v_e_100_);
lean_dec_ref(v_e_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object* v_e_105_){
_start:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntType___closed__0));
v___x_107_ = l_Lean_Expr_isConstOf(v_e_105_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isIntType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_105_ = stack[0].m_obj;
uint8_t v_res_108_;
v_res_108_ = l_Lean_Meta_Grind_Arith_isIntType(v_e_105_);
stack->m_num = v_res_108_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntType___boxed(lean_object* v_e_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Lean_Meta_Grind_Arith_isIntType(v_e_109_);
lean_dec_ref(v_e_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_isInstAddNat(lean_object* v_e_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = l_Lean_Expr_cleanupAnnotations(v_e_118_);
v___x_120_ = l_Lean_Expr_isApp(v___x_119_);
if (v___x_120_ == 0)
{
lean_dec_ref(v___x_119_);
return v___x_120_;
}
else
{
lean_object* v_arg_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_arg_121_ = lean_ctor_get(v___x_119_, 1);
lean_inc_ref(v_arg_121_);
v___x_122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_119_);
v___x_123_ = l_Lean_Expr_isApp(v___x_122_);
if (v___x_123_ == 0)
{
lean_dec_ref(v___x_122_);
lean_dec_ref(v_arg_121_);
return v___x_123_;
}
else
{
lean_object* v_arg_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_arg_124_ = lean_ctor_get(v___x_122_, 1);
lean_inc_ref(v_arg_124_);
v___x_125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_122_);
v___x_126_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1));
v___x_127_ = l_Lean_Expr_isConstOf(v___x_125_, v___x_126_);
lean_dec_ref(v___x_125_);
if (v___x_127_ == 0)
{
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_arg_121_);
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = l_Lean_Meta_Grind_Arith_isNatType(v_arg_124_);
lean_dec_ref(v_arg_124_);
if (v___x_128_ == 0)
{
lean_dec_ref(v_arg_121_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3));
v___x_130_ = l_Lean_Expr_isConstOf(v_arg_121_, v___x_129_);
lean_dec_ref(v_arg_121_);
return v___x_130_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isInstAddNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_118_ = stack[0].m_obj;
uint8_t v_res_131_;
v_res_131_ = l_Lean_Meta_Grind_Arith_isInstAddNat(v_e_118_);
stack->m_num = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___boxed(lean_object* v_e_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Lean_Meta_Grind_Arith_isInstAddNat(v_e_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_isInstLENat(lean_object* v_e_138_){
_start:
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInstLENat___closed__1));
v___x_140_ = l_Lean_Expr_isConstOf(v_e_138_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isInstLENat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_138_ = stack[0].m_obj;
uint8_t v_res_141_;
v_res_141_ = l_Lean_Meta_Grind_Arith_isInstLENat(v_e_138_);
stack->m_num = v_res_141_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___boxed(lean_object* v_e_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Lean_Meta_Grind_Arith_isInstLENat(v_e_142_);
lean_dec_ref(v_e_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f(lean_object* v_e_150_){
_start:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = l_Lean_Expr_cleanupAnnotations(v_e_150_);
v___x_152_ = l_Lean_Expr_isApp(v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
lean_dec_ref(v___x_151_);
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
v___x_157_ = lean_box(0);
return v___x_157_;
}
else
{
lean_object* v_arg_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_arg_158_ = lean_ctor_get(v___x_155_, 1);
lean_inc_ref(v_arg_158_);
v___x_159_ = l_Lean_Expr_appFnCleanup___redArg(v___x_155_);
v___x_160_ = l_Lean_Expr_isApp(v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
lean_dec_ref(v___x_159_);
lean_dec_ref(v_arg_158_);
lean_dec_ref(v_arg_154_);
v___x_161_ = lean_box(0);
return v___x_161_;
}
else
{
lean_object* v_arg_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_arg_162_ = lean_ctor_get(v___x_159_, 1);
lean_inc_ref(v_arg_162_);
v___x_163_ = l_Lean_Expr_appFnCleanup___redArg(v___x_159_);
v___x_164_ = l_Lean_Expr_isApp(v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
lean_dec_ref(v___x_163_);
lean_dec_ref(v_arg_162_);
lean_dec_ref(v_arg_158_);
lean_dec_ref(v_arg_154_);
v___x_165_ = lean_box(0);
return v___x_165_;
}
else
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = l_Lean_Expr_appFnCleanup___redArg(v___x_163_);
v___x_167_ = l_Lean_Expr_isApp(v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
lean_dec_ref(v___x_166_);
lean_dec_ref(v_arg_162_);
lean_dec_ref(v_arg_158_);
lean_dec_ref(v_arg_154_);
v___x_168_ = lean_box(0);
return v___x_168_;
}
else
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = l_Lean_Expr_appFnCleanup___redArg(v___x_166_);
v___x_170_ = l_Lean_Expr_isApp(v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
lean_dec_ref(v___x_169_);
lean_dec_ref(v_arg_162_);
lean_dec_ref(v_arg_158_);
lean_dec_ref(v_arg_154_);
v___x_171_ = lean_box(0);
return v___x_171_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_169_);
v___x_173_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2));
v___x_174_ = l_Lean_Expr_isConstOf(v___x_172_, v___x_173_);
lean_dec_ref(v___x_172_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec_ref(v_arg_162_);
lean_dec_ref(v_arg_158_);
lean_dec_ref(v_arg_154_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
uint8_t v___x_176_; 
v___x_176_ = l_Lean_Meta_Grind_Arith_isInstAddNat(v_arg_162_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
lean_dec_ref(v_arg_158_);
lean_dec_ref(v_arg_154_);
v___x_177_ = lean_box(0);
return v___x_177_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v_arg_158_);
lean_ctor_set(v___x_178_, 1, v_arg_154_);
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
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
uint8_t l_Lean_Meta_Grind_Arith_isNatAdd(lean_object* v_e_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = l_Lean_Expr_cleanupAnnotations(v_e_180_);
v___x_182_ = l_Lean_Expr_isApp(v___x_181_);
if (v___x_182_ == 0)
{
lean_dec_ref(v___x_181_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = l_Lean_Expr_appFnCleanup___redArg(v___x_181_);
v___x_184_ = l_Lean_Expr_isApp(v___x_183_);
if (v___x_184_ == 0)
{
lean_dec_ref(v___x_183_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = l_Lean_Expr_appFnCleanup___redArg(v___x_183_);
v___x_186_ = l_Lean_Expr_isApp(v___x_185_);
if (v___x_186_ == 0)
{
lean_dec_ref(v___x_185_);
return v___x_186_;
}
else
{
lean_object* v_arg_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_arg_187_ = lean_ctor_get(v___x_185_, 1);
lean_inc_ref(v_arg_187_);
v___x_188_ = l_Lean_Expr_appFnCleanup___redArg(v___x_185_);
v___x_189_ = l_Lean_Expr_isApp(v___x_188_);
if (v___x_189_ == 0)
{
lean_dec_ref(v___x_188_);
lean_dec_ref(v_arg_187_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_188_);
v___x_191_ = l_Lean_Expr_isApp(v___x_190_);
if (v___x_191_ == 0)
{
lean_dec_ref(v___x_190_);
lean_dec_ref(v_arg_187_);
return v___x_191_;
}
else
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = l_Lean_Expr_appFnCleanup___redArg(v___x_190_);
v___x_193_ = l_Lean_Expr_isApp(v___x_192_);
if (v___x_193_ == 0)
{
lean_dec_ref(v___x_192_);
lean_dec_ref(v_arg_187_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_194_ = l_Lean_Expr_appFnCleanup___redArg(v___x_192_);
v___x_195_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2));
v___x_196_ = l_Lean_Expr_isConstOf(v___x_194_, v___x_195_);
lean_dec_ref(v___x_194_);
if (v___x_196_ == 0)
{
lean_dec_ref(v_arg_187_);
return v___x_196_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = l_Lean_Meta_Grind_Arith_isInstAddNat(v_arg_187_);
return v___x_197_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isNatAdd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_180_ = stack[0].m_obj;
uint8_t v_res_198_;
v_res_198_ = l_Lean_Meta_Grind_Arith_isNatAdd(v_e_180_);
stack->m_num = v_res_198_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd___boxed(lean_object* v_e_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Lean_Meta_Grind_Arith_isNatAdd(v_e_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f(lean_object* v_e_202_){
_start:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = l_Lean_Expr_cleanupAnnotations(v_e_202_);
v___x_204_ = l_Lean_Expr_isApp(v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec_ref(v___x_203_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v_arg_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_arg_206_ = lean_ctor_get(v___x_203_, 1);
lean_inc_ref(v_arg_206_);
v___x_207_ = l_Lean_Expr_appFnCleanup___redArg(v___x_203_);
v___x_208_ = l_Lean_Expr_isApp(v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
lean_dec_ref(v___x_207_);
lean_dec_ref(v_arg_206_);
v___x_209_ = lean_box(0);
return v___x_209_;
}
else
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = l_Lean_Expr_appFnCleanup___redArg(v___x_207_);
v___x_211_ = l_Lean_Expr_isApp(v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
lean_dec_ref(v___x_210_);
lean_dec_ref(v_arg_206_);
v___x_212_ = lean_box(0);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_213_ = l_Lean_Expr_appFnCleanup___redArg(v___x_210_);
v___x_214_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__2));
v___x_215_ = l_Lean_Expr_isConstOf(v___x_213_, v___x_214_);
lean_dec_ref(v___x_213_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
lean_dec_ref(v_arg_206_);
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = l_Lean_Expr_cleanupAnnotations(v_arg_206_);
v___x_218_ = l_Lean_Expr_isApp(v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
lean_dec_ref(v___x_217_);
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v_arg_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_arg_220_ = lean_ctor_get(v___x_217_, 1);
lean_inc_ref(v_arg_220_);
v___x_221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_217_);
v___x_222_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__4));
v___x_223_ = l_Lean_Expr_isConstOf(v___x_221_, v___x_222_);
lean_dec_ref(v___x_221_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; 
lean_dec_ref(v_arg_220_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
else
{
if (lean_obj_tag(v_arg_220_) == 9)
{
lean_object* v_a_225_; 
v_a_225_ = lean_ctor_get(v_arg_220_, 0);
lean_inc_ref(v_a_225_);
lean_dec_ref_known(v_arg_220_, 1);
if (lean_obj_tag(v_a_225_) == 0)
{
lean_object* v_val_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
v_val_226_ = lean_ctor_get(v_a_225_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_a_225_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v_a_225_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_val_226_);
lean_dec(v_a_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
lean_ctor_set_tag(v___x_228_, 1);
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_val_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
else
{
lean_object* v___x_234_; 
lean_dec_ref(v_a_225_);
v___x_234_ = lean_box(0);
return v___x_234_;
}
}
else
{
lean_object* v___x_235_; 
lean_dec_ref(v_arg_220_);
v___x_235_ = lean_box(0);
return v___x_235_;
}
}
}
}
}
}
}
}
}
uint8_t l_Lean_Meta_Grind_Arith_isArithTerm(lean_object* v_e_276_){
_start:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = l_Lean_Expr_cleanupAnnotations(v_e_276_);
v___x_278_ = l_Lean_Expr_isApp(v___x_277_);
if (v___x_278_ == 0)
{
lean_dec_ref(v___x_277_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = l_Lean_Expr_appFnCleanup___redArg(v___x_277_);
v___x_280_ = l_Lean_Expr_isApp(v___x_279_);
if (v___x_280_ == 0)
{
lean_dec_ref(v___x_279_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = l_Lean_Expr_appFnCleanup___redArg(v___x_279_);
v___x_282_ = l_Lean_Expr_isApp(v___x_281_);
if (v___x_282_ == 0)
{
lean_dec_ref(v___x_281_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_283_ = l_Lean_Expr_appFnCleanup___redArg(v___x_281_);
v___x_284_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__2));
v___x_285_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__5));
v___x_287_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatNum___closed__2));
v___x_289_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isIntNum___closed__2));
v___x_291_ = l_Lean_Expr_isConstOf(v___x_283_, v___x_290_);
if (v___x_291_ == 0)
{
uint8_t v___x_292_; 
v___x_292_ = l_Lean_Expr_isApp(v___x_283_);
if (v___x_292_ == 0)
{
lean_dec_ref(v___x_283_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = l_Lean_Expr_appFnCleanup___redArg(v___x_283_);
v___x_294_ = l_Lean_Expr_isApp(v___x_293_);
if (v___x_294_ == 0)
{
lean_dec_ref(v___x_293_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = l_Lean_Expr_appFnCleanup___redArg(v___x_293_);
v___x_296_ = l_Lean_Expr_isApp(v___x_295_);
if (v___x_296_ == 0)
{
lean_dec_ref(v___x_295_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_295_);
v___x_298_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__8));
v___x_299_ = l_Lean_Expr_isConstOf(v___x_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__11));
v___x_301_ = l_Lean_Expr_isConstOf(v___x_297_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__14));
v___x_303_ = l_Lean_Expr_isConstOf(v___x_297_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__17));
v___x_305_ = l_Lean_Expr_isConstOf(v___x_297_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__20));
v___x_307_ = l_Lean_Expr_isConstOf(v___x_297_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isArithTerm___closed__23));
v___x_309_ = l_Lean_Expr_isConstOf(v___x_297_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2));
v___x_311_ = l_Lean_Expr_isConstOf(v___x_297_, v___x_310_);
lean_dec_ref(v___x_297_);
return v___x_311_;
}
else
{
lean_dec_ref(v___x_297_);
return v___x_309_;
}
}
else
{
lean_dec_ref(v___x_297_);
return v___x_307_;
}
}
else
{
lean_dec_ref(v___x_297_);
return v___x_305_;
}
}
else
{
lean_dec_ref(v___x_297_);
return v___x_303_;
}
}
else
{
lean_dec_ref(v___x_297_);
return v___x_301_;
}
}
else
{
lean_dec_ref(v___x_297_);
return v___x_299_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_283_);
return v___x_291_;
}
}
else
{
lean_dec_ref(v___x_283_);
return v___x_289_;
}
}
else
{
lean_dec_ref(v___x_283_);
return v___x_287_;
}
}
else
{
lean_dec_ref(v___x_283_);
return v___x_285_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isArithTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_276_ = stack[0].m_obj;
uint8_t v_res_312_;
v_res_312_ = l_Lean_Meta_Grind_Arith_isArithTerm(v_e_276_);
stack->m_num = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___boxed(lean_object* v_e_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Lean_Meta_Grind_Arith_isArithTerm(v_e_313_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object* v_e_316_){
_start:
{
uint8_t v___x_317_; 
lean_inc_ref(v_e_316_);
v___x_317_ = l_Lean_Meta_Grind_Arith_isArithTerm(v_e_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_MessageData_ofExpr(v_e_316_);
return v___x_318_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = l_Lean_MessageData_ofExpr(v_e_316_);
v___x_320_ = l_Lean_aquote(v___x_319_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_gcdExt_spec__0(lean_object* v_a_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_nat_to_int(v_a_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_gcdExt___closed__0(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_nat_to_int(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_gcdExt___closed__0, &l_Lean_Meta_Grind_Arith_gcdExt___closed__0_once, _init_l_Lean_Meta_Grind_Arith_gcdExt___closed__0);
v___x_328_ = lean_int_dec_eq(v_b_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_snd_331_; lean_object* v_fst_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_351_; 
v___x_329_ = lean_int_emod(v_a_325_, v_b_326_);
v___x_330_ = l_Lean_Meta_Grind_Arith_gcdExt(v_b_326_, v___x_329_);
lean_dec(v___x_329_);
v_snd_331_ = lean_ctor_get(v___x_330_, 1);
v_fst_332_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_351_ == 0)
{
v___x_334_ = v___x_330_;
v_isShared_335_ = v_isSharedCheck_351_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_snd_331_);
lean_inc(v_fst_332_);
lean_dec(v___x_330_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_351_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_fst_336_; lean_object* v_snd_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_350_; 
v_fst_336_ = lean_ctor_get(v_snd_331_, 0);
v_snd_337_ = lean_ctor_get(v_snd_331_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v_snd_331_);
if (v_isSharedCheck_350_ == 0)
{
v___x_339_ = v_snd_331_;
v_isShared_340_ = v_isSharedCheck_350_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_snd_337_);
lean_inc(v_fst_336_);
lean_dec(v_snd_331_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_350_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_341_ = lean_int_ediv(v_a_325_, v_b_326_);
v___x_342_ = lean_int_mul(v___x_341_, v_snd_337_);
lean_dec(v___x_341_);
v___x_343_ = lean_int_sub(v_fst_336_, v___x_342_);
lean_dec(v___x_342_);
lean_dec(v_fst_336_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_343_);
lean_ctor_set(v___x_339_, 0, v_snd_337_);
v___x_345_ = v___x_339_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_snd_337_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_343_);
v___x_345_ = v_reuseFailAlloc_349_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_347_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 1, v___x_345_);
v___x_347_ = v___x_334_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_fst_332_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___y_355_; uint8_t v___x_358_; 
v___x_352_ = lean_nat_abs(v_a_325_);
v___x_353_ = lean_nat_to_int(v___x_352_);
v___x_358_ = lean_int_dec_eq(v_a_325_, v___x_327_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
v___x_359_ = lean_int_ediv(v_a_325_, v___x_353_);
v___y_355_ = v___x_359_;
goto v___jp_354_;
}
else
{
v___y_355_ = v___x_327_;
goto v___jp_354_;
}
v___jp_354_:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___y_355_);
lean_ctor_set(v___x_356_, 1, v___x_327_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_353_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt___boxed(lean_object* v_a_360_, lean_object* v_b_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Meta_Grind_Arith_gcdExt(v_a_360_, v_b_361_);
lean_dec(v_b_361_);
lean_dec(v_a_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object* v_a_363_, lean_object* v_sz_364_){
_start:
{
lean_object* v_size_365_; uint8_t v___x_366_; 
v_size_365_ = lean_ctor_get(v_a_363_, 2);
v___x_366_ = lean_nat_dec_lt(v_sz_364_, v_size_365_);
if (v___x_366_ == 0)
{
return v_a_363_;
}
else
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_PersistentArray_pop___redArg(v_a_363_);
v_a_363_ = v___x_367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_shrink___boxed(lean_object* v_a_369_, lean_object* v_sz_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Grind_Arith_shrink(v_a_369_, v_sz_370_);
lean_dec(v_sz_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go_spec__0(lean_object* v_a_372_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_nat_to_int(v_a_372_);
v___x_374_ = l_Rat_ofInt(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go_spec__0(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(lean_object* v_sz_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_size_379_; uint8_t v___x_380_; 
v_size_379_ = lean_ctor_get(v_a_378_, 2);
v___x_380_ = lean_nat_dec_lt(v_size_379_, v_sz_377_);
if (v___x_380_ == 0)
{
return v_a_378_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___closed__0);
v___x_382_ = l_Lean_PersistentArray_push___redArg(v_a_378_, v___x_381_);
v_a_378_ = v___x_382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go___boxed(lean_object* v_sz_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(v_sz_384_, v_a_385_);
lean_dec(v_sz_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize(lean_object* v_a_387_, lean_object* v_sz_388_){
_start:
{
lean_object* v_size_389_; uint8_t v___x_390_; 
v_size_389_ = lean_ctor_get(v_a_387_, 2);
v___x_390_ = lean_nat_dec_lt(v_sz_388_, v_size_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_resize_go(v_sz_388_, v_a_387_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_Grind_Arith_shrink(v_a_387_, v_sz_388_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_resize___boxed(lean_object* v_a_393_, lean_object* v_sz_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Grind_Arith_resize(v_a_393_, v_sz_394_);
lean_dec(v_sz_394_);
return v_res_395_;
}
}
uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(lean_object* v_c_396_){
_start:
{
size_t v___x_397_; uint64_t v___x_398_; uint64_t v___x_399_; uint64_t v___x_400_; 
v___x_397_ = lean_ptr_addr(v_c_396_);
v___x_398_ = lean_usize_to_uint64(v___x_397_);
v___x_399_ = 2ULL;
v___x_400_ = lean_uint64_shift_right(v___x_398_, v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_396_ = stack[0].m_obj;
uint64_t v_res_401_;
v_res_401_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(v_c_396_);
stack->m_num = v_res_401_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg___boxed(lean_object* v_c_402_){
_start:
{
uint64_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___redArg(v_c_402_);
lean_dec(v_c_402_);
v_r_404_ = lean_box_uint64(v_res_403_);
return v_r_404_;
}
}
uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(lean_object* v_00_u03b1_405_, lean_object* v_c_406_){
_start:
{
size_t v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; 
v___x_407_ = lean_ptr_addr(v_c_406_);
v___x_408_ = lean_usize_to_uint64(v___x_407_);
v___x_409_ = 2ULL;
v___x_410_ = lean_uint64_shift_right(v___x_408_, v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_406_ = stack[1].m_obj;
uint64_t v_res_411_;
v_res_411_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(lean_box(0), v_c_406_);
stack->m_num = v_res_411_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1___boxed(lean_object* v_00_u03b1_412_, lean_object* v_c_413_){
_start:
{
uint64_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_unsafe__1(v_00_u03b1_412_, v_c_413_);
lean_dec(v_c_413_);
v_r_415_ = lean_box_uint64(v_res_414_);
return v_r_415_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(uint64_t v_a_416_, lean_object* v_x_417_){
_start:
{
if (lean_obj_tag(v_x_417_) == 0)
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
else
{
lean_object* v_key_419_; lean_object* v_tail_420_; uint64_t v___x_421_; uint8_t v___x_422_; 
v_key_419_ = lean_ctor_get(v_x_417_, 0);
v_tail_420_ = lean_ctor_get(v_x_417_, 2);
v___x_421_ = lean_unbox_uint64(v_key_419_);
v___x_422_ = lean_uint64_dec_eq(v___x_421_, v_a_416_);
if (v___x_422_ == 0)
{
v_x_417_ = v_tail_420_;
goto _start;
}
else
{
return v___x_422_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_416_ = stack[0].m_num;
lean_object* v_x_417_ = stack[1].m_obj;
uint8_t v_res_424_;
v_res_424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_416_, v_x_417_);
stack->m_num = v_res_424_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg___boxed(lean_object* v_a_425_, lean_object* v_x_426_){
_start:
{
uint64_t v_a_boxed_427_; uint8_t v_res_428_; lean_object* v_r_429_; 
v_a_boxed_427_ = lean_unbox_uint64(v_a_425_);
lean_dec_ref(v_a_425_);
v_res_428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_boxed_427_, v_x_426_);
lean_dec(v_x_426_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(lean_object* v_m_430_, uint64_t v_a_431_){
_start:
{
lean_object* v_buckets_432_; lean_object* v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; uint64_t v_fold_436_; uint64_t v___x_437_; uint64_t v___x_438_; uint64_t v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_buckets_432_ = lean_ctor_get(v_m_430_, 1);
v___x_433_ = lean_array_get_size(v_buckets_432_);
v___x_434_ = 32ULL;
v___x_435_ = lean_uint64_shift_right(v_a_431_, v___x_434_);
v_fold_436_ = lean_uint64_xor(v_a_431_, v___x_435_);
v___x_437_ = 16ULL;
v___x_438_ = lean_uint64_shift_right(v_fold_436_, v___x_437_);
v___x_439_ = lean_uint64_xor(v_fold_436_, v___x_438_);
v___x_440_ = lean_uint64_to_usize(v___x_439_);
v___x_441_ = lean_usize_of_nat(v___x_433_);
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_sub(v___x_441_, v___x_442_);
v___x_444_ = lean_usize_land(v___x_440_, v___x_443_);
v___x_445_ = lean_array_uget_borrowed(v_buckets_432_, v___x_444_);
v___x_446_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_431_, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_430_ = stack[0].m_obj;
uint64_t v_a_431_ = stack[1].m_num;
uint8_t v_res_447_;
v_res_447_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_m_430_, v_a_431_);
stack->m_num = v_res_447_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg___boxed(lean_object* v_m_448_, lean_object* v_a_449_){
_start:
{
uint64_t v_a_boxed_450_; uint8_t v_res_451_; lean_object* v_r_452_; 
v_a_boxed_450_ = lean_unbox_uint64(v_a_449_);
lean_dec_ref(v_a_449_);
v_res_451_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_m_448_, v_a_boxed_450_);
lean_dec_ref(v_m_448_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
return v_x_453_;
}
else
{
lean_object* v_key_455_; lean_object* v_value_456_; lean_object* v_tail_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_481_; 
v_key_455_ = lean_ctor_get(v_x_454_, 0);
v_value_456_ = lean_ctor_get(v_x_454_, 1);
v_tail_457_ = lean_ctor_get(v_x_454_, 2);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_454_);
if (v_isSharedCheck_481_ == 0)
{
v___x_459_ = v_x_454_;
v_isShared_460_ = v_isSharedCheck_481_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_tail_457_);
lean_inc(v_value_456_);
lean_inc(v_key_455_);
lean_dec(v_x_454_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_481_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; uint64_t v___x_465_; uint64_t v_fold_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v___x_469_; size_t v___x_470_; size_t v___x_471_; size_t v___x_472_; size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_461_ = lean_array_get_size(v_x_453_);
v___x_462_ = 32ULL;
v___x_463_ = lean_unbox_uint64(v_key_455_);
v___x_464_ = lean_uint64_shift_right(v___x_463_, v___x_462_);
v___x_465_ = lean_unbox_uint64(v_key_455_);
v_fold_466_ = lean_uint64_xor(v___x_465_, v___x_464_);
v___x_467_ = 16ULL;
v___x_468_ = lean_uint64_shift_right(v_fold_466_, v___x_467_);
v___x_469_ = lean_uint64_xor(v_fold_466_, v___x_468_);
v___x_470_ = lean_uint64_to_usize(v___x_469_);
v___x_471_ = lean_usize_of_nat(v___x_461_);
v___x_472_ = ((size_t)1ULL);
v___x_473_ = lean_usize_sub(v___x_471_, v___x_472_);
v___x_474_ = lean_usize_land(v___x_470_, v___x_473_);
v___x_475_ = lean_array_uget_borrowed(v_x_453_, v___x_474_);
lean_inc(v___x_475_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 2, v___x_475_);
v___x_477_ = v___x_459_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_key_455_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_value_456_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v___x_475_);
v___x_477_ = v_reuseFailAlloc_480_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; 
v___x_478_ = lean_array_uset(v_x_453_, v___x_474_, v___x_477_);
v_x_453_ = v___x_478_;
v_x_454_ = v_tail_457_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(lean_object* v_i_482_, lean_object* v_source_483_, lean_object* v_target_484_){
_start:
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_array_get_size(v_source_483_);
v___x_486_ = lean_nat_dec_lt(v_i_482_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec_ref(v_source_483_);
lean_dec(v_i_482_);
return v_target_484_;
}
else
{
lean_object* v_es_487_; lean_object* v___x_488_; lean_object* v_source_489_; lean_object* v_target_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_es_487_ = lean_array_fget(v_source_483_, v_i_482_);
v___x_488_ = lean_box(0);
v_source_489_ = lean_array_fset(v_source_483_, v_i_482_, v___x_488_);
v_target_490_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(v_target_484_, v_es_487_);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_add(v_i_482_, v___x_491_);
lean_dec(v_i_482_);
v_i_482_ = v___x_492_;
v_source_483_ = v_source_489_;
v_target_484_ = v_target_490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(lean_object* v_data_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_nbuckets_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_495_ = lean_array_get_size(v_data_494_);
v___x_496_ = lean_unsigned_to_nat(2u);
v_nbuckets_497_ = lean_nat_mul(v___x_495_, v___x_496_);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_box(0);
v___x_500_ = lean_mk_array(v_nbuckets_497_, v___x_499_);
v___x_501_ = lean_array_propagate_mark(v_data_494_, v___x_500_);
v___x_502_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(v___x_498_, v_data_494_, v___x_501_);
return v___x_502_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(lean_object* v_m_503_, uint64_t v_a_504_, lean_object* v_b_505_){
_start:
{
lean_object* v_size_506_; lean_object* v_buckets_507_; lean_object* v___x_508_; uint64_t v___x_509_; uint64_t v___x_510_; uint64_t v_fold_511_; uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; size_t v___x_518_; size_t v___x_519_; lean_object* v_bkt_520_; uint8_t v___x_521_; 
v_size_506_ = lean_ctor_get(v_m_503_, 0);
v_buckets_507_ = lean_ctor_get(v_m_503_, 1);
v___x_508_ = lean_array_get_size(v_buckets_507_);
v___x_509_ = 32ULL;
v___x_510_ = lean_uint64_shift_right(v_a_504_, v___x_509_);
v_fold_511_ = lean_uint64_xor(v_a_504_, v___x_510_);
v___x_512_ = 16ULL;
v___x_513_ = lean_uint64_shift_right(v_fold_511_, v___x_512_);
v___x_514_ = lean_uint64_xor(v_fold_511_, v___x_513_);
v___x_515_ = lean_uint64_to_usize(v___x_514_);
v___x_516_ = lean_usize_of_nat(v___x_508_);
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_sub(v___x_516_, v___x_517_);
v___x_519_ = lean_usize_land(v___x_515_, v___x_518_);
v_bkt_520_ = lean_array_uget_borrowed(v_buckets_507_, v___x_519_);
v___x_521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_504_, v_bkt_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_543_; 
lean_inc_ref(v_buckets_507_);
lean_inc(v_size_506_);
v_isSharedCheck_543_ = !lean_is_exclusive(v_m_503_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; lean_object* v_unused_545_; 
v_unused_544_ = lean_ctor_get(v_m_503_, 1);
lean_dec(v_unused_544_);
v_unused_545_ = lean_ctor_get(v_m_503_, 0);
lean_dec(v_unused_545_);
v___x_523_ = v_m_503_;
v_isShared_524_ = v_isSharedCheck_543_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_m_503_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_543_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v_size_x27_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_buckets_x27_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v_size_x27_526_ = lean_nat_add(v_size_506_, v___x_525_);
lean_dec(v_size_506_);
v___x_527_ = lean_box_uint64(v_a_504_);
lean_inc(v_bkt_520_);
v___x_528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v_b_505_);
lean_ctor_set(v___x_528_, 2, v_bkt_520_);
v_buckets_x27_529_ = lean_array_uset(v_buckets_507_, v___x_519_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(4u);
v___x_531_ = lean_nat_mul(v_size_x27_526_, v___x_530_);
v___x_532_ = lean_unsigned_to_nat(3u);
v___x_533_ = lean_nat_div(v___x_531_, v___x_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_array_get_size(v_buckets_x27_529_);
v___x_535_ = lean_nat_dec_le(v___x_533_, v___x_534_);
lean_dec(v___x_533_);
if (v___x_535_ == 0)
{
lean_object* v_val_536_; lean_object* v___x_538_; 
v_val_536_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(v_buckets_x27_529_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_val_536_);
lean_ctor_set(v___x_523_, 0, v_size_x27_526_);
v___x_538_ = v___x_523_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_size_x27_526_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_val_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
else
{
lean_object* v___x_541_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_buckets_x27_529_);
lean_ctor_set(v___x_523_, 0, v_size_x27_526_);
v___x_541_ = v___x_523_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_size_x27_526_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_buckets_x27_529_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_dec(v_b_505_);
return v_m_503_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_503_ = stack[0].m_obj;
uint64_t v_a_504_ = stack[1].m_num;
lean_object* v_b_505_ = stack[2].m_obj;
lean_object* v_res_546_;
v_res_546_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_m_503_, v_a_504_, v_b_505_);
stack->m_obj
 = v_res_546_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg___boxed(lean_object* v_m_547_, lean_object* v_a_548_, lean_object* v_b_549_){
_start:
{
uint64_t v_a_boxed_550_; lean_object* v_res_551_; 
v_a_boxed_550_ = lean_unbox_uint64(v_a_548_);
lean_dec_ref(v_a_548_);
v_res_551_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_m_547_, v_a_boxed_550_, v_b_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(lean_object* v_c_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_visited_554_; lean_object* v_found_555_; size_t v___x_556_; uint64_t v___x_557_; uint64_t v___x_558_; uint64_t v_addr_559_; uint8_t v___x_560_; 
v_visited_554_ = lean_ctor_get(v_a_553_, 0);
v_found_555_ = lean_ctor_get(v_a_553_, 1);
v___x_556_ = lean_ptr_addr(v_c_552_);
v___x_557_ = lean_usize_to_uint64(v___x_556_);
v___x_558_ = 2ULL;
v_addr_559_ = lean_uint64_shift_right(v___x_557_, v___x_558_);
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_visited_554_, v_addr_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_571_; 
lean_inc(v_found_555_);
lean_inc_ref(v_visited_554_);
v_isSharedCheck_571_ = !lean_is_exclusive(v_a_553_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; lean_object* v_unused_573_; 
v_unused_572_ = lean_ctor_get(v_a_553_, 1);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_a_553_, 0);
lean_dec(v_unused_573_);
v___x_562_ = v_a_553_;
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
else
{
lean_dec(v_a_553_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_564_ = lean_box(0);
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_visited_554_, v_addr_559_, v___x_564_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_565_);
v___x_567_ = v___x_562_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_found_555_);
v___x_567_ = v_reuseFailAlloc_570_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_box(v___x_560_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
return v___x_569_;
}
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_box(v___x_560_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_a_553_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg___boxed(lean_object* v_c_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(v_c_576_, v_a_577_);
lean_dec(v_c_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(lean_object* v_00_u03b1_579_, lean_object* v_c_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(v_c_580_, v_a_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___boxed(lean_object* v_00_u03b1_584_, lean_object* v_c_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(v_00_u03b1_584_, v_c_585_, v_a_586_, v_a_587_);
lean_dec(v_a_586_);
lean_dec(v_c_585_);
return v_res_588_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(lean_object* v_00_u03b2_589_, lean_object* v_m_590_, uint64_t v_a_591_){
_start:
{
uint8_t v___x_592_; 
v___x_592_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_m_590_, v_a_591_);
return v___x_592_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_590_ = stack[1].m_obj;
uint64_t v_a_591_ = stack[2].m_num;
uint8_t v_res_593_;
v_res_593_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(lean_box(0), v_m_590_, v_a_591_);
stack->m_num = v_res_593_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___boxed(lean_object* v_00_u03b2_594_, lean_object* v_m_595_, lean_object* v_a_596_){
_start:
{
uint64_t v_a_boxed_597_; uint8_t v_res_598_; lean_object* v_r_599_; 
v_a_boxed_597_ = lean_unbox_uint64(v_a_596_);
lean_dec_ref(v_a_596_);
v_res_598_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(v_00_u03b2_594_, v_m_595_, v_a_boxed_597_);
lean_dec_ref(v_m_595_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(lean_object* v_00_u03b2_600_, lean_object* v_m_601_, uint64_t v_a_602_, lean_object* v_b_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_m_601_, v_a_602_, v_b_603_);
return v___x_604_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_601_ = stack[1].m_obj;
uint64_t v_a_602_ = stack[2].m_num;
lean_object* v_b_603_ = stack[3].m_obj;
lean_object* v_res_605_;
v_res_605_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(lean_box(0), v_m_601_, v_a_602_, v_b_603_);
stack->m_obj
 = v_res_605_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___boxed(lean_object* v_00_u03b2_606_, lean_object* v_m_607_, lean_object* v_a_608_, lean_object* v_b_609_){
_start:
{
uint64_t v_a_boxed_610_; lean_object* v_res_611_; 
v_a_boxed_610_ = lean_unbox_uint64(v_a_608_);
lean_dec_ref(v_a_608_);
v_res_611_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(v_00_u03b2_606_, v_m_607_, v_a_boxed_610_, v_b_609_);
return v_res_611_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(lean_object* v_00_u03b2_612_, uint64_t v_a_613_, lean_object* v_x_614_){
_start:
{
uint8_t v___x_615_; 
v___x_615_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_a_613_, v_x_614_);
return v___x_615_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_613_ = stack[1].m_num;
lean_object* v_x_614_ = stack[2].m_obj;
uint8_t v_res_616_;
v_res_616_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(lean_box(0), v_a_613_, v_x_614_);
stack->m_num = v_res_616_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___boxed(lean_object* v_00_u03b2_617_, lean_object* v_a_618_, lean_object* v_x_619_){
_start:
{
uint64_t v_a_boxed_620_; uint8_t v_res_621_; lean_object* v_r_622_; 
v_a_boxed_620_ = lean_unbox_uint64(v_a_618_);
lean_dec_ref(v_a_618_);
v_res_621_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(v_00_u03b2_617_, v_a_boxed_620_, v_x_619_);
lean_dec(v_x_619_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2(lean_object* v_00_u03b2_623_, lean_object* v_data_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(v_data_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_626_, lean_object* v_i_627_, lean_object* v_source_628_, lean_object* v_target_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3___redArg(v_i_627_, v_source_628_, v_target_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2_spec__3_spec__4___redArg(v_x_632_, v_x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(lean_object* v_fvarId_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_visited_637_; lean_object* v_found_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_648_; 
v_visited_637_ = lean_ctor_get(v_a_636_, 0);
v_found_638_ = lean_ctor_get(v_a_636_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_a_636_);
if (v_isSharedCheck_648_ == 0)
{
v___x_640_ = v_a_636_;
v_isShared_641_ = v_isSharedCheck_648_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_found_638_);
lean_inc(v_visited_637_);
lean_dec(v_a_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_648_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_642_ = lean_box(0);
v___x_643_ = l_Lean_FVarIdSet_insert(v_found_638_, v_fvarId_635_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_643_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_visited_637_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_647_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_642_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
return v___x_646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(lean_object* v_fvarId_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(v_fvarId_649_, v_a_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___boxed(lean_object* v_fvarId_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(v_fvarId_653_, v_a_654_, v_a_655_);
lean_dec(v_a_654_);
return v_res_656_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
v___x_658_ = lean_unsigned_to_nat(16u);
v___x_659_ = lean_mk_array(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0);
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v___x_660_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_box(1);
v___x_664_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run(lean_object* v_x_666_, lean_object* v_decVars_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_snd_670_; lean_object* v_found_671_; 
v___x_668_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2);
v___x_669_ = lean_apply_2(v_x_666_, v_decVars_667_, v___x_668_);
v_snd_670_ = lean_ctor_get(v___x_669_, 1);
lean_inc(v_snd_670_);
lean_dec_ref(v___x_669_);
v_found_671_ = lean_ctor_get(v_snd_670_, 1);
lean_inc(v_found_671_);
lean_dec(v_snd_670_);
return v_found_671_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________(void){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = 1;
return v___x_672_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
v___x_721_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20));
v___x_722_ = l_Lean_mkConst(v___x_721_, v___x_720_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent(void){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21, &l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21_once, _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21);
return v___x_723_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object* v_parent_x3f_724_){
_start:
{
if (lean_obj_tag(v_parent_x3f_724_) == 0)
{
uint8_t v___x_725_; 
v___x_725_ = 0;
return v___x_725_;
}
else
{
lean_object* v_val_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_val_726_ = lean_ctor_get(v_parent_x3f_724_, 0);
v___x_727_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_728_ = lean_expr_eqv(v_val_726_, v___x_727_);
return v___x_728_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent_0interp(lean_interpreter_value* stack)
{
lean_object* v_parent_x3f_724_ = stack[0].m_obj;
uint8_t v_res_729_;
v_res_729_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_724_);
stack->m_num = v_res_729_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent___boxed(lean_object* v_parent_x3f_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_730_);
lean_dec(v_parent_x3f_730_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___lam__0(lean_object* v_getCoeff_733_, lean_object* v___x_734_, lean_object* v_c_735_, lean_object* v_____s_736_){
_start:
{
lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_756_; 
v_fst_737_ = lean_ctor_get(v_____s_736_, 0);
v_snd_738_ = lean_ctor_get(v_____s_736_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_____s_736_);
if (v_isSharedCheck_756_ == 0)
{
v___x_740_ = v_____s_736_;
v_isShared_741_ = v_isSharedCheck_756_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_snd_738_);
lean_inc(v_fst_737_);
lean_dec(v_____s_736_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_756_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_b_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
lean_inc(v_c_735_);
v_b_742_ = lean_apply_1(v_getCoeff_733_, v_c_735_);
v___x_743_ = lean_nat_to_int(v___x_734_);
v___x_744_ = lean_int_dec_eq(v_b_742_, v___x_743_);
lean_dec(v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_746_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v_c_735_);
lean_ctor_set(v___x_740_, 0, v_b_742_);
v___x_746_ = v___x_740_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_b_742_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_c_735_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v_todo_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_todo_747_ = lean_array_push(v_snd_738_, v___x_746_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v_fst_737_);
lean_ctor_set(v___x_748_, 1, v_todo_747_);
v___x_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
else
{
lean_object* v_cs_x27_751_; lean_object* v___x_753_; 
lean_dec(v_b_742_);
v_cs_x27_751_ = l_Lean_PersistentArray_push___redArg(v_fst_737_, v_c_735_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v_cs_x27_751_);
v___x_753_ = v___x_740_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_cs_x27_751_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_snd_738_);
v___x_753_ = v_reuseFailAlloc_755_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; 
v___x_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_unsigned_to_nat(32u);
v___x_777_ = lean_mk_empty_array_with_capacity(v___x_776_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11(void){
_start:
{
size_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_cs_x27_784_; 
v___x_779_ = ((size_t)5ULL);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_unsigned_to_nat(32u);
v___x_782_ = lean_mk_empty_array_with_capacity(v___x_781_);
v___x_783_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__10, &l_Lean_Meta_Grind_Arith_split___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10);
v_cs_x27_784_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_784_, 0, v___x_783_);
lean_ctor_set(v_cs_x27_784_, 1, v___x_782_);
lean_ctor_set(v_cs_x27_784_, 2, v___x_780_);
lean_ctor_set(v_cs_x27_784_, 3, v___x_780_);
lean_ctor_set_usize(v_cs_x27_784_, 4, v___x_779_);
return v_cs_x27_784_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13(void){
_start:
{
lean_object* v_todo_787_; lean_object* v_cs_x27_788_; lean_object* v___x_789_; 
v_todo_787_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___redArg___closed__12));
v_cs_x27_788_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__11, &l_Lean_Meta_Grind_Arith_split___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_cs_x27_788_);
lean_ctor_set(v___x_789_, 1, v_todo_787_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg(lean_object* v_cs_790_, lean_object* v_getCoeff_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_fst_797_; lean_object* v_snd_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v___x_792_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___redArg___closed__9));
v___x_793_ = lean_unsigned_to_nat(0u);
v___f_794_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_split___redArg___lam__0), 4, 2);
lean_closure_set(v___f_794_, 0, v_getCoeff_791_);
lean_closure_set(v___f_794_, 1, v___x_793_);
v___x_795_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__13, &l_Lean_Meta_Grind_Arith_split___redArg___closed__13_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13);
v___x_796_ = l_Lean_PersistentArray_forIn___redArg(v___x_792_, v_cs_790_, v___x_795_, v___f_794_);
v_fst_797_ = lean_ctor_get(v___x_796_, 0);
v_snd_798_ = lean_ctor_get(v___x_796_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_796_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snd_798_);
lean_inc(v_fst_797_);
lean_dec(v___x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_fst_797_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_snd_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___boxed(lean_object* v_cs_806_, lean_object* v_getCoeff_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Meta_Grind_Arith_split___redArg(v_cs_806_, v_getCoeff_807_);
lean_dec_ref(v_cs_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split(lean_object* v_00_u03b1_809_, lean_object* v_cs_810_, lean_object* v_getCoeff_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Meta_Grind_Arith_split___redArg(v_cs_810_, v_getCoeff_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___boxed(lean_object* v_00_u03b1_813_, lean_object* v_cs_814_, lean_object* v_getCoeff_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Meta_Grind_Arith_split(v_00_u03b1_813_, v_cs_814_, v_getCoeff_815_);
lean_dec_ref(v_cs_814_);
return v_res_816_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
