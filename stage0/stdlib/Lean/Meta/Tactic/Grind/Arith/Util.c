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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(lean_object* v_m_404_, uint64_t v_query_405_, lean_object* v_x_406_, lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
lean_object* v_zero_409_; uint8_t v_isZero_410_; 
v_zero_409_ = lean_unsigned_to_nat(0u);
v_isZero_410_ = lean_nat_dec_eq(v_x_407_, v_zero_409_);
if (v_isZero_410_ == 1)
{
lean_dec(v_x_408_);
lean_dec(v_x_407_);
if (lean_obj_tag(v_x_406_) == 0)
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(2);
return v___x_411_;
}
else
{
lean_object* v_val_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_val_412_ = lean_ctor_get(v_x_406_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_x_406_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v_x_406_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_val_412_);
lean_dec(v_x_406_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_val_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v_keyArray_420_; lean_object* v_valueArray_421_; lean_object* v___x_422_; uint8_t v_isSome_423_; 
v_keyArray_420_ = lean_ctor_get(v_m_404_, 1);
v_valueArray_421_ = lean_ctor_get(v_m_404_, 2);
v___x_422_ = lean_array_fget_borrowed(v_keyArray_420_, v_x_408_);
v_isSome_423_ = lean_noption_is_some(v___x_422_);
if (v_isSome_423_ == 0)
{
lean_dec(v_x_407_);
if (lean_obj_tag(v_x_406_) == 0)
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v_x_408_);
return v___x_424_;
}
else
{
lean_object* v_val_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec(v_x_408_);
v_val_425_ = lean_ctor_get(v_x_406_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_x_406_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v_x_406_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_val_425_);
lean_dec(v_x_406_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_val_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
else
{
lean_object* v_one_433_; lean_object* v_n_434_; lean_object* v___y_436_; 
v_one_433_ = lean_unsigned_to_nat(1u);
v_n_434_ = lean_nat_sub(v_x_407_, v_one_433_);
lean_dec(v_x_407_);
if (v_isSome_423_ == 0)
{
goto v___jp_442_;
}
else
{
lean_object* v___x_444_; uint8_t v_isSome_445_; 
v___x_444_ = lean_array_fget_borrowed(v_valueArray_421_, v_x_408_);
v_isSome_445_ = lean_noption_is_some(v___x_444_);
if (v_isSome_445_ == 0)
{
goto v___jp_442_;
}
else
{
lean_object* v_val_446_; uint64_t v___x_447_; uint8_t v___x_448_; 
lean_inc(v___x_422_);
v_val_446_ = lean_noption_get(v___x_422_);
v___x_447_ = lean_unbox_uint64(v_val_446_);
v___x_448_ = lean_uint64_dec_eq(v___x_447_, v_query_405_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
lean_dec(v_val_446_);
v___x_449_ = lean_array_get_size(v_keyArray_420_);
v___x_450_ = lean_nat_add(v_x_408_, v_one_433_);
lean_dec(v_x_408_);
v___x_451_ = lean_nat_dec_lt(v___x_450_, v___x_449_);
if (v___x_451_ == 0)
{
lean_dec(v___x_450_);
v_x_407_ = v_n_434_;
v_x_408_ = v_zero_409_;
goto _start;
}
else
{
v_x_407_ = v_n_434_;
v_x_408_ = v___x_450_;
goto _start;
}
}
else
{
lean_object* v_val_454_; lean_object* v___x_455_; 
lean_dec(v_n_434_);
lean_dec(v_x_406_);
lean_inc(v___x_444_);
v_val_454_ = lean_noption_get(v___x_444_);
v___x_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_455_, 0, v_x_408_);
lean_ctor_set(v___x_455_, 1, v_val_446_);
lean_ctor_set(v___x_455_, 2, v_val_454_);
return v___x_455_;
}
}
}
v___jp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_437_ = lean_array_get_size(v_keyArray_420_);
v___x_438_ = lean_nat_add(v_x_408_, v_one_433_);
lean_dec(v_x_408_);
v___x_439_ = lean_nat_dec_lt(v___x_438_, v___x_437_);
if (v___x_439_ == 0)
{
lean_dec(v___x_438_);
v_x_406_ = v___y_436_;
v_x_407_ = v_n_434_;
v_x_408_ = v_zero_409_;
goto _start;
}
else
{
v_x_406_ = v___y_436_;
v_x_407_ = v_n_434_;
v_x_408_ = v___x_438_;
goto _start;
}
}
v___jp_442_:
{
if (lean_obj_tag(v_x_406_) == 0)
{
lean_object* v___x_443_; 
lean_inc(v_x_408_);
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v_x_408_);
v___y_436_ = v___x_443_;
goto v___jp_435_;
}
else
{
v___y_436_ = v_x_406_;
goto v___jp_435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg___boxed(lean_object* v_m_456_, lean_object* v_query_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
uint64_t v_query_boxed_461_; lean_object* v_res_462_; 
v_query_boxed_461_ = lean_unbox_uint64(v_query_457_);
lean_dec_ref(v_query_457_);
v_res_462_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(v_m_456_, v_query_boxed_461_, v_x_458_, v_x_459_, v_x_460_);
lean_dec_ref(v_m_456_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(lean_object* v_m_463_, uint64_t v_query_464_){
_start:
{
lean_object* v_keyArray_465_; lean_object* v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v_fold_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; size_t v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_keyArray_465_ = lean_ctor_get(v_m_463_, 1);
v___x_466_ = lean_array_get_size(v_keyArray_465_);
v___x_467_ = 32ULL;
v___x_468_ = lean_uint64_shift_right(v_query_464_, v___x_467_);
v_fold_469_ = lean_uint64_xor(v_query_464_, v___x_468_);
v___x_470_ = 16ULL;
v___x_471_ = lean_uint64_shift_right(v_fold_469_, v___x_470_);
v___x_472_ = lean_uint64_xor(v_fold_469_, v___x_471_);
v___x_473_ = lean_uint64_to_usize(v___x_472_);
v___x_474_ = lean_usize_of_nat(v___x_466_);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_sub(v___x_474_, v___x_475_);
v___x_477_ = lean_usize_land(v___x_473_, v___x_476_);
v___x_478_ = lean_usize_to_nat(v___x_477_);
v___x_479_ = lean_box(0);
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(v_m_463_, v_query_464_, v___x_479_, v___x_466_, v___x_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg___boxed(lean_object* v_m_481_, lean_object* v_query_482_){
_start:
{
uint64_t v_query_boxed_483_; lean_object* v_res_484_; 
v_query_boxed_483_ = lean_unbox_uint64(v_query_482_);
lean_dec_ref(v_query_482_);
v_res_484_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_m_481_, v_query_boxed_483_);
lean_dec_ref(v_m_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(lean_object* v_m_485_, uint64_t v_query_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_m_485_, v_query_486_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_index_488_; lean_object* v_key_489_; lean_object* v_value_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
v_index_488_ = lean_ctor_get(v___x_487_, 0);
v_key_489_ = lean_ctor_get(v___x_487_, 1);
v_value_490_ = lean_ctor_get(v___x_487_, 2);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_487_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_value_490_);
lean_inc(v_key_489_);
lean_inc(v_index_488_);
lean_dec(v___x_487_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_index_488_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_key_489_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_value_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
lean_object* v___x_498_; 
lean_dec(v___x_487_);
v___x_498_ = lean_box(1);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg___boxed(lean_object* v_m_499_, lean_object* v_query_500_){
_start:
{
uint64_t v_query_boxed_501_; lean_object* v_res_502_; 
v_query_boxed_501_ = lean_unbox_uint64(v_query_500_);
lean_dec_ref(v_query_500_);
v_res_502_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_m_499_, v_query_boxed_501_);
lean_dec_ref(v_m_499_);
return v_res_502_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(lean_object* v_m_503_, uint64_t v_a_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_m_503_, v_a_504_);
if (lean_obj_tag(v___x_505_) == 0)
{
uint8_t v___x_506_; 
lean_dec_ref_known(v___x_505_, 3);
v___x_506_ = 1;
return v___x_506_;
}
else
{
uint8_t v___x_507_; 
v___x_507_ = 0;
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg___boxed(lean_object* v_m_508_, lean_object* v_a_509_){
_start:
{
uint64_t v_a_boxed_510_; uint8_t v_res_511_; lean_object* v_r_512_; 
v_a_boxed_510_ = lean_unbox_uint64(v_a_509_);
lean_dec_ref(v_a_509_);
v_res_511_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_m_508_, v_a_boxed_510_);
lean_dec_ref(v_m_508_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5___redArg(lean_object* v_b_513_, lean_object* v_acc_514_, lean_object* v_i_515_){
_start:
{
lean_object* v___y_517_; lean_object* v_keyArray_525_; lean_object* v_valueArray_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_keyArray_525_ = lean_ctor_get(v_b_513_, 1);
v_valueArray_526_ = lean_ctor_get(v_b_513_, 2);
v___x_527_ = lean_array_get_size(v_keyArray_525_);
v___x_528_ = lean_nat_dec_lt(v_i_515_, v___x_527_);
if (v___x_528_ == 0)
{
lean_dec(v_i_515_);
return v_acc_514_;
}
else
{
lean_object* v___x_529_; uint8_t v_isSome_530_; 
v___x_529_ = lean_array_fget_borrowed(v_keyArray_525_, v_i_515_);
v_isSome_530_ = lean_noption_is_some(v___x_529_);
if (v_isSome_530_ == 0)
{
goto v___jp_521_;
}
else
{
lean_object* v___x_531_; uint8_t v_isSome_532_; 
v___x_531_ = lean_array_fget_borrowed(v_valueArray_526_, v_i_515_);
v_isSome_532_ = lean_noption_is_some(v___x_531_);
if (v_isSome_532_ == 0)
{
goto v___jp_521_;
}
else
{
lean_object* v_val_533_; lean_object* v_val_534_; lean_object* v_i_536_; uint64_t v___x_541_; lean_object* v___x_542_; 
lean_inc(v___x_529_);
v_val_533_ = lean_noption_get(v___x_529_);
lean_inc(v___x_531_);
v_val_534_ = lean_noption_get(v___x_531_);
v___x_541_ = lean_unbox_uint64(v_val_533_);
v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_acc_514_, v___x_541_);
switch(lean_obj_tag(v___x_542_))
{
case 0:
{
lean_object* v_index_543_; lean_object* v_size_544_; lean_object* v___x_545_; 
v_index_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_index_543_);
lean_dec_ref_known(v___x_542_, 3);
v_size_544_ = lean_ctor_get(v_acc_514_, 0);
lean_inc(v_size_544_);
v___x_545_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_514_, v_size_544_, v_index_543_, v_val_533_, v_val_534_);
lean_dec(v_index_543_);
v___y_517_ = v___x_545_;
goto v___jp_516_;
}
case 1:
{
lean_object* v_index_546_; 
v_index_546_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_index_546_);
lean_dec_ref_known(v___x_542_, 1);
v_i_536_ = v_index_546_;
goto v___jp_535_;
}
default: 
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_514_, v___x_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_index_549_; 
v_index_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_index_549_);
lean_dec_ref_known(v___x_548_, 1);
v_i_536_ = v_index_549_;
goto v___jp_535_;
}
else
{
lean_dec(v_val_534_);
lean_dec(v_val_533_);
v___y_517_ = v_acc_514_;
goto v___jp_516_;
}
}
}
v___jp_535_:
{
lean_object* v_size_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_size_537_ = lean_ctor_get(v_acc_514_, 0);
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_add(v_size_537_, v___x_538_);
v___x_540_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_514_, v___x_539_, v_i_536_, v_val_533_, v_val_534_);
lean_dec(v_i_536_);
v___y_517_ = v___x_540_;
goto v___jp_516_;
}
}
}
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_i_515_, v___x_518_);
lean_dec(v_i_515_);
v_acc_514_ = v___y_517_;
v_i_515_ = v___x_519_;
goto _start;
}
v___jp_521_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_i_515_, v___x_522_);
lean_dec(v_i_515_);
v_i_515_ = v___x_523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_550_, lean_object* v_acc_551_, lean_object* v_i_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5___redArg(v_b_550_, v_acc_551_, v_i_552_);
lean_dec_ref(v_b_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4___redArg(lean_object* v_init_554_, lean_object* v_b_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5___redArg(v_b_555_, v_init_554_, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4___redArg___boxed(lean_object* v_init_558_, lean_object* v_b_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4___redArg(v_init_558_, v_b_559_);
lean_dec_ref(v_b_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2___redArg(lean_object* v_m_561_){
_start:
{
lean_object* v_keyArray_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_cellCount_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_target_569_; lean_object* v___x_570_; 
v_keyArray_562_ = lean_ctor_get(v_m_561_, 1);
v___x_563_ = lean_array_get_size(v_keyArray_562_);
v___x_564_ = lean_unsigned_to_nat(2u);
v_cellCount_565_ = lean_nat_mul(v___x_563_, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_565_);
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_565_);
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_565_);
v_target_569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_569_, 0, v___x_566_);
lean_ctor_set(v_target_569_, 1, v___x_567_);
lean_ctor_set(v_target_569_, 2, v___x_568_);
v___x_570_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4___redArg(v_target_569_, v_m_561_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2___redArg___boxed(lean_object* v_m_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2___redArg(v_m_571_);
lean_dec_ref(v_m_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(lean_object* v_c_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_visited_575_; lean_object* v_found_576_; size_t v___x_577_; uint64_t v___x_578_; uint64_t v___x_579_; uint64_t v_addr_580_; uint8_t v___x_581_; lean_object* v___y_583_; 
v_visited_575_ = lean_ctor_get(v_a_574_, 0);
v_found_576_ = lean_ctor_get(v_a_574_, 1);
v___x_577_ = lean_ptr_addr(v_c_573_);
v___x_578_ = lean_usize_to_uint64(v___x_577_);
v___x_579_ = 2ULL;
v_addr_580_ = lean_uint64_shift_right(v___x_578_, v___x_579_);
v___x_581_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_visited_575_, v_addr_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_587_; lean_object* v___y_589_; lean_object* v_i_590_; lean_object* v___y_597_; lean_object* v___y_608_; lean_object* v_i_609_; lean_object* v___x_626_; 
lean_inc(v_found_576_);
lean_inc_ref(v_visited_575_);
lean_dec_ref(v_a_574_);
v___x_587_ = lean_box(0);
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_visited_575_, v_addr_580_);
switch(lean_obj_tag(v___x_626_))
{
case 0:
{
lean_dec_ref_known(v___x_626_, 3);
v___y_583_ = v_visited_575_;
goto v___jp_582_;
}
case 1:
{
lean_object* v_index_627_; lean_object* v_size_628_; lean_object* v_keyArray_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_index_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_index_627_);
lean_dec_ref_known(v___x_626_, 1);
v_size_628_ = lean_ctor_get(v_visited_575_, 0);
v_keyArray_629_ = lean_ctor_get(v_visited_575_, 1);
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_add(v_size_628_, v___x_630_);
v___x_632_ = lean_array_get_size(v_keyArray_629_);
v___x_633_ = lean_nat_dec_lt(v___x_631_, v___x_632_);
if (v___x_633_ == 0)
{
lean_dec(v___x_631_);
lean_dec(v_index_627_);
goto v___jp_615_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_634_ = lean_unsigned_to_nat(4u);
v___x_635_ = lean_nat_mul(v___x_631_, v___x_634_);
v___x_636_ = lean_unsigned_to_nat(3u);
v___x_637_ = lean_nat_mul(v___x_632_, v___x_636_);
v___x_638_ = lean_nat_dec_le(v___x_635_, v___x_637_);
lean_dec(v___x_637_);
lean_dec(v___x_635_);
if (v___x_638_ == 0)
{
lean_dec(v___x_631_);
lean_dec(v_index_627_);
goto v___jp_615_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_box_uint64(v_addr_580_);
v___x_640_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visited_575_, v___x_631_, v_index_627_, v___x_639_, v___x_587_);
lean_dec(v_index_627_);
v___y_583_ = v___x_640_;
goto v___jp_582_;
}
}
}
default: 
{
lean_object* v_size_641_; lean_object* v_keyArray_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_size_641_ = lean_ctor_get(v_visited_575_, 0);
v_keyArray_642_ = lean_ctor_get(v_visited_575_, 1);
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_add(v_size_641_, v___x_643_);
v___x_645_ = lean_array_get_size(v_keyArray_642_);
v___x_646_ = lean_nat_dec_lt(v___x_644_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_dec(v___x_644_);
v___x_647_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2___redArg(v_visited_575_);
lean_dec_ref(v_visited_575_);
v___y_597_ = v___x_647_;
goto v___jp_596_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_648_ = lean_unsigned_to_nat(4u);
v___x_649_ = lean_nat_mul(v___x_644_, v___x_648_);
lean_dec(v___x_644_);
v___x_650_ = lean_unsigned_to_nat(3u);
v___x_651_ = lean_nat_mul(v___x_645_, v___x_650_);
v___x_652_ = lean_nat_dec_le(v___x_649_, v___x_651_);
lean_dec(v___x_651_);
lean_dec(v___x_649_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2___redArg(v_visited_575_);
lean_dec_ref(v_visited_575_);
v___y_597_ = v___x_653_;
goto v___jp_596_;
}
else
{
v___y_597_ = v_visited_575_;
goto v___jp_596_;
}
}
}
}
v___jp_588_:
{
lean_object* v_size_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_size_591_ = lean_ctor_get(v___y_589_, 0);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_add(v_size_591_, v___x_592_);
v___x_594_ = lean_box_uint64(v_addr_580_);
v___x_595_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_589_, v___x_593_, v_i_590_, v___x_594_, v___x_587_);
lean_dec(v_i_590_);
v___y_583_ = v___x_595_;
goto v___jp_582_;
}
v___jp_596_:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v___y_597_, v_addr_580_);
switch(lean_obj_tag(v___x_598_))
{
case 0:
{
lean_object* v_index_599_; lean_object* v_size_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_index_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_index_599_);
lean_dec_ref_known(v___x_598_, 3);
v_size_600_ = lean_ctor_get(v___y_597_, 0);
lean_inc(v_size_600_);
v___x_601_ = lean_box_uint64(v_addr_580_);
v___x_602_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_597_, v_size_600_, v_index_599_, v___x_601_, v___x_587_);
lean_dec(v_index_599_);
v___y_583_ = v___x_602_;
goto v___jp_582_;
}
case 1:
{
lean_object* v_index_603_; 
v_index_603_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_index_603_);
lean_dec_ref_known(v___x_598_, 1);
v___y_589_ = v___y_597_;
v_i_590_ = v_index_603_;
goto v___jp_588_;
}
default: 
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_597_, v___x_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_index_606_; 
v_index_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_index_606_);
lean_dec_ref_known(v___x_605_, 1);
v___y_589_ = v___y_597_;
v_i_590_ = v_index_606_;
goto v___jp_588_;
}
else
{
v___y_583_ = v___y_597_;
goto v___jp_582_;
}
}
}
}
v___jp_607_:
{
lean_object* v_size_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_size_610_ = lean_ctor_get(v___y_608_, 0);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_add(v_size_610_, v___x_611_);
v___x_613_ = lean_box_uint64(v_addr_580_);
v___x_614_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_608_, v___x_612_, v_i_609_, v___x_613_, v___x_587_);
lean_dec(v_i_609_);
v___y_583_ = v___x_614_;
goto v___jp_582_;
}
v___jp_615_:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2___redArg(v_visited_575_);
lean_dec_ref(v_visited_575_);
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v___x_616_, v_addr_580_);
switch(lean_obj_tag(v___x_617_))
{
case 0:
{
lean_object* v_index_618_; lean_object* v_size_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_index_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_index_618_);
lean_dec_ref_known(v___x_617_, 3);
v_size_619_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_size_619_);
v___x_620_ = lean_box_uint64(v_addr_580_);
v___x_621_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_616_, v_size_619_, v_index_618_, v___x_620_, v___x_587_);
lean_dec(v_index_618_);
v___y_583_ = v___x_621_;
goto v___jp_582_;
}
case 1:
{
lean_object* v_index_622_; 
v_index_622_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_index_622_);
lean_dec_ref_known(v___x_617_, 1);
v___y_608_ = v___x_616_;
v_i_609_ = v_index_622_;
goto v___jp_607_;
}
default: 
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_616_, v___x_623_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_index_625_; 
v_index_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_index_625_);
lean_dec_ref_known(v___x_624_, 1);
v___y_608_ = v___x_616_;
v_i_609_ = v_index_625_;
goto v___jp_607_;
}
else
{
v___y_583_ = v___x_616_;
goto v___jp_582_;
}
}
}
}
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_box(v___x_581_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_a_574_);
return v___x_655_;
}
v___jp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___y_583_);
lean_ctor_set(v___x_584_, 1, v_found_576_);
v___x_585_ = lean_box(v___x_581_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg___boxed(lean_object* v_c_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(v_c_656_, v_a_657_);
lean_dec(v_c_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(lean_object* v_00_u03b1_659_, lean_object* v_c_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___redArg(v_c_660_, v_a_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited___boxed(lean_object* v_00_u03b1_664_, lean_object* v_c_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited(v_00_u03b1_664_, v_c_665_, v_a_666_, v_a_667_);
lean_dec(v_a_666_);
lean_dec(v_c_665_);
return v_res_668_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(lean_object* v_00_u03b2_669_, lean_object* v_m_670_, uint64_t v_a_671_){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___redArg(v_m_670_, v_a_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0___boxed(lean_object* v_00_u03b2_673_, lean_object* v_m_674_, lean_object* v_a_675_){
_start:
{
uint64_t v_a_boxed_676_; uint8_t v_res_677_; lean_object* v_r_678_; 
v_a_boxed_676_ = lean_unbox_uint64(v_a_675_);
lean_dec_ref(v_a_675_);
v_res_677_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0(v_00_u03b2_673_, v_m_674_, v_a_boxed_676_);
lean_dec_ref(v_m_674_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(lean_object* v_00_u03b2_679_, lean_object* v_m_680_, uint64_t v_query_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___redArg(v_m_680_, v_query_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1___boxed(lean_object* v_00_u03b2_683_, lean_object* v_m_684_, lean_object* v_query_685_){
_start:
{
uint64_t v_query_boxed_686_; lean_object* v_res_687_; 
v_query_boxed_686_ = lean_unbox_uint64(v_query_685_);
lean_dec_ref(v_query_685_);
v_res_687_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1(v_00_u03b2_683_, v_m_684_, v_query_boxed_686_);
lean_dec_ref(v_m_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2(lean_object* v_00_u03b2_688_, lean_object* v_m_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2___redArg(v_m_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2___boxed(lean_object* v_00_u03b2_691_, lean_object* v_m_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2(v_00_u03b2_691_, v_m_692_);
lean_dec_ref(v_m_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(lean_object* v_00_u03b2_694_, lean_object* v_m_695_, uint64_t v_query_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___redArg(v_m_695_, v_query_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0___boxed(lean_object* v_00_u03b2_698_, lean_object* v_m_699_, lean_object* v_query_700_){
_start:
{
uint64_t v_query_boxed_701_; lean_object* v_res_702_; 
v_query_boxed_701_ = lean_unbox_uint64(v_query_700_);
lean_dec_ref(v_query_700_);
v_res_702_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__0_spec__0(v_00_u03b2_698_, v_m_699_, v_query_boxed_701_);
lean_dec_ref(v_m_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2(lean_object* v_00_u03b2_703_, lean_object* v_m_704_, uint64_t v_query_705_, lean_object* v_x_706_, lean_object* v_x_707_, lean_object* v_x_708_, lean_object* v_x_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___redArg(v_m_704_, v_query_705_, v_x_706_, v_x_707_, v_x_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2___boxed(lean_object* v_00_u03b2_711_, lean_object* v_m_712_, lean_object* v_query_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
uint64_t v_query_boxed_718_; lean_object* v_res_719_; 
v_query_boxed_718_ = lean_unbox_uint64(v_query_713_);
lean_dec_ref(v_query_713_);
v_res_719_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__1_spec__2(v_00_u03b2_711_, v_m_712_, v_query_boxed_718_, v_x_714_, v_x_715_, v_x_716_, v_x_717_);
lean_dec_ref(v_m_712_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4(lean_object* v_00_u03b2_720_, lean_object* v_init_721_, lean_object* v_b_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4___redArg(v_init_721_, v_b_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4___boxed(lean_object* v_00_u03b2_724_, lean_object* v_init_725_, lean_object* v_b_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4(v_00_u03b2_724_, v_init_725_, v_b_726_);
lean_dec_ref(v_b_726_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_728_, lean_object* v_b_729_, lean_object* v_acc_730_, lean_object* v_i_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5___redArg(v_b_729_, v_acc_730_, v_i_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_733_, lean_object* v_b_734_, lean_object* v_acc_735_, lean_object* v_i_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_Arith_CollectDecVars_alreadyVisited_spec__2_spec__4_spec__5(v_00_u03b2_733_, v_b_734_, v_acc_735_, v_i_736_);
lean_dec_ref(v_b_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(lean_object* v_fvarId_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_visited_740_; lean_object* v_found_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_751_; 
v_visited_740_ = lean_ctor_get(v_a_739_, 0);
v_found_741_ = lean_ctor_get(v_a_739_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_a_739_);
if (v_isSharedCheck_751_ == 0)
{
v___x_743_ = v_a_739_;
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_found_741_);
lean_inc(v_visited_740_);
lean_dec(v_a_739_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_745_ = lean_box(0);
v___x_746_ = l_Lean_FVarIdSet_insert(v_found_741_, v_fvarId_738_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_746_);
v___x_748_ = v___x_743_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_visited_740_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_746_);
v___x_748_ = v_reuseFailAlloc_750_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_745_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(lean_object* v_fvarId_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___redArg(v_fvarId_752_, v_a_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound___boxed(lean_object* v_fvarId_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Meta_Grind_Arith_CollectDecVars_markAsFound(v_fvarId_756_, v_a_757_, v_a_758_);
lean_dec(v_a_757_);
return v_res_759_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0(void){
_start:
{
lean_object* v_cellCount_760_; lean_object* v___x_761_; 
v_cellCount_760_ = lean_unsigned_to_nat(16u);
v___x_761_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1(void){
_start:
{
lean_object* v_cellCount_762_; lean_object* v___x_763_; 
v_cellCount_762_ = lean_unsigned_to_nat(16u);
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_762_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_764_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__1);
v___x_765_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__0);
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
lean_ctor_set(v___x_767_, 2, v___x_764_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_box(1);
v___x_769_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__2);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run(lean_object* v_x_771_, lean_object* v_decVars_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_snd_775_; lean_object* v_found_776_; 
v___x_773_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3, &l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CollectDecVars_CollectDecVarsM_run___closed__3);
v___x_774_ = lean_apply_2(v_x_771_, v_decVars_772_, v___x_773_);
v_snd_775_ = lean_ctor_get(v___x_774_, 1);
lean_inc(v_snd_775_);
lean_dec_ref(v___x_774_);
v_found_776_ = lean_ctor_get(v_snd_775_, 1);
lean_inc(v_found_776_);
lean_dec(v_snd_775_);
return v_found_776_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Grind_Arith_Util_0__Lean_Meta_Grind_Arith_________intModuleMarker________(void){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = 1;
return v___x_777_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_box(0);
v___x_826_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__20));
v___x_827_ = l_Lean_mkConst(v___x_826_, v___x_825_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent(void){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21, &l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21_once, _init_l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent___closed__21);
return v___x_828_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object* v_parent_x3f_829_){
_start:
{
if (lean_obj_tag(v_parent_x3f_829_) == 0)
{
uint8_t v___x_830_; 
v___x_830_ = 0;
return v___x_830_;
}
else
{
lean_object* v_val_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_val_831_ = lean_ctor_get(v_parent_x3f_829_, 0);
v___x_832_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
v___x_833_ = lean_expr_eqv(v_val_831_, v___x_832_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent___boxed(lean_object* v_parent_x3f_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_834_);
lean_dec(v_parent_x3f_834_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___lam__0(lean_object* v_getCoeff_837_, lean_object* v___x_838_, lean_object* v_c_839_, lean_object* v_____s_840_){
_start:
{
lean_object* v_fst_841_; lean_object* v_snd_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_860_; 
v_fst_841_ = lean_ctor_get(v_____s_840_, 0);
v_snd_842_ = lean_ctor_get(v_____s_840_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_____s_840_);
if (v_isSharedCheck_860_ == 0)
{
v___x_844_ = v_____s_840_;
v_isShared_845_ = v_isSharedCheck_860_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_snd_842_);
lean_inc(v_fst_841_);
lean_dec(v_____s_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_860_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_b_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
lean_inc(v_c_839_);
v_b_846_ = lean_apply_1(v_getCoeff_837_, v_c_839_);
v___x_847_ = lean_nat_to_int(v___x_838_);
v___x_848_ = lean_int_dec_eq(v_b_846_, v___x_847_);
lean_dec(v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_850_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_c_839_);
lean_ctor_set(v___x_844_, 0, v_b_846_);
v___x_850_ = v___x_844_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_b_846_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_c_839_);
v___x_850_ = v_reuseFailAlloc_854_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v_todo_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_todo_851_ = lean_array_push(v_snd_842_, v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v_fst_841_);
lean_ctor_set(v___x_852_, 1, v_todo_851_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
else
{
lean_object* v_cs_x27_855_; lean_object* v___x_857_; 
lean_dec(v_b_846_);
v_cs_x27_855_ = l_Lean_PersistentArray_push___redArg(v_fst_841_, v_c_839_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v_cs_x27_855_);
v___x_857_ = v___x_844_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_cs_x27_855_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_snd_842_);
v___x_857_ = v_reuseFailAlloc_859_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_unsigned_to_nat(32u);
v___x_881_ = lean_mk_empty_array_with_capacity(v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11(void){
_start:
{
size_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v_cs_x27_888_; 
v___x_883_ = ((size_t)5ULL);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_unsigned_to_nat(32u);
v___x_886_ = lean_mk_empty_array_with_capacity(v___x_885_);
v___x_887_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__10, &l_Lean_Meta_Grind_Arith_split___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__10);
v_cs_x27_888_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_888_, 0, v___x_887_);
lean_ctor_set(v_cs_x27_888_, 1, v___x_886_);
lean_ctor_set(v_cs_x27_888_, 2, v___x_884_);
lean_ctor_set(v_cs_x27_888_, 3, v___x_884_);
lean_ctor_set_usize(v_cs_x27_888_, 4, v___x_883_);
return v_cs_x27_888_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13(void){
_start:
{
lean_object* v_todo_891_; lean_object* v_cs_x27_892_; lean_object* v___x_893_; 
v_todo_891_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___redArg___closed__12));
v_cs_x27_892_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__11, &l_Lean_Meta_Grind_Arith_split___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__11);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_cs_x27_892_);
lean_ctor_set(v___x_893_, 1, v_todo_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg(lean_object* v_cs_894_, lean_object* v_getCoeff_895_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_fst_901_; lean_object* v_snd_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
v___x_896_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___redArg___closed__9));
v___x_897_ = lean_unsigned_to_nat(0u);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_split___redArg___lam__0), 4, 2);
lean_closure_set(v___f_898_, 0, v_getCoeff_895_);
lean_closure_set(v___f_898_, 1, v___x_897_);
v___x_899_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___redArg___closed__13, &l_Lean_Meta_Grind_Arith_split___redArg___closed__13_once, _init_l_Lean_Meta_Grind_Arith_split___redArg___closed__13);
v___x_900_ = l_Lean_PersistentArray_forIn___redArg(v___x_896_, v_cs_894_, v___x_899_, v___f_898_);
v_fst_901_ = lean_ctor_get(v___x_900_, 0);
v_snd_902_ = lean_ctor_get(v___x_900_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_900_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_snd_902_);
lean_inc(v_fst_901_);
lean_dec(v___x_900_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_fst_901_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_snd_902_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___redArg___boxed(lean_object* v_cs_910_, lean_object* v_getCoeff_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Meta_Grind_Arith_split___redArg(v_cs_910_, v_getCoeff_911_);
lean_dec_ref(v_cs_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split(lean_object* v_00_u03b1_913_, lean_object* v_cs_914_, lean_object* v_getCoeff_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_Meta_Grind_Arith_split___redArg(v_cs_914_, v_getCoeff_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___boxed(lean_object* v_00_u03b1_917_, lean_object* v_cs_918_, lean_object* v_getCoeff_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Meta_Grind_Arith_split(v_00_u03b1_917_, v_cs_918_, v_getCoeff_919_);
lean_dec_ref(v_cs_918_);
return v_res_920_;
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
