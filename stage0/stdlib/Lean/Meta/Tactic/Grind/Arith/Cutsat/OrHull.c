// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.OrHull
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Init.Data.Int.OfNat import Lean.Meta.NatInstTesters import Lean.Meta.IntInstTesters import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_addConst(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstLENat___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getDisjuncts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getDisjuncts___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getDisjuncts___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getDisjuncts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getDisjuncts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getDisjuncts___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getDisjuncts___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getDisjuncts(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "of_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__2_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__3_value),LEAN_SCALAR_PTR_LITERAL(105, 164, 65, 191, 194, 192, 188, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "of_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__2_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 9, 233, 146, 238, 75, 109, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__8(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__7___boxed(lean_object**);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getDisjuncts(lean_object* v_e_4_, lean_object* v_acc_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = l_Lean_Expr_cleanupAnnotations(v_e_4_);
v___x_7_ = l_Lean_Expr_isApp(v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
lean_dec_ref(v___x_6_);
v___x_8_ = lean_array_push(v_acc_5_, v_e_4_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6_);
v___x_10_ = l_Lean_Expr_isApp(v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
lean_dec_ref(v___x_9_);
lean_dec_ref(v___x_6_);
v___x_11_ = lean_array_push(v_acc_5_, v_e_4_);
return v___x_11_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_12_ = l_Lean_Expr_appFnCleanup___redArg(v___x_9_);
v___x_13_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getDisjuncts___closed__1));
v___x_14_ = l_Lean_Expr_isConstOf(v___x_12_, v___x_13_);
lean_dec_ref(v___x_12_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
lean_dec_ref(v___x_9_);
lean_dec_ref(v___x_6_);
v___x_15_ = lean_array_push(v_acc_5_, v_e_4_);
return v___x_15_;
}
else
{
lean_object* v_arg_16_; lean_object* v_arg_17_; lean_object* v___x_18_; 
lean_dec_ref(v_e_4_);
v_arg_16_ = lean_ctor_get(v___x_6_, 1);
lean_inc_ref(v_arg_16_);
lean_dec_ref(v___x_6_);
v_arg_17_ = lean_ctor_get(v___x_9_, 1);
lean_inc_ref(v_arg_17_);
lean_dec_ref(v___x_9_);
v___x_18_ = lean_array_push(v_acc_5_, v_arg_17_);
v_e_4_ = v_arg_16_;
v_acc_5_ = v___x_18_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(lean_object* v_00_u03b1_26_){
_start:
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1));
v___x_28_ = l_Lean_Expr_isConstOf(v_00_u03b1_26_, v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__3));
v___x_30_ = l_Lean_Expr_isConstOf(v_00_u03b1_26_, v___x_29_);
return v___x_30_;
}
else
{
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___boxed(lean_object* v_00_u03b1_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(v_00_u03b1_31_);
lean_dec_ref(v_00_u03b1_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom(lean_object* v_e_42_){
_start:
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = l_Lean_Expr_cleanupAnnotations(v_e_42_);
v___x_44_ = l_Lean_Expr_isApp(v___x_43_);
if (v___x_44_ == 0)
{
lean_dec_ref(v___x_43_);
return v___x_44_;
}
else
{
lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_45_ = l_Lean_Expr_appFnCleanup___redArg(v___x_43_);
lean_dec_ref(v___x_43_);
v___x_46_ = l_Lean_Expr_isApp(v___x_45_);
if (v___x_46_ == 0)
{
lean_dec_ref(v___x_45_);
return v___x_46_;
}
else
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = l_Lean_Expr_appFnCleanup___redArg(v___x_45_);
lean_dec_ref(v___x_45_);
v___x_48_ = l_Lean_Expr_isApp(v___x_47_);
if (v___x_48_ == 0)
{
lean_dec_ref(v___x_47_);
return v___x_48_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_49_ = l_Lean_Expr_appFnCleanup___redArg(v___x_47_);
v___x_50_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__1));
v___x_51_ = l_Lean_Expr_isConstOf(v___x_49_, v___x_50_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; 
lean_dec_ref(v___x_47_);
v___x_52_ = l_Lean_Expr_isApp(v___x_49_);
if (v___x_52_ == 0)
{
lean_dec_ref(v___x_49_);
return v___x_52_;
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_53_ = l_Lean_Expr_appFnCleanup___redArg(v___x_49_);
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4));
v___x_55_ = l_Lean_Expr_isConstOf(v___x_53_, v___x_54_);
lean_dec_ref(v___x_53_);
if (v___x_55_ == 0)
{
lean_dec_ref(v___x_49_);
return v___x_55_;
}
else
{
lean_object* v_arg_56_; uint8_t v___x_57_; 
v_arg_56_ = lean_ctor_get(v___x_49_, 1);
lean_inc_ref(v_arg_56_);
lean_dec_ref(v___x_49_);
v___x_57_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(v_arg_56_);
lean_dec_ref(v_arg_56_);
return v___x_57_;
}
}
}
else
{
lean_object* v_arg_58_; uint8_t v___x_59_; 
lean_dec_ref(v___x_49_);
v_arg_58_ = lean_ctor_get(v___x_47_, 1);
lean_inc_ref(v_arg_58_);
lean_dec_ref(v___x_47_);
v___x_59_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(v_arg_58_);
lean_dec_ref(v_arg_58_);
return v___x_59_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___boxed(lean_object* v_e_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom(v_e_60_);
lean_dec_ref(v_e_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts(lean_object* v_d_66_, lean_object* v_revPath_67_, lean_object* v_acc_68_){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = l_Lean_Expr_cleanupAnnotations(v_d_66_);
v___x_75_ = l_Lean_Expr_isApp(v___x_74_);
if (v___x_75_ == 0)
{
lean_dec_ref(v___x_74_);
goto v___jp_69_;
}
else
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = l_Lean_Expr_appFnCleanup___redArg(v___x_74_);
v___x_77_ = l_Lean_Expr_isApp(v___x_76_);
if (v___x_77_ == 0)
{
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_74_);
goto v___jp_69_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_78_ = l_Lean_Expr_appFnCleanup___redArg(v___x_76_);
v___x_79_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts___closed__1));
v___x_80_ = l_Lean_Expr_isConstOf(v___x_78_, v___x_79_);
lean_dec_ref(v___x_78_);
if (v___x_80_ == 0)
{
lean_dec_ref(v___x_76_);
lean_dec_ref(v___x_74_);
goto v___jp_69_;
}
else
{
lean_object* v_arg_81_; lean_object* v_arg_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec_ref(v_d_66_);
v_arg_81_ = lean_ctor_get(v___x_74_, 1);
lean_inc_ref(v_arg_81_);
lean_dec_ref(v___x_74_);
v_arg_82_ = lean_ctor_get(v___x_76_, 1);
lean_inc_ref(v_arg_82_);
lean_dec_ref(v___x_76_);
v___x_83_ = lean_box(v___x_80_);
lean_inc(v_revPath_67_);
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v_revPath_67_);
v___x_85_ = 0;
v___x_86_ = lean_box(v___x_85_);
v___x_87_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_revPath_67_);
v___x_88_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts(v_arg_82_, v___x_87_, v_acc_68_);
v_d_66_ = v_arg_81_;
v_revPath_67_ = v___x_84_;
v_acc_68_ = v___x_88_;
goto _start;
}
}
}
v___jp_69_:
{
uint8_t v___x_70_; 
v___x_70_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom(v_d_66_);
if (v___x_70_ == 0)
{
lean_dec(v_revPath_67_);
lean_dec_ref(v_d_66_);
return v_acc_68_;
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = l_List_reverse___redArg(v_revPath_67_);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v_d_66_);
v___x_73_ = lean_array_push(v_acc_68_, v___x_72_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry(lean_object* v_p_90_, lean_object* v_alt_91_, lean_object* v_entries_92_){
_start:
{
lean_object* v_k_93_; lean_object* v___x_94_; lean_object* v_lin_95_; 
v_k_93_ = l_Int_Internal_Linear_Poly_getConst(v_p_90_);
v___x_94_ = lean_int_neg(v_k_93_);
v_lin_95_ = l_Int_Internal_Linear_Poly_addConst(v_p_90_, v___x_94_);
lean_dec(v___x_94_);
if (lean_obj_tag(v_lin_95_) == 0)
{
lean_dec_ref_known(v_lin_95_, 1);
lean_dec(v_k_93_);
lean_dec_ref(v_alt_91_);
return v_entries_92_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_96_, 0, v_lin_95_);
lean_ctor_set(v___x_96_, 1, v_k_93_);
lean_ctor_set(v___x_96_, 2, v_alt_91_);
v___x_97_ = lean_array_push(v_entries_92_, v___x_96_);
return v___x_97_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0___closed__0(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_nat_to_int(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0(lean_object* v_path_100_, lean_object* v_snd_101_, lean_object* v_a_102_, lean_object* v_a_103_, uint8_t v_kind_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0___closed__0);
v___x_106_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_106_, 0, v_path_100_);
lean_ctor_set(v___x_106_, 1, v_snd_101_);
lean_ctor_set(v___x_106_, 2, v_a_102_);
lean_ctor_set(v___x_106_, 3, v_a_103_);
lean_ctor_set(v___x_106_, 4, v___x_105_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*5, v_kind_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0___boxed(lean_object* v_path_107_, lean_object* v_snd_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_kind_111_){
_start:
{
uint8_t v_kind_boxed_112_; lean_object* v_res_113_; 
v_kind_boxed_112_ = lean_unbox(v_kind_111_);
v_res_113_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0(v_path_107_, v_snd_108_, v_a_109_, v_a_110_, v_kind_boxed_112_);
return v_res_113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__0(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_to_int(v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__1(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__0);
v___x_117_ = lean_int_neg(v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries(lean_object* v_gen_129_, lean_object* v_path_130_, lean_object* v_c_131_, lean_object* v_entries_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
uint8_t v___y_145_; lean_object* v_fst_146_; lean_object* v_fst_147_; lean_object* v_snd_148_; lean_object* v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; uint8_t v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v_fst_226_; lean_object* v_fst_227_; uint8_t v_fst_228_; uint8_t v_snd_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___x_269_; 
v___x_269_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_131_, v_a_140_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_359_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_359_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_359_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_359_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = l_Lean_Expr_cleanupAnnotations(v_a_270_);
lean_dec(v_a_270_);
v___x_275_ = l_Lean_Expr_isApp(v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_277_; 
lean_dec_ref(v___x_274_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v_entries_132_);
v___x_277_ = v___x_272_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_entries_132_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
else
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = l_Lean_Expr_appFnCleanup___redArg(v___x_274_);
v___x_280_ = l_Lean_Expr_isApp(v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_282_; 
lean_dec_ref(v___x_279_);
lean_dec_ref(v___x_274_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v_entries_132_);
v___x_282_ = v___x_272_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_entries_132_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
else
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = l_Lean_Expr_appFnCleanup___redArg(v___x_279_);
v___x_285_ = l_Lean_Expr_isApp(v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_287_; 
lean_dec_ref(v___x_284_);
lean_dec_ref(v___x_279_);
lean_dec_ref(v___x_274_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v_entries_132_);
v___x_287_ = v___x_272_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_entries_132_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
else
{
lean_object* v_arg_289_; lean_object* v_arg_290_; lean_object* v_arg_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_arg_289_ = lean_ctor_get(v___x_274_, 1);
lean_inc_ref(v_arg_289_);
lean_dec_ref(v___x_274_);
v_arg_290_ = lean_ctor_get(v___x_279_, 1);
lean_inc_ref(v_arg_290_);
lean_dec_ref(v___x_279_);
v_arg_291_ = lean_ctor_get(v___x_284_, 1);
lean_inc_ref(v_arg_291_);
v___x_292_ = l_Lean_Expr_appFnCleanup___redArg(v___x_284_);
lean_dec_ref(v___x_284_);
v___x_293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__1));
v___x_294_ = l_Lean_Expr_isConstOf(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
uint8_t v___x_295_; 
v___x_295_ = l_Lean_Expr_isApp(v___x_292_);
if (v___x_295_ == 0)
{
lean_object* v___x_297_; 
lean_dec_ref(v___x_292_);
lean_dec_ref(v_arg_291_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_289_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v_entries_132_);
v___x_297_ = v___x_272_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_entries_132_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_292_);
v___x_300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4));
v___x_301_ = l_Lean_Expr_isConstOf(v___x_299_, v___x_300_);
lean_dec_ref(v___x_299_);
if (v___x_301_ == 0)
{
lean_object* v___x_303_; 
lean_dec_ref(v___x_292_);
lean_dec_ref(v_arg_291_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_289_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v_entries_132_);
v___x_303_ = v___x_272_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_entries_132_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
else
{
lean_object* v_arg_305_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___x_319_; uint8_t v___x_320_; 
lean_del_object(v___x_272_);
v_arg_305_ = lean_ctor_get(v___x_292_, 1);
lean_inc_ref(v_arg_305_);
lean_dec_ref(v___x_292_);
v___x_319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1));
v___x_320_ = l_Lean_Expr_isConstOf(v_arg_305_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_291_, v_a_140_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_330_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_330_ == 0)
{
v___x_324_ = v___x_321_;
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
uint8_t v___x_326_; 
v___x_326_ = lean_unbox(v_a_322_);
lean_dec(v_a_322_);
if (v___x_326_ == 0)
{
lean_object* v___x_328_; 
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_289_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v_entries_132_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_entries_132_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
else
{
lean_del_object(v___x_324_);
v___y_307_ = v_a_133_;
v___y_308_ = v_a_134_;
v___y_309_ = v_a_135_;
v___y_310_ = v_a_136_;
v___y_311_ = v_a_137_;
v___y_312_ = v_a_138_;
v___y_313_ = v_a_139_;
v___y_314_ = v_a_140_;
v___y_315_ = v_a_141_;
v___y_316_ = v_a_142_;
goto v___jp_306_;
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_289_);
lean_dec_ref(v_entries_132_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
v_a_331_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_321_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_321_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
else
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_arg_291_, v_a_140_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint8_t v___x_344_; 
v___x_344_ = lean_unbox(v_a_340_);
lean_dec(v_a_340_);
if (v___x_344_ == 0)
{
lean_object* v___x_346_; 
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_289_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v_entries_132_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_entries_132_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
else
{
lean_del_object(v___x_342_);
v___y_307_ = v_a_133_;
v___y_308_ = v_a_134_;
v___y_309_ = v_a_135_;
v___y_310_ = v_a_136_;
v___y_311_ = v_a_137_;
v___y_312_ = v_a_138_;
v___y_313_ = v_a_139_;
v___y_314_ = v_a_140_;
v___y_315_ = v_a_141_;
v___y_316_ = v_a_142_;
goto v___jp_306_;
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec_ref(v_arg_305_);
lean_dec_ref(v_arg_290_);
lean_dec_ref(v_arg_289_);
lean_dec_ref(v_entries_132_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
v_a_349_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_339_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_339_);
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
v___jp_306_:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1));
v___x_318_ = l_Lean_Expr_isConstOf(v_arg_305_, v___x_317_);
lean_dec_ref(v_arg_305_);
v_fst_226_ = v_arg_290_;
v_fst_227_ = v_arg_289_;
v_fst_228_ = v___x_294_;
v_snd_229_ = v___x_318_;
v___y_230_ = v___y_307_;
v___y_231_ = v___y_308_;
v___y_232_ = v___y_309_;
v___y_233_ = v___y_310_;
v___y_234_ = v___y_311_;
v___y_235_ = v___y_312_;
v___y_236_ = v___y_313_;
v___y_237_ = v___y_314_;
v___y_238_ = v___y_315_;
v___y_239_ = v___y_316_;
goto v___jp_225_;
}
}
}
}
else
{
lean_object* v___x_357_; uint8_t v___x_358_; 
lean_dec_ref(v___x_292_);
lean_del_object(v___x_272_);
v___x_357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1));
v___x_358_ = l_Lean_Expr_isConstOf(v_arg_291_, v___x_357_);
lean_dec_ref(v_arg_291_);
v_fst_226_ = v_arg_290_;
v_fst_227_ = v_arg_289_;
v_fst_228_ = v___x_294_;
v_snd_229_ = v___x_358_;
v___y_230_ = v_a_133_;
v___y_231_ = v_a_134_;
v___y_232_ = v_a_135_;
v___y_233_ = v_a_136_;
v___y_234_ = v_a_137_;
v___y_235_ = v_a_138_;
v___y_236_ = v_a_139_;
v___y_237_ = v_a_140_;
v___y_238_ = v_a_141_;
v___y_239_ = v_a_142_;
goto v___jp_225_;
}
}
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec_ref(v_entries_132_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
v_a_360_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_269_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_269_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
v___jp_144_:
{
lean_object* v___x_159_; 
lean_inc(v_gen_129_);
v___x_159_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_146_, v_gen_129_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_161_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v___x_159_, 1);
v___x_161_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_147_, v_gen_129_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_185_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_185_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_185_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_185_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_inc(v_a_162_);
lean_inc(v_a_160_);
v___x_166_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_166_, 0, v_a_160_);
lean_ctor_set(v___x_166_, 1, v_a_162_);
v___x_167_ = l_Int_Internal_Linear_Expr_norm(v___x_166_);
lean_dec_ref_known(v___x_166_, 2);
if (v___y_145_ == 0)
{
uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_168_ = 0;
v___x_169_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0(v_path_130_, v_snd_148_, v_a_160_, v_a_162_, v___x_168_);
v___x_170_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry(v___x_167_, v___x_169_, v_entries_132_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_170_);
v___x_172_ = v___x_164_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__1);
lean_inc_ref(v___x_167_);
v___x_175_ = l_Int_Internal_Linear_Poly_mul(v___x_167_, v___x_174_);
v___x_176_ = 2;
lean_inc(v_a_162_);
lean_inc(v_a_160_);
lean_inc(v_snd_148_);
lean_inc(v_path_130_);
v___x_177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0(v_path_130_, v_snd_148_, v_a_160_, v_a_162_, v___x_176_);
v___x_178_ = 1;
v___x_179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___lam__0(v_path_130_, v_snd_148_, v_a_160_, v_a_162_, v___x_178_);
v___x_180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry(v___x_167_, v___x_179_, v_entries_132_);
v___x_181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry(v___x_175_, v___x_177_, v___x_180_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_181_);
v___x_183_ = v___x_164_;
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
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec(v_a_160_);
lean_dec(v_snd_148_);
lean_dec_ref(v_entries_132_);
lean_dec(v_path_130_);
v_a_186_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_161_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_161_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec(v_snd_148_);
lean_dec_ref(v_fst_147_);
lean_dec_ref(v_entries_132_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
v_a_194_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_159_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_159_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
v___jp_202_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_221_ = lean_box(0);
lean_inc(v___y_220_);
v___x_222_ = l_Lean_mkConst(v___y_220_, v___x_221_);
lean_inc_ref(v___y_206_);
lean_inc_ref(v___y_203_);
v___x_223_ = l_Lean_mkApp6(v___x_222_, v___y_211_, v___y_212_, v___y_203_, v___y_206_, v___y_208_, v___y_207_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
v___y_145_ = v___y_216_;
v_fst_146_ = v___y_203_;
v_fst_147_ = v___y_206_;
v_snd_148_ = v___x_224_;
v___y_149_ = v___y_204_;
v___y_150_ = v___y_217_;
v___y_151_ = v___y_205_;
v___y_152_ = v___y_218_;
v___y_153_ = v___y_213_;
v___y_154_ = v___y_215_;
v___y_155_ = v___y_210_;
v___y_156_ = v___y_214_;
v___y_157_ = v___y_209_;
v___y_158_ = v___y_219_;
goto v___jp_144_;
}
v___jp_225_:
{
if (v_snd_229_ == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_box(0);
v___y_145_ = v_fst_228_;
v_fst_146_ = v_fst_226_;
v_fst_147_ = v_fst_227_;
v_snd_148_ = v___x_240_;
v___y_149_ = v___y_230_;
v___y_150_ = v___y_231_;
v___y_151_ = v___y_232_;
v___y_152_ = v___y_233_;
v___y_153_ = v___y_234_;
v___y_154_ = v___y_235_;
v___y_155_ = v___y_236_;
v___y_156_ = v___y_237_;
v___y_157_ = v___y_238_;
v___y_158_ = v___y_239_;
goto v___jp_144_;
}
else
{
lean_object* v___x_241_; 
lean_inc_ref(v_fst_226_);
v___x_241_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_fst_226_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v_fst_243_; lean_object* v_snd_244_; lean_object* v___x_245_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_a_242_);
lean_dec_ref_known(v___x_241_, 1);
v_fst_243_ = lean_ctor_get(v_a_242_, 0);
lean_inc(v_fst_243_);
v_snd_244_ = lean_ctor_get(v_a_242_, 1);
lean_inc(v_snd_244_);
lean_dec(v_a_242_);
lean_inc_ref(v_fst_227_);
v___x_245_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_fst_227_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v___x_245_, 1);
if (v_fst_228_ == 0)
{
lean_object* v_fst_247_; lean_object* v_snd_248_; lean_object* v___x_249_; 
v_fst_247_ = lean_ctor_get(v_a_246_, 0);
lean_inc(v_fst_247_);
v_snd_248_ = lean_ctor_get(v_a_246_, 1);
lean_inc(v_snd_248_);
lean_dec(v_a_246_);
v___x_249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__4));
v___y_203_ = v_fst_243_;
v___y_204_ = v___y_230_;
v___y_205_ = v___y_232_;
v___y_206_ = v_fst_247_;
v___y_207_ = v_snd_248_;
v___y_208_ = v_snd_244_;
v___y_209_ = v___y_238_;
v___y_210_ = v___y_236_;
v___y_211_ = v_fst_226_;
v___y_212_ = v_fst_227_;
v___y_213_ = v___y_234_;
v___y_214_ = v___y_237_;
v___y_215_ = v___y_235_;
v___y_216_ = v_fst_228_;
v___y_217_ = v___y_231_;
v___y_218_ = v___y_233_;
v___y_219_ = v___y_239_;
v___y_220_ = v___x_249_;
goto v___jp_202_;
}
else
{
lean_object* v_fst_250_; lean_object* v_snd_251_; lean_object* v___x_252_; 
v_fst_250_ = lean_ctor_get(v_a_246_, 0);
lean_inc(v_fst_250_);
v_snd_251_ = lean_ctor_get(v_a_246_, 1);
lean_inc(v_snd_251_);
lean_dec(v_a_246_);
v___x_252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___closed__6));
v___y_203_ = v_fst_243_;
v___y_204_ = v___y_230_;
v___y_205_ = v___y_232_;
v___y_206_ = v_fst_250_;
v___y_207_ = v_snd_251_;
v___y_208_ = v_snd_244_;
v___y_209_ = v___y_238_;
v___y_210_ = v___y_236_;
v___y_211_ = v_fst_226_;
v___y_212_ = v_fst_227_;
v___y_213_ = v___y_234_;
v___y_214_ = v___y_237_;
v___y_215_ = v___y_235_;
v___y_216_ = v_fst_228_;
v___y_217_ = v___y_231_;
v___y_218_ = v___y_233_;
v___y_219_ = v___y_239_;
v___y_220_ = v___x_252_;
goto v___jp_202_;
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_snd_244_);
lean_dec(v_fst_243_);
lean_dec_ref(v_fst_227_);
lean_dec_ref(v_fst_226_);
lean_dec_ref(v_entries_132_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
v_a_253_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_245_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_245_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec_ref(v_fst_227_);
lean_dec_ref(v_fst_226_);
lean_dec_ref(v_entries_132_);
lean_dec(v_path_130_);
lean_dec(v_gen_129_);
v_a_261_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_241_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_241_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries___boxed(lean_object* v_gen_368_, lean_object* v_path_369_, lean_object* v_c_370_, lean_object* v_entries_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries(v_gen_368_, v_path_369_, v_c_370_, v_entries_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec(v_a_372_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f_spec__0(lean_object* v_lin_384_, lean_object* v_as_385_, size_t v_i_386_, size_t v_stop_387_, lean_object* v_b_388_){
_start:
{
lean_object* v___y_390_; uint8_t v___x_394_; 
v___x_394_ = lean_usize_dec_eq(v_i_386_, v_stop_387_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v_lin_396_; lean_object* v_k_397_; uint8_t v___x_398_; 
v___x_395_ = lean_array_uget_borrowed(v_as_385_, v_i_386_);
v_lin_396_ = lean_ctor_get(v___x_395_, 0);
v_k_397_ = lean_ctor_get(v___x_395_, 1);
v___x_398_ = l_Int_Internal_Linear_instBEqPoly_beq(v_lin_396_, v_lin_384_);
if (v___x_398_ == 0)
{
v___y_390_ = v_b_388_;
goto v___jp_389_;
}
else
{
if (lean_obj_tag(v_b_388_) == 0)
{
lean_object* v___x_399_; 
lean_inc(v___x_395_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_395_);
v___y_390_ = v___x_399_;
goto v___jp_389_;
}
else
{
lean_object* v_val_400_; lean_object* v_k_401_; uint8_t v___x_402_; 
v_val_400_ = lean_ctor_get(v_b_388_, 0);
v_k_401_ = lean_ctor_get(v_val_400_, 1);
v___x_402_ = lean_int_dec_lt(v_k_401_, v_k_397_);
if (v___x_402_ == 0)
{
v___y_390_ = v_b_388_;
goto v___jp_389_;
}
else
{
lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_isSharedCheck_409_ = !lean_is_exclusive(v_b_388_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v_b_388_, 0);
lean_dec(v_unused_410_);
v___x_404_ = v_b_388_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_dec(v_b_388_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
lean_inc(v___x_395_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_395_);
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_395_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
v___y_390_ = v___x_407_;
goto v___jp_389_;
}
}
}
}
}
}
else
{
return v_b_388_;
}
v___jp_389_:
{
size_t v___x_391_; size_t v___x_392_; 
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_386_, v___x_391_);
v_i_386_ = v___x_392_;
v_b_388_ = v___y_390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f_spec__0___boxed(lean_object* v_lin_411_, lean_object* v_as_412_, lean_object* v_i_413_, lean_object* v_stop_414_, lean_object* v_b_415_){
_start:
{
size_t v_i_boxed_416_; size_t v_stop_boxed_417_; lean_object* v_res_418_; 
v_i_boxed_416_ = lean_unbox_usize(v_i_413_);
lean_dec(v_i_413_);
v_stop_boxed_417_ = lean_unbox_usize(v_stop_414_);
lean_dec(v_stop_414_);
v_res_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f_spec__0(v_lin_411_, v_as_412_, v_i_boxed_416_, v_stop_boxed_417_, v_b_415_);
lean_dec_ref(v_as_412_);
lean_dec_ref(v_lin_411_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f(lean_object* v_entries_419_, lean_object* v_lin_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_421_ = lean_box(0);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_array_get_size(v_entries_419_);
v___x_424_ = lean_nat_dec_lt(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
return v___x_421_;
}
else
{
size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v___x_425_ = ((size_t)0ULL);
v___x_426_ = lean_usize_of_nat(v___x_423_);
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f_spec__0(v_lin_420_, v_entries_419_, v___x_425_, v___x_426_, v___x_421_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f___boxed(lean_object* v_entries_428_, lean_object* v_lin_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f(v_entries_428_, v_lin_429_);
lean_dec_ref(v_lin_429_);
lean_dec_ref(v_entries_428_);
return v_res_430_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__8(lean_object* v_as_431_, size_t v_i_432_, size_t v_stop_433_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_eq(v_i_432_, v_stop_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_435_ = lean_array_uget_borrowed(v_as_431_, v_i_432_);
v___x_436_ = lean_array_get_size(v___x_435_);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_nat_dec_eq(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
size_t v___x_439_; size_t v___x_440_; 
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_add(v_i_432_, v___x_439_);
v_i_432_ = v___x_440_;
goto _start;
}
else
{
return v___x_438_;
}
}
else
{
uint8_t v___x_442_; 
v___x_442_ = 0;
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__8___boxed(lean_object* v_as_443_, lean_object* v_i_444_, lean_object* v_stop_445_){
_start:
{
size_t v_i_boxed_446_; size_t v_stop_boxed_447_; uint8_t v_res_448_; lean_object* v_r_449_; 
v_i_boxed_446_ = lean_unbox_usize(v_i_444_);
lean_dec(v_i_444_);
v_stop_boxed_447_ = lean_unbox_usize(v_stop_445_);
lean_dec(v_stop_445_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__8(v_as_443_, v_i_boxed_446_, v_stop_boxed_447_);
lean_dec_ref(v_as_443_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__6(lean_object* v_as_450_, size_t v_i_451_, size_t v_stop_452_, lean_object* v_b_453_){
_start:
{
lean_object* v___y_455_; uint8_t v___x_459_; 
v___x_459_ = lean_usize_dec_eq(v_i_451_, v_stop_452_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v_k_461_; uint8_t v___x_462_; 
v___x_460_ = lean_array_uget_borrowed(v_as_450_, v_i_451_);
v_k_461_ = lean_ctor_get(v___x_460_, 1);
v___x_462_ = lean_int_dec_le(v_b_453_, v_k_461_);
if (v___x_462_ == 0)
{
v___y_455_ = v_k_461_;
goto v___jp_454_;
}
else
{
v___y_455_ = v_b_453_;
goto v___jp_454_;
}
}
else
{
lean_inc(v_b_453_);
return v_b_453_;
}
v___jp_454_:
{
size_t v___x_456_; size_t v___x_457_; 
v___x_456_ = ((size_t)1ULL);
v___x_457_ = lean_usize_add(v_i_451_, v___x_456_);
v_i_451_ = v___x_457_;
v_b_453_ = v___y_455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__6___boxed(lean_object* v_as_463_, lean_object* v_i_464_, lean_object* v_stop_465_, lean_object* v_b_466_){
_start:
{
size_t v_i_boxed_467_; size_t v_stop_boxed_468_; lean_object* v_res_469_; 
v_i_boxed_467_ = lean_unbox_usize(v_i_464_);
lean_dec(v_i_464_);
v_stop_boxed_468_ = lean_unbox_usize(v_stop_465_);
lean_dec(v_stop_465_);
v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__6(v_as_463_, v_i_boxed_467_, v_stop_boxed_468_, v_b_466_);
lean_dec(v_b_466_);
lean_dec_ref(v_as_463_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__4(lean_object* v___x_470_, size_t v_sz_471_, size_t v_i_472_, lean_object* v_bs_473_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = lean_usize_dec_lt(v_i_472_, v_sz_471_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v_bs_473_);
return v___x_475_;
}
else
{
lean_object* v_v_476_; lean_object* v___x_477_; 
v_v_476_ = lean_array_uget_borrowed(v_bs_473_, v_i_472_);
v___x_477_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_findStrongest_x3f(v_v_476_, v___x_470_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; 
lean_dec_ref(v_bs_473_);
v___x_478_ = lean_box(0);
return v___x_478_;
}
else
{
lean_object* v_val_479_; lean_object* v___x_480_; lean_object* v_bs_x27_481_; size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v_val_479_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_val_479_);
lean_dec_ref_known(v___x_477_, 1);
v___x_480_ = lean_unsigned_to_nat(0u);
v_bs_x27_481_ = lean_array_uset(v_bs_473_, v_i_472_, v___x_480_);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_add(v_i_472_, v___x_482_);
v___x_484_ = lean_array_uset(v_bs_x27_481_, v_i_472_, v_val_479_);
v_i_472_ = v___x_483_;
v_bs_473_ = v___x_484_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__4___boxed(lean_object* v___x_486_, lean_object* v_sz_487_, lean_object* v_i_488_, lean_object* v_bs_489_){
_start:
{
size_t v_sz_boxed_490_; size_t v_i_boxed_491_; lean_object* v_res_492_; 
v_sz_boxed_490_ = lean_unbox_usize(v_sz_487_);
lean_dec(v_sz_487_);
v_i_boxed_491_ = lean_unbox_usize(v_i_488_);
lean_dec(v_i_488_);
v_res_492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__4(v___x_486_, v_sz_boxed_490_, v_i_boxed_491_, v_bs_489_);
lean_dec_ref(v___x_486_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__5(lean_object* v___y_493_, size_t v_sz_494_, size_t v_i_495_, lean_object* v_bs_496_){
_start:
{
uint8_t v___x_497_; 
v___x_497_ = lean_usize_dec_lt(v_i_495_, v_sz_494_);
if (v___x_497_ == 0)
{
return v_bs_496_;
}
else
{
lean_object* v_v_498_; lean_object* v_alt_499_; lean_object* v_k_500_; lean_object* v_path_501_; lean_object* v_toIntThm_x3f_502_; lean_object* v_lhs_503_; lean_object* v_rhs_504_; uint8_t v_kind_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_519_; 
v_v_498_ = lean_array_uget_borrowed(v_bs_496_, v_i_495_);
v_alt_499_ = lean_ctor_get(v_v_498_, 2);
lean_inc_ref(v_alt_499_);
v_k_500_ = lean_ctor_get(v_v_498_, 1);
lean_inc(v_k_500_);
v_path_501_ = lean_ctor_get(v_alt_499_, 0);
v_toIntThm_x3f_502_ = lean_ctor_get(v_alt_499_, 1);
v_lhs_503_ = lean_ctor_get(v_alt_499_, 2);
v_rhs_504_ = lean_ctor_get(v_alt_499_, 3);
v_kind_505_ = lean_ctor_get_uint8(v_alt_499_, sizeof(void*)*5);
v_isSharedCheck_519_ = !lean_is_exclusive(v_alt_499_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v_alt_499_, 4);
lean_dec(v_unused_520_);
v___x_507_ = v_alt_499_;
v_isShared_508_ = v_isSharedCheck_519_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_rhs_504_);
lean_inc(v_lhs_503_);
lean_inc(v_toIntThm_x3f_502_);
lean_inc(v_path_501_);
lean_dec(v_alt_499_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_519_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v_bs_x27_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v_bs_x27_510_ = lean_array_uset(v_bs_496_, v_i_495_, v___x_509_);
v___x_511_ = lean_int_sub(v_k_500_, v___y_493_);
lean_dec(v_k_500_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 4, v___x_511_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_path_501_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_toIntThm_x3f_502_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_lhs_503_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_rhs_504_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v___x_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_518_, sizeof(void*)*5, v_kind_505_);
v___x_513_ = v_reuseFailAlloc_518_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_514_ = ((size_t)1ULL);
v___x_515_ = lean_usize_add(v_i_495_, v___x_514_);
v___x_516_ = lean_array_uset(v_bs_x27_510_, v_i_495_, v___x_513_);
v_i_495_ = v___x_515_;
v_bs_496_ = v___x_516_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__5___boxed(lean_object* v___y_521_, lean_object* v_sz_522_, lean_object* v_i_523_, lean_object* v_bs_524_){
_start:
{
size_t v_sz_boxed_525_; size_t v_i_boxed_526_; lean_object* v_res_527_; 
v_sz_boxed_525_ = lean_unbox_usize(v_sz_522_);
lean_dec(v_sz_522_);
v_i_boxed_526_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__5(v___y_521_, v_sz_boxed_525_, v_i_boxed_526_, v_bs_524_);
lean_dec(v___y_521_);
return v_res_527_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3_spec__3(lean_object* v_a_528_, lean_object* v_as_529_, size_t v_i_530_, size_t v_stop_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = lean_usize_dec_eq(v_i_530_, v_stop_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_array_uget_borrowed(v_as_529_, v_i_530_);
v___x_534_ = l_Int_Internal_Linear_instBEqPoly_beq(v_a_528_, v___x_533_);
if (v___x_534_ == 0)
{
size_t v___x_535_; size_t v___x_536_; 
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_add(v_i_530_, v___x_535_);
v_i_530_ = v___x_536_;
goto _start;
}
else
{
return v___x_534_;
}
}
else
{
uint8_t v___x_538_; 
v___x_538_ = 0;
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3_spec__3___boxed(lean_object* v_a_539_, lean_object* v_as_540_, lean_object* v_i_541_, lean_object* v_stop_542_){
_start:
{
size_t v_i_boxed_543_; size_t v_stop_boxed_544_; uint8_t v_res_545_; lean_object* v_r_546_; 
v_i_boxed_543_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_stop_boxed_544_ = lean_unbox_usize(v_stop_542_);
lean_dec(v_stop_542_);
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3_spec__3(v_a_539_, v_as_540_, v_i_boxed_543_, v_stop_boxed_544_);
lean_dec_ref(v_as_540_);
lean_dec_ref(v_a_539_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3(lean_object* v_as_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_array_get_size(v_as_547_);
v___x_551_ = lean_nat_dec_lt(v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
return v___x_551_;
}
else
{
size_t v___x_552_; size_t v___x_553_; uint8_t v___x_554_; 
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_550_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3_spec__3(v_a_548_, v_as_547_, v___x_552_, v___x_553_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3___boxed(lean_object* v_as_555_, lean_object* v_a_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3(v_as_555_, v_a_556_);
lean_dec_ref(v_a_556_);
lean_dec_ref(v_as_555_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__7(lean_object* v___x_561_, lean_object* v_e_562_, lean_object* v_as_563_, size_t v_sz_564_, size_t v_i_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_a_579_; uint8_t v___x_583_; 
v___x_583_ = lean_usize_dec_lt(v_i_565_, v_sz_564_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
lean_dec_ref(v_e_562_);
lean_dec_ref(v___x_561_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v_b_566_);
return v___x_584_;
}
else
{
lean_object* v_snd_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_664_; 
v_snd_585_ = lean_ctor_get(v_b_566_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_b_566_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v_b_566_, 0);
lean_dec(v_unused_665_);
v___x_587_ = v_b_566_;
v_isShared_588_ = v_isSharedCheck_664_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_snd_585_);
lean_dec(v_b_566_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_664_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_a_589_; lean_object* v_lin_590_; lean_object* v_k_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_662_; 
v_a_589_ = lean_array_uget(v_as_563_, v_i_565_);
v_lin_590_ = lean_ctor_get(v_a_589_, 0);
v_k_591_ = lean_ctor_get(v_a_589_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_a_589_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v_a_589_, 2);
lean_dec(v_unused_663_);
v___x_593_ = v_a_589_;
v_isShared_594_ = v_isSharedCheck_662_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_k_591_);
lean_inc(v_lin_590_);
lean_dec(v_a_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_662_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_box(0);
v___x_596_ = l_Array_contains___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__3(v_snd_585_, v_lin_590_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; size_t v_sz_598_; size_t v___x_599_; lean_object* v___x_600_; 
lean_inc_ref(v_lin_590_);
v___x_597_ = lean_array_push(v_snd_585_, v_lin_590_);
v_sz_598_ = lean_array_size(v___x_561_);
v___x_599_ = ((size_t)0ULL);
lean_inc_ref(v___x_561_);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__4(v_lin_590_, v_sz_598_, v___x_599_, v___x_561_);
if (lean_obj_tag(v___x_600_) == 1)
{
lean_object* v_val_601_; lean_object* v___y_603_; lean_object* v___x_645_; lean_object* v___y_647_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_val_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_val_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_array_get_size(v_val_601_);
v___x_653_ = lean_nat_dec_lt(v___x_645_, v___x_652_);
if (v___x_653_ == 0)
{
v___y_647_ = v_k_591_;
goto v___jp_646_;
}
else
{
lean_object* v___x_654_; lean_object* v_k_655_; 
lean_dec(v_k_591_);
v___x_654_ = lean_array_fget_borrowed(v_val_601_, v___x_645_);
v_k_655_ = lean_ctor_get(v___x_654_, 1);
lean_inc(v_k_655_);
v___y_647_ = v_k_655_;
goto v___jp_646_;
}
v___jp_602_:
{
size_t v_sz_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v_sz_604_ = lean_array_size(v_val_601_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__5(v___y_603_, v_sz_604_, v___x_599_, v_val_601_);
v___x_606_ = l_Int_Internal_Linear_Poly_addConst(v_lin_590_, v___y_603_);
lean_dec(v___y_603_);
lean_inc_ref(v_e_562_);
v___x_607_ = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(v___x_607_, 0, v_e_562_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 2, v___x_595_);
lean_ctor_set(v___x_593_, 1, v___x_607_);
lean_ctor_set(v___x_593_, 0, v___x_606_);
v___x_609_ = v___x_593_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v___x_595_);
v___x_609_ = v_reuseFailAlloc_644_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_610_; 
lean_inc(v___y_576_);
lean_inc_ref(v___y_575_);
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
lean_inc(v___y_568_);
lean_inc(v___y_567_);
v___x_610_ = lean_grind_cutsat_assert_le(v___x_609_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v___x_611_; 
lean_dec_ref_known(v___x_610_, 1);
v___x_611_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v___y_567_, v___y_575_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_627_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_627_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_627_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_627_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
uint8_t v___x_616_; 
v___x_616_ = lean_unbox(v_a_612_);
lean_dec(v_a_612_);
if (v___x_616_ == 0)
{
lean_object* v___x_618_; 
lean_del_object(v___x_614_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_597_);
lean_ctor_set(v___x_587_, 0, v___x_595_);
v___x_618_ = v___x_587_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_597_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
v_a_579_ = v___x_618_;
goto v___jp_578_;
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_622_; 
lean_dec_ref(v_e_562_);
lean_dec_ref(v___x_561_);
v___x_620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__7___closed__0));
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_597_);
lean_ctor_set(v___x_587_, 0, v___x_620_);
v___x_622_ = v___x_587_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_597_);
v___x_622_ = v_reuseFailAlloc_626_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_622_);
v___x_624_ = v___x_614_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v___x_597_);
lean_del_object(v___x_587_);
lean_dec_ref(v_e_562_);
lean_dec_ref(v___x_561_);
v_a_628_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_611_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_611_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v___x_597_);
lean_del_object(v___x_587_);
lean_dec_ref(v_e_562_);
lean_dec_ref(v___x_561_);
v_a_636_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_610_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_610_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
v___jp_646_:
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = lean_array_get_size(v_val_601_);
v___x_649_ = lean_nat_dec_lt(v___x_645_, v___x_648_);
if (v___x_649_ == 0)
{
v___y_603_ = v___y_647_;
goto v___jp_602_;
}
else
{
size_t v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_usize_of_nat(v___x_648_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__6(v_val_601_, v___x_599_, v___x_650_, v___y_647_);
lean_dec(v___y_647_);
v___y_603_ = v___x_651_;
goto v___jp_602_;
}
}
}
else
{
lean_object* v___x_657_; 
lean_dec(v___x_600_);
lean_del_object(v___x_593_);
lean_dec(v_k_591_);
lean_dec_ref(v_lin_590_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_597_);
lean_ctor_set(v___x_587_, 0, v___x_595_);
v___x_657_ = v___x_587_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_597_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
v_a_579_ = v___x_657_;
goto v___jp_578_;
}
}
}
else
{
lean_object* v___x_660_; 
lean_del_object(v___x_593_);
lean_dec(v_k_591_);
lean_dec_ref(v_lin_590_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_595_);
v___x_660_ = v___x_587_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_snd_585_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
v_a_579_ = v___x_660_;
goto v___jp_578_;
}
}
}
}
}
v___jp_578_:
{
size_t v___x_580_; size_t v___x_581_; 
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_add(v_i_565_, v___x_580_);
v_i_565_ = v___x_581_;
v_b_566_ = v_a_579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__7___boxed(lean_object** _args){
lean_object* v___x_666_ = _args[0];
lean_object* v_e_667_ = _args[1];
lean_object* v_as_668_ = _args[2];
lean_object* v_sz_669_ = _args[3];
lean_object* v_i_670_ = _args[4];
lean_object* v_b_671_ = _args[5];
lean_object* v___y_672_ = _args[6];
lean_object* v___y_673_ = _args[7];
lean_object* v___y_674_ = _args[8];
lean_object* v___y_675_ = _args[9];
lean_object* v___y_676_ = _args[10];
lean_object* v___y_677_ = _args[11];
lean_object* v___y_678_ = _args[12];
lean_object* v___y_679_ = _args[13];
lean_object* v___y_680_ = _args[14];
lean_object* v___y_681_ = _args[15];
lean_object* v___y_682_ = _args[16];
_start:
{
size_t v_sz_boxed_683_; size_t v_i_boxed_684_; lean_object* v_res_685_; 
v_sz_boxed_683_ = lean_unbox_usize(v_sz_669_);
lean_dec(v_sz_669_);
v_i_boxed_684_ = lean_unbox_usize(v_i_670_);
lean_dec(v_i_670_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__7(v___x_666_, v_e_667_, v_as_668_, v_sz_boxed_683_, v_i_boxed_684_, v_b_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v_as_668_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0(size_t v_sz_688_, size_t v_i_689_, lean_object* v_bs_690_){
_start:
{
uint8_t v___x_691_; 
v___x_691_ = lean_usize_dec_lt(v_i_689_, v_sz_688_);
if (v___x_691_ == 0)
{
return v_bs_690_;
}
else
{
lean_object* v_v_692_; lean_object* v___x_693_; lean_object* v_bs_x27_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v_v_692_ = lean_array_uget(v_bs_690_, v_i_689_);
v___x_693_ = lean_unsigned_to_nat(0u);
v_bs_x27_694_ = lean_array_uset(v_bs_690_, v_i_689_, v___x_693_);
v___x_695_ = lean_box(0);
v___x_696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___closed__0));
v___x_697_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getArithConjuncts(v_v_692_, v___x_695_, v___x_696_);
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_add(v_i_689_, v___x_698_);
v___x_700_ = lean_array_uset(v_bs_x27_694_, v_i_689_, v___x_697_);
v_i_689_ = v___x_699_;
v_bs_690_ = v___x_700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___boxed(lean_object* v_sz_702_, lean_object* v_i_703_, lean_object* v_bs_704_){
_start:
{
size_t v_sz_boxed_705_; size_t v_i_boxed_706_; lean_object* v_res_707_; 
v_sz_boxed_705_ = lean_unbox_usize(v_sz_702_);
lean_dec(v_sz_702_);
v_i_boxed_706_ = lean_unbox_usize(v_i_703_);
lean_dec(v_i_703_);
v_res_707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0(v_sz_boxed_705_, v_i_boxed_706_, v_bs_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1(lean_object* v_a_708_, lean_object* v_as_709_, size_t v_sz_710_, size_t v_i_711_, lean_object* v_b_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = lean_usize_dec_lt(v_i_711_, v_sz_710_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_dec(v_a_708_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_b_712_);
return v___x_725_;
}
else
{
lean_object* v_a_726_; lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v___x_729_; 
v_a_726_ = lean_array_uget_borrowed(v_as_709_, v_i_711_);
v_fst_727_ = lean_ctor_get(v_a_726_, 0);
v_snd_728_ = lean_ctor_get(v_a_726_, 1);
lean_inc(v_snd_728_);
lean_inc(v_fst_727_);
lean_inc(v_a_708_);
v___x_729_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_pushEntries(v_a_708_, v_fst_727_, v_snd_728_, v_b_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; size_t v___x_731_; size_t v___x_732_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = ((size_t)1ULL);
v___x_732_ = lean_usize_add(v_i_711_, v___x_731_);
v_i_711_ = v___x_732_;
v_b_712_ = v_a_730_;
goto _start;
}
else
{
lean_dec(v_a_708_);
return v___x_729_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___boxed(lean_object* v_a_734_, lean_object* v_as_735_, lean_object* v_sz_736_, lean_object* v_i_737_, lean_object* v_b_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
size_t v_sz_boxed_750_; size_t v_i_boxed_751_; lean_object* v_res_752_; 
v_sz_boxed_750_ = lean_unbox_usize(v_sz_736_);
lean_dec(v_sz_736_);
v_i_boxed_751_ = lean_unbox_usize(v_i_737_);
lean_dec(v_i_737_);
v_res_752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1(v_a_734_, v_as_735_, v_sz_boxed_750_, v_i_boxed_751_, v_b_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v_as_735_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__2(lean_object* v_a_755_, lean_object* v_as_756_, size_t v_sz_757_, size_t v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = lean_usize_dec_lt(v_i_758_, v_sz_757_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_dec(v_a_755_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v_b_759_);
return v___x_772_;
}
else
{
lean_object* v_snd_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_813_; 
v_snd_773_ = lean_ctor_get(v_b_759_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_b_759_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v_b_759_, 0);
lean_dec(v_unused_814_);
v___x_775_ = v_b_759_;
v_isShared_776_ = v_isSharedCheck_813_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_snd_773_);
lean_dec(v_b_759_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_813_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v_a_778_; lean_object* v___x_779_; lean_object* v___x_780_; size_t v_sz_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_777_ = lean_box(0);
v_a_778_ = lean_array_uget_borrowed(v_as_756_, v_i_758_);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__2___closed__0));
v_sz_781_ = lean_array_size(v_a_778_);
v___x_782_ = ((size_t)0ULL);
lean_inc(v_a_755_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1(v_a_755_, v_a_778_, v_sz_781_, v___x_782_, v___x_780_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_804_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_804_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_804_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_804_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = lean_array_get_size(v_a_784_);
v___x_789_ = lean_nat_dec_eq(v___x_788_, v___x_779_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_del_object(v___x_786_);
v___x_790_ = lean_array_push(v_snd_773_, v_a_784_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___x_790_);
lean_ctor_set(v___x_775_, 0, v___x_777_);
v___x_792_ = v___x_775_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_790_);
v___x_792_ = v_reuseFailAlloc_796_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
size_t v___x_793_; size_t v___x_794_; 
v___x_793_ = ((size_t)1ULL);
v___x_794_ = lean_usize_add(v_i_758_, v___x_793_);
v_i_758_ = v___x_794_;
v_b_759_ = v___x_792_;
goto _start;
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_dec(v_a_784_);
lean_dec(v_a_755_);
v___x_797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__7___closed__0));
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_797_);
v___x_799_ = v___x_775_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_snd_773_);
v___x_799_ = v_reuseFailAlloc_803_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_799_);
v___x_801_ = v___x_786_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_del_object(v___x_775_);
lean_dec(v_snd_773_);
lean_dec(v_a_755_);
v_a_805_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_783_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_783_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__2___boxed(lean_object* v_a_815_, lean_object* v_as_816_, lean_object* v_sz_817_, lean_object* v_i_818_, lean_object* v_b_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
size_t v_sz_boxed_831_; size_t v_i_boxed_832_; lean_object* v_res_833_; 
v_sz_boxed_831_ = lean_unbox_usize(v_sz_817_);
lean_dec(v_sz_817_);
v_i_boxed_832_ = lean_unbox_usize(v_i_818_);
lean_dec(v_i_818_);
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__2(v_a_815_, v_as_816_, v_sz_boxed_831_, v_i_boxed_832_, v_b_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v_as_816_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull(lean_object* v_e_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_842_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_958_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_958_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_958_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_958_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint8_t v_lia_856_; 
v_lia_856_ = lean_ctor_get_uint8(v_a_852_, sizeof(void*)*18 + 24);
lean_dec(v_a_852_);
if (v_lia_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_859_; 
lean_dec_ref(v_e_839_);
v___x_857_ = lean_box(0);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_object* v___x_861_; 
lean_del_object(v___x_854_);
v___x_861_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_840_, v_a_848_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_949_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_949_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_949_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_949_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
uint8_t v___x_866_; 
v___x_866_ = lean_unbox(v_a_862_);
lean_dec(v_a_862_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; size_t v_sz_870_; size_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__0));
lean_inc_ref(v_e_839_);
v___x_869_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getDisjuncts(v_e_839_, v___x_868_);
v_sz_870_ = lean_array_size(v___x_869_);
v___x_871_ = ((size_t)0ULL);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0(v_sz_870_, v___x_871_, v___x_869_);
v___x_937_ = lean_array_get_size(v___x_872_);
v___x_938_ = lean_nat_dec_lt(v___x_867_, v___x_937_);
if (v___x_938_ == 0)
{
lean_del_object(v___x_864_);
goto v___jp_873_;
}
else
{
if (v___x_938_ == 0)
{
lean_del_object(v___x_864_);
goto v___jp_873_;
}
else
{
size_t v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_usize_of_nat(v___x_937_);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__8(v___x_872_, v___x_871_, v___x_939_);
if (v___x_940_ == 0)
{
lean_del_object(v___x_864_);
goto v___jp_873_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_943_; 
lean_dec_ref(v___x_872_);
lean_dec_ref(v_e_839_);
v___x_941_ = lean_box(0);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_941_);
v___x_943_ = v___x_864_;
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
}
}
v___jp_873_:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_839_, v_a_840_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; size_t v_sz_877_; lean_object* v___x_878_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v___x_876_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__1));
v_sz_877_ = lean_array_size(v___x_872_);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__2(v_a_875_, v___x_872_, v_sz_877_, v___x_871_, v___x_876_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec_ref(v___x_872_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_920_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_920_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_920_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_920_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_fst_883_; 
v_fst_883_ = lean_ctor_get(v_a_879_, 0);
if (lean_obj_tag(v_fst_883_) == 0)
{
lean_object* v_snd_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v_snd_884_ = lean_ctor_get(v_a_879_, 1);
lean_inc(v_snd_884_);
lean_dec(v_a_879_);
v___x_885_ = lean_array_get_size(v_snd_884_);
v___x_886_ = lean_nat_dec_lt(v___x_867_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_889_; 
lean_dec(v_snd_884_);
lean_dec_ref(v_e_839_);
v___x_887_ = lean_box(0);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_887_);
v___x_889_ = v___x_881_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
else
{
lean_object* v___x_891_; size_t v_sz_892_; lean_object* v___x_893_; 
lean_del_object(v___x_881_);
v___x_891_ = lean_array_fget(v_snd_884_, v___x_867_);
v_sz_892_ = lean_array_size(v___x_891_);
v___x_893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__7(v_snd_884_, v_e_839_, v___x_891_, v_sz_892_, v___x_871_, v___x_876_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec(v___x_891_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_907_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_907_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_907_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_907_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_fst_898_; 
v_fst_898_ = lean_ctor_get(v_a_894_, 0);
lean_inc(v_fst_898_);
lean_dec(v_a_894_);
if (lean_obj_tag(v_fst_898_) == 0)
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_box(0);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_899_);
v___x_901_ = v___x_896_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
else
{
lean_object* v_val_903_; lean_object* v___x_905_; 
v_val_903_ = lean_ctor_get(v_fst_898_, 0);
lean_inc(v_val_903_);
lean_dec_ref_known(v_fst_898_, 1);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v_val_903_);
v___x_905_ = v___x_896_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_val_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_a_908_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_893_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_893_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
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
}
else
{
lean_object* v_val_916_; lean_object* v___x_918_; 
lean_inc_ref(v_fst_883_);
lean_dec(v_a_879_);
lean_dec_ref(v_e_839_);
v_val_916_ = lean_ctor_get(v_fst_883_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v_fst_883_, 1);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v_val_916_);
v___x_918_ = v___x_881_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_val_916_);
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
lean_dec_ref(v_e_839_);
v_a_921_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_878_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_878_);
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
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v___x_872_);
lean_dec_ref(v_e_839_);
v_a_929_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_874_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_874_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
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
}
else
{
lean_object* v___x_945_; lean_object* v___x_947_; 
lean_dec_ref(v_e_839_);
v___x_945_ = lean_box(0);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_945_);
v___x_947_ = v___x_864_;
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
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v_e_839_);
v_a_950_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_861_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_861_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
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
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref(v_e_839_);
v_a_959_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_851_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_851_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___boxed(lean_object* v_e_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull(v_e_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec(v_a_968_);
return v_res_979_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(builtin);
}
#ifdef __cplusplus
}
#endif
