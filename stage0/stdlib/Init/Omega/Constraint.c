// Lean compiler output
// Module: Init.Omega.Constraint
// Imports: public import Init.Omega.Coeffs import Init.Data.Int.Lemmas import Init.Data.Int.Order import Init.Data.ToString.Macro import Init.Omega.Int import Init.PropLemmas import Init.RCases
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_leading(lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Omega_IntList_smul(lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_gcd(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_sdiv(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_dot(lean_object*, lean_object*);
lean_object* l_String_Internal_append___boxed(lean_object*, lean_object*);
lean_object* l_Option_merge___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_bmod(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Omega_IntList_set(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Omega_LowerBound_sat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LowerBound_sat___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Omega_UpperBound_sat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_UpperBound_sat___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Omega_instBEqConstraint_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_instBEqConstraint_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_instBEqConstraint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_instBEqConstraint_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_instBEqConstraint___closed__0 = (const lean_object*)&l_Lean_Omega_instBEqConstraint___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_instBEqConstraint = (const lean_object*)&l_Lean_Omega_instBEqConstraint___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqConstraint_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqConstraint_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqConstraint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqConstraint___boxed(lean_object*, lean_object*);
static const lean_string_object l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__3_value;
static lean_once_cell_t l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Omega_instReprConstraint_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lowerBound"};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Omega_instReprConstraint_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__7;
static const lean_string_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "upperBound"};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__11_value;
static const lean_string_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Omega_instReprConstraint_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__13;
static lean_once_cell_t l_Lean_Omega_instReprConstraint_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__14;
static const lean_ctor_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Omega_instReprConstraint_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Omega_instReprConstraint_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Omega_instReprConstraint_repr___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_instReprConstraint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_instReprConstraint_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_instReprConstraint___closed__0 = (const lean_object*)&l_Lean_Omega_instReprConstraint___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_instReprConstraint = (const lean_object*)&l_Lean_Omega_instReprConstraint___closed__0_value;
static const lean_closure_object l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instAppendString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Internal_append___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instAppendString___closed__0 = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instAppendString___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instAppendString = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instAppendString___closed__0_value;
static const lean_string_object l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___closed__0 = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___closed__0 = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___closed__0_value;
static const lean_string_object l_Lean_Omega_Constraint_instToString___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Omega_Constraint_instToString___private__1___closed__0 = (const lean_object*)&l_Lean_Omega_Constraint_instToString___private__1___closed__0_value;
static const lean_string_object l_Lean_Omega_Constraint_instToString___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "(-∞, ∞)"};
static const lean_object* l_Lean_Omega_Constraint_instToString___private__1___closed__1 = (const lean_object*)&l_Lean_Omega_Constraint_instToString___private__1___closed__1_value;
static const lean_string_object l_Lean_Omega_Constraint_instToString___private__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "(-∞, "};
static const lean_object* l_Lean_Omega_Constraint_instToString___private__1___closed__2 = (const lean_object*)&l_Lean_Omega_Constraint_instToString___private__1___closed__2_value;
static const lean_string_object l_Lean_Omega_Constraint_instToString___private__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Omega_Constraint_instToString___private__1___closed__3 = (const lean_object*)&l_Lean_Omega_Constraint_instToString___private__1___closed__3_value;
static const lean_string_object l_Lean_Omega_Constraint_instToString___private__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = ", ∞)"};
static const lean_object* l_Lean_Omega_Constraint_instToString___private__1___closed__4 = (const lean_object*)&l_Lean_Omega_Constraint_instToString___private__1___closed__4_value;
static const lean_string_object l_Lean_Omega_Constraint_instToString___private__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Omega_Constraint_instToString___private__1___closed__5 = (const lean_object*)&l_Lean_Omega_Constraint_instToString___private__1___closed__5_value;
static const lean_string_object l_Lean_Omega_Constraint_instToString___private__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Omega_Constraint_instToString___private__1___closed__6 = (const lean_object*)&l_Lean_Omega_Constraint_instToString___private__1___closed__6_value;
static const lean_string_object l_Lean_Omega_Constraint_instToString___private__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Omega_Constraint_instToString___private__1___closed__7 = (const lean_object*)&l_Lean_Omega_Constraint_instToString___private__1___closed__7_value;
static const lean_string_object l_Lean_Omega_Constraint_instToString___private__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∅"};
static const lean_object* l_Lean_Omega_Constraint_instToString___private__1___closed__8 = (const lean_object*)&l_Lean_Omega_Constraint_instToString___private__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_instToString___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_instToString___private__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Omega_Constraint_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_Constraint_instToString___private__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_Constraint_instToString___closed__0 = (const lean_object*)&l_Lean_Omega_Constraint_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_Constraint_instToString = (const lean_object*)&l_Lean_Omega_Constraint_instToString___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_sat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_sat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_map(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_flip(lean_object*);
static const lean_closure_object l_Lean_Omega_Constraint_neg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_Constraint_neg___closed__0 = (const lean_object*)&l_Lean_Omega_Constraint_neg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_neg(lean_object*);
static const lean_ctor_object l_Lean_Omega_Constraint_trivial___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Omega_Constraint_trivial___closed__0 = (const lean_object*)&l_Lean_Omega_Constraint_trivial___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_Constraint_trivial = (const lean_object*)&l_Lean_Omega_Constraint_trivial___closed__0_value;
static lean_once_cell_t l_Lean_Omega_Constraint_impossible___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_Constraint_impossible___closed__0;
static lean_once_cell_t l_Lean_Omega_Constraint_impossible___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_Constraint_impossible___closed__1;
static lean_once_cell_t l_Lean_Omega_Constraint_impossible___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_Constraint_impossible___closed__2;
static lean_once_cell_t l_Lean_Omega_Constraint_impossible___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_Constraint_impossible___closed__3;
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_impossible;
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_exact(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_isImpossible(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_isImpossible___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_isExact(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_isExact___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Omega_Constraint_scale___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_Constraint_scale___closed__0;
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_Constraint_combine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_Constraint_combine___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_Constraint_combine___closed__0 = (const lean_object*)&l_Lean_Omega_Constraint_combine___closed__0_value;
static const lean_closure_object l_Lean_Omega_Constraint_combine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_Constraint_combine___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_Constraint_combine___closed__1 = (const lean_object*)&l_Lean_Omega_Constraint_combine___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Option_merge_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Option_merge_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_div(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_sat_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_sat_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_normalize_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_normalize(lean_object*);
static lean_once_cell_t l_Lean_Omega_positivize_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_positivize_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Omega_positivize_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_tidy_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_tidy(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_tidyConstraint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_tidyCoeffs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_bmod__coeffs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__coeffs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__coeffs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Omega_LowerBound_sat(lean_object* v_b_1_, lean_object* v_t_2_){
_start:
{
if (lean_obj_tag(v_b_1_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
lean_object* v_val_4_; uint8_t v___x_5_; 
v_val_4_ = lean_ctor_get(v_b_1_, 0);
v___x_5_ = lean_int_dec_le(v_val_4_, v_t_2_);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LowerBound_sat___boxed(lean_object* v_b_6_, lean_object* v_t_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lean_Omega_LowerBound_sat(v_b_6_, v_t_7_);
lean_dec(v_t_7_);
lean_dec(v_b_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_UpperBound_sat(lean_object* v_b_10_, lean_object* v_t_11_){
_start:
{
if (lean_obj_tag(v_b_10_) == 0)
{
uint8_t v___x_12_; 
v___x_12_ = 1;
return v___x_12_;
}
else
{
lean_object* v_val_13_; uint8_t v___x_14_; 
v_val_13_ = lean_ctor_get(v_b_10_, 0);
v___x_14_ = lean_int_dec_le(v_t_11_, v_val_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_UpperBound_sat___boxed(lean_object* v_b_15_, lean_object* v_t_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lean_Omega_UpperBound_sat(v_b_15_, v_t_16_);
lean_dec(v_t_16_);
lean_dec(v_b_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_19_) == 0)
{
if (lean_obj_tag(v_x_20_) == 0)
{
uint8_t v___x_21_; 
v___x_21_ = 1;
return v___x_21_;
}
else
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
}
else
{
if (lean_obj_tag(v_x_20_) == 0)
{
uint8_t v___x_23_; 
v___x_23_ = 0;
return v___x_23_;
}
else
{
lean_object* v_val_24_; lean_object* v_val_25_; uint8_t v___x_26_; 
v_val_24_ = lean_ctor_get(v_x_19_, 0);
v_val_25_ = lean_ctor_get(v_x_20_, 0);
v___x_26_ = lean_int_dec_eq(v_val_24_, v_val_25_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0___boxed(lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_x_27_, v_x_28_);
lean_dec(v_x_28_);
lean_dec(v_x_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_instBEqConstraint_beq(lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_lowerBound_33_; lean_object* v_upperBound_34_; lean_object* v_lowerBound_35_; lean_object* v_upperBound_36_; uint8_t v___x_37_; 
v_lowerBound_33_ = lean_ctor_get(v_x_31_, 0);
v_upperBound_34_ = lean_ctor_get(v_x_31_, 1);
v_lowerBound_35_ = lean_ctor_get(v_x_32_, 0);
v_upperBound_36_ = lean_ctor_get(v_x_32_, 1);
v___x_37_ = l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_lowerBound_33_, v_lowerBound_35_);
if (v___x_37_ == 0)
{
return v___x_37_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_upperBound_34_, v_upperBound_36_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instBEqConstraint_beq___boxed(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Lean_Omega_instBEqConstraint_beq(v_x_39_, v_x_40_);
lean_dec_ref(v_x_40_);
lean_dec_ref(v_x_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqConstraint_decEq(lean_object* v_x_45_, lean_object* v_x_46_){
_start:
{
lean_object* v_lowerBound_47_; lean_object* v_upperBound_48_; lean_object* v_lowerBound_49_; lean_object* v_upperBound_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v_lowerBound_47_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_lowerBound_47_);
v_upperBound_48_ = lean_ctor_get(v_x_45_, 1);
lean_inc(v_upperBound_48_);
lean_dec_ref(v_x_45_);
v_lowerBound_49_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_lowerBound_49_);
v_upperBound_50_ = lean_ctor_get(v_x_46_, 1);
lean_inc(v_upperBound_50_);
lean_dec_ref(v_x_46_);
v___x_51_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc_ref(v___x_51_);
v___x_52_ = l_Option_instDecidableEq___redArg(v___x_51_, v_lowerBound_47_, v_lowerBound_49_);
if (v___x_52_ == 0)
{
lean_dec_ref(v___x_51_);
lean_dec(v_upperBound_50_);
lean_dec(v_upperBound_48_);
return v___x_52_;
}
else
{
uint8_t v___x_53_; 
v___x_53_ = l_Option_instDecidableEq___redArg(v___x_51_, v_upperBound_48_, v_upperBound_50_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqConstraint_decEq___boxed(lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_x_54_, v_x_55_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqConstraint(lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_x_58_, v_x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqConstraint___boxed(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Lean_Omega_instDecidableEqConstraint(v_x_61_, v_x_62_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
static lean_object* _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_nat_to_int(v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v___x_75_; 
v___x_75_ = ((lean_object*)(l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__1));
return v___x_75_;
}
else
{
lean_object* v_val_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_97_; 
v_val_76_ = lean_ctor_get(v_x_73_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_97_ == 0)
{
v___x_78_ = v_x_73_;
v_isShared_79_ = v_isSharedCheck_97_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_val_76_);
lean_dec(v_x_73_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_97_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___y_82_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_80_ = ((lean_object*)(l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__3));
v___x_85_ = lean_obj_once(&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4, &l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once, _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4);
v___x_86_ = lean_int_dec_lt(v_val_76_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = l_Int_repr(v_val_76_);
lean_dec(v_val_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 3);
lean_ctor_set(v___x_78_, 0, v___x_87_);
v___x_89_ = v___x_78_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
v___y_82_ = v___x_89_;
goto v___jp_81_;
}
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_91_ = lean_unsigned_to_nat(1024u);
v___x_92_ = l_Int_repr(v_val_76_);
lean_dec(v_val_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 3);
lean_ctor_set(v___x_78_, 0, v___x_92_);
v___x_94_ = v___x_78_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_96_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; 
v___x_95_ = l_Repr_addAppParen(v___x_94_, v___x_91_);
v___y_82_ = v___x_95_;
goto v___jp_81_;
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_80_);
lean_ctor_set(v___x_83_, 1, v___y_82_);
v___x_84_ = l_Repr_addAppParen(v___x_83_, v_x_74_);
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___boxed(lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(v_x_98_, v_x_99_);
lean_dec(v_x_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Omega_instReprConstraint_repr_spec__1(lean_object* v_a_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_nat_to_int(v_a_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(14u);
v___x_117_ = lean_nat_to_int(v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__0));
v___x_126_ = lean_string_length(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_obj_once(&l_Lean_Omega_instReprConstraint_repr___redArg___closed__13, &l_Lean_Omega_instReprConstraint_repr___redArg___closed__13_once, _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__13);
v___x_128_ = lean_nat_to_int(v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr___redArg(lean_object* v_x_133_){
_start:
{
lean_object* v_lowerBound_134_; lean_object* v_upperBound_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_168_; 
v_lowerBound_134_ = lean_ctor_get(v_x_133_, 0);
v_upperBound_135_ = lean_ctor_get(v_x_133_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_168_ == 0)
{
v___x_137_ = v_x_133_;
v_isShared_138_ = v_isSharedCheck_168_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_upperBound_135_);
lean_inc(v_lowerBound_134_);
lean_dec(v_x_133_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_168_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_139_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__5));
v___x_140_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__6));
v___x_141_ = lean_obj_once(&l_Lean_Omega_instReprConstraint_repr___redArg___closed__7, &l_Lean_Omega_instReprConstraint_repr___redArg___closed__7_once, _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__7);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(v_lowerBound_134_, v___x_142_);
if (v_isShared_138_ == 0)
{
lean_ctor_set_tag(v___x_137_, 4);
lean_ctor_set(v___x_137_, 1, v___x_143_);
lean_ctor_set(v___x_137_, 0, v___x_141_);
v___x_145_ = v___x_137_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_167_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
uint8_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_146_ = 0;
v___x_147_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*1, v___x_146_);
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_140_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__9));
v___x_150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = lean_box(1);
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__11));
v___x_154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_139_);
v___x_156_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(v_upperBound_135_, v___x_142_);
v___x_157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_141_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set_uint8(v___x_158_, sizeof(void*)*1, v___x_146_);
v___x_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_155_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_obj_once(&l_Lean_Omega_instReprConstraint_repr___redArg___closed__14, &l_Lean_Omega_instReprConstraint_repr___redArg___closed__14_once, _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__14);
v___x_161_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__15));
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_159_);
v___x_163_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__16));
v___x_164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_160_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_146_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr(lean_object* v_x_169_, lean_object* v_prec_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Omega_instReprConstraint_repr___redArg(v_x_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr___boxed(lean_object* v_x_172_, lean_object* v_prec_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Omega_instReprConstraint_repr(v_x_172_, v_prec_173_);
lean_dec(v_prec_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0(lean_object* v_x_180_){
_start:
{
lean_object* v_intZero_181_; uint8_t v_isNeg_182_; 
v_intZero_181_ = lean_obj_once(&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4, &l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once, _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4);
v_isNeg_182_ = lean_int_dec_lt(v_x_180_, v_intZero_181_);
if (v_isNeg_182_ == 0)
{
lean_object* v_a_183_; lean_object* v___x_184_; 
v_a_183_ = lean_nat_abs(v_x_180_);
v___x_184_ = l_Nat_reprFast(v_a_183_);
return v___x_184_;
}
else
{
lean_object* v_abs_185_; lean_object* v_one_186_; lean_object* v_a_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_abs_185_ = lean_nat_abs(v_x_180_);
v_one_186_ = lean_unsigned_to_nat(1u);
v_a_187_ = lean_nat_sub(v_abs_185_, v_one_186_);
lean_dec(v_abs_185_);
v___x_188_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___closed__0));
v___x_189_ = lean_nat_add(v_a_187_, v_one_186_);
lean_dec(v_a_187_);
v___x_190_ = l_Nat_reprFast(v___x_189_);
v___x_191_ = lean_string_append(v___x_188_, v___x_190_);
lean_dec_ref(v___x_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___boxed(lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0(v_x_192_);
lean_dec(v_x_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_instToString___private__1(lean_object* v_x_205_){
_start:
{
lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v_lowerBound_212_; 
v_lowerBound_212_ = lean_ctor_get(v_x_205_, 0);
if (lean_obj_tag(v_lowerBound_212_) == 0)
{
lean_object* v_upperBound_213_; 
v_upperBound_213_ = lean_ctor_get(v_x_205_, 1);
if (lean_obj_tag(v_upperBound_213_) == 0)
{
lean_object* v___x_214_; 
v___x_214_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__1));
return v___x_214_;
}
else
{
lean_object* v_val_215_; lean_object* v___x_216_; lean_object* v___y_218_; lean_object* v_intZero_222_; uint8_t v_isNeg_223_; 
v_val_215_ = lean_ctor_get(v_upperBound_213_, 0);
v___x_216_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__2));
v_intZero_222_ = lean_obj_once(&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4, &l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once, _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4);
v_isNeg_223_ = lean_int_dec_lt(v_val_215_, v_intZero_222_);
if (v_isNeg_223_ == 0)
{
lean_object* v_a_224_; lean_object* v___x_225_; 
v_a_224_ = lean_nat_abs(v_val_215_);
v___x_225_ = l_Nat_reprFast(v_a_224_);
v___y_218_ = v___x_225_;
goto v___jp_217_;
}
else
{
lean_object* v_abs_226_; lean_object* v_one_227_; lean_object* v_a_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_abs_226_ = lean_nat_abs(v_val_215_);
v_one_227_ = lean_unsigned_to_nat(1u);
v_a_228_ = lean_nat_sub(v_abs_226_, v_one_227_);
lean_dec(v_abs_226_);
v___x_229_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___closed__0));
v___x_230_ = lean_nat_add(v_a_228_, v_one_227_);
lean_dec(v_a_228_);
v___x_231_ = l_Nat_reprFast(v___x_230_);
v___x_232_ = lean_string_append(v___x_229_, v___x_231_);
lean_dec_ref(v___x_231_);
v___y_218_ = v___x_232_;
goto v___jp_217_;
}
v___jp_217_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_string_append(v___x_216_, v___y_218_);
lean_dec_ref(v___y_218_);
v___x_220_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__0));
v___x_221_ = lean_string_append(v___x_219_, v___x_220_);
return v___x_221_;
}
}
}
else
{
lean_object* v_upperBound_233_; 
v_upperBound_233_ = lean_ctor_get(v_x_205_, 1);
if (lean_obj_tag(v_upperBound_233_) == 0)
{
lean_object* v_val_234_; lean_object* v___x_235_; lean_object* v___y_237_; lean_object* v_intZero_241_; uint8_t v_isNeg_242_; 
v_val_234_ = lean_ctor_get(v_lowerBound_212_, 0);
v___x_235_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__3));
v_intZero_241_ = lean_obj_once(&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4, &l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once, _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4);
v_isNeg_242_ = lean_int_dec_lt(v_val_234_, v_intZero_241_);
if (v_isNeg_242_ == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; 
v_a_243_ = lean_nat_abs(v_val_234_);
v___x_244_ = l_Nat_reprFast(v_a_243_);
v___y_237_ = v___x_244_;
goto v___jp_236_;
}
else
{
lean_object* v_abs_245_; lean_object* v_one_246_; lean_object* v_a_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_abs_245_ = lean_nat_abs(v_val_234_);
v_one_246_ = lean_unsigned_to_nat(1u);
v_a_247_ = lean_nat_sub(v_abs_245_, v_one_246_);
lean_dec(v_abs_245_);
v___x_248_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___closed__0));
v___x_249_ = lean_nat_add(v_a_247_, v_one_246_);
lean_dec(v_a_247_);
v___x_250_ = l_Nat_reprFast(v___x_249_);
v___x_251_ = lean_string_append(v___x_248_, v___x_250_);
lean_dec_ref(v___x_250_);
v___y_237_ = v___x_251_;
goto v___jp_236_;
}
v___jp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_string_append(v___x_235_, v___y_237_);
lean_dec_ref(v___y_237_);
v___x_239_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__4));
v___x_240_ = lean_string_append(v___x_238_, v___x_239_);
return v___x_240_;
}
}
else
{
lean_object* v_val_252_; lean_object* v_val_253_; uint8_t v___x_254_; 
v_val_252_ = lean_ctor_get(v_lowerBound_212_, 0);
v_val_253_ = lean_ctor_get(v_upperBound_233_, 0);
v___x_254_ = lean_int_dec_lt(v_val_253_, v_val_252_);
if (v___x_254_ == 0)
{
uint8_t v___x_255_; 
v___x_255_ = lean_int_dec_eq(v_val_252_, v_val_253_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___y_258_; lean_object* v_intZero_273_; uint8_t v_isNeg_274_; 
v___x_256_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__3));
v_intZero_273_ = lean_obj_once(&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4, &l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once, _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4);
v_isNeg_274_ = lean_int_dec_lt(v_val_252_, v_intZero_273_);
if (v_isNeg_274_ == 0)
{
lean_object* v_a_275_; lean_object* v___x_276_; 
v_a_275_ = lean_nat_abs(v_val_252_);
v___x_276_ = l_Nat_reprFast(v_a_275_);
v___y_258_ = v___x_276_;
goto v___jp_257_;
}
else
{
lean_object* v_abs_277_; lean_object* v_one_278_; lean_object* v_a_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_abs_277_ = lean_nat_abs(v_val_252_);
v_one_278_ = lean_unsigned_to_nat(1u);
v_a_279_ = lean_nat_sub(v_abs_277_, v_one_278_);
lean_dec(v_abs_277_);
v___x_280_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___closed__0));
v___x_281_ = lean_nat_add(v_a_279_, v_one_278_);
lean_dec(v_a_279_);
v___x_282_ = l_Nat_reprFast(v___x_281_);
v___x_283_ = lean_string_append(v___x_280_, v___x_282_);
lean_dec_ref(v___x_282_);
v___y_258_ = v___x_283_;
goto v___jp_257_;
}
v___jp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_intZero_262_; uint8_t v_isNeg_263_; 
v___x_259_ = lean_string_append(v___x_256_, v___y_258_);
lean_dec_ref(v___y_258_);
v___x_260_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__5));
v___x_261_ = lean_string_append(v___x_259_, v___x_260_);
v_intZero_262_ = lean_obj_once(&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4, &l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once, _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4);
v_isNeg_263_ = lean_int_dec_lt(v_val_253_, v_intZero_262_);
if (v_isNeg_263_ == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; 
v_a_264_ = lean_nat_abs(v_val_253_);
v___x_265_ = l_Nat_reprFast(v_a_264_);
v___y_207_ = v___x_261_;
v___y_208_ = v___x_265_;
goto v___jp_206_;
}
else
{
lean_object* v_abs_266_; lean_object* v_one_267_; lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_abs_266_ = lean_nat_abs(v_val_253_);
v_one_267_ = lean_unsigned_to_nat(1u);
v_a_268_ = lean_nat_sub(v_abs_266_, v_one_267_);
lean_dec(v_abs_266_);
v___x_269_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___closed__0));
v___x_270_ = lean_nat_add(v_a_268_, v_one_267_);
lean_dec(v_a_268_);
v___x_271_ = l_Nat_reprFast(v___x_270_);
v___x_272_ = lean_string_append(v___x_269_, v___x_271_);
lean_dec_ref(v___x_271_);
v___y_207_ = v___x_261_;
v___y_208_ = v___x_272_;
goto v___jp_206_;
}
}
}
else
{
lean_object* v___x_284_; lean_object* v___y_286_; lean_object* v_intZero_290_; uint8_t v_isNeg_291_; 
v___x_284_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__6));
v_intZero_290_ = lean_obj_once(&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4, &l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once, _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4);
v_isNeg_291_ = lean_int_dec_lt(v_val_252_, v_intZero_290_);
if (v_isNeg_291_ == 0)
{
lean_object* v_a_292_; lean_object* v___x_293_; 
v_a_292_ = lean_nat_abs(v_val_252_);
v___x_293_ = l_Nat_reprFast(v_a_292_);
v___y_286_ = v___x_293_;
goto v___jp_285_;
}
else
{
lean_object* v_abs_294_; lean_object* v_one_295_; lean_object* v_a_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_abs_294_ = lean_nat_abs(v_val_252_);
v_one_295_ = lean_unsigned_to_nat(1u);
v_a_296_ = lean_nat_sub(v_abs_294_, v_one_295_);
lean_dec(v_abs_294_);
v___x_297_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_instToStringInt___lam__0___closed__0));
v___x_298_ = lean_nat_add(v_a_296_, v_one_295_);
lean_dec(v_a_296_);
v___x_299_ = l_Nat_reprFast(v___x_298_);
v___x_300_ = lean_string_append(v___x_297_, v___x_299_);
lean_dec_ref(v___x_299_);
v___y_286_ = v___x_300_;
goto v___jp_285_;
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_string_append(v___x_284_, v___y_286_);
lean_dec_ref(v___y_286_);
v___x_288_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__7));
v___x_289_ = lean_string_append(v___x_287_, v___x_288_);
return v___x_289_;
}
}
}
else
{
lean_object* v___x_301_; 
v___x_301_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__8));
return v___x_301_;
}
}
}
v___jp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_string_append(v___y_207_, v___y_208_);
lean_dec_ref(v___y_208_);
v___x_210_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__0));
v___x_211_ = lean_string_append(v___x_209_, v___x_210_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_instToString___private__1___boxed(lean_object* v_x_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Omega_Constraint_instToString___private__1(v_x_302_);
lean_dec_ref(v_x_302_);
return v_res_303_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_sat(lean_object* v_c_306_, lean_object* v_t_307_){
_start:
{
lean_object* v_lowerBound_308_; lean_object* v_upperBound_309_; uint8_t v___y_311_; 
v_lowerBound_308_ = lean_ctor_get(v_c_306_, 0);
v_upperBound_309_ = lean_ctor_get(v_c_306_, 1);
if (lean_obj_tag(v_lowerBound_308_) == 0)
{
uint8_t v___x_314_; 
v___x_314_ = 1;
v___y_311_ = v___x_314_;
goto v___jp_310_;
}
else
{
lean_object* v_val_315_; uint8_t v___x_316_; 
v_val_315_ = lean_ctor_get(v_lowerBound_308_, 0);
v___x_316_ = lean_int_dec_le(v_val_315_, v_t_307_);
if (v___x_316_ == 0)
{
return v___x_316_;
}
else
{
v___y_311_ = v___x_316_;
goto v___jp_310_;
}
}
v___jp_310_:
{
if (lean_obj_tag(v_upperBound_309_) == 0)
{
return v___y_311_;
}
else
{
lean_object* v_val_312_; uint8_t v___x_313_; 
v_val_312_ = lean_ctor_get(v_upperBound_309_, 0);
v___x_313_ = lean_int_dec_le(v_t_307_, v_val_312_);
if (v___x_313_ == 0)
{
return v___x_313_;
}
else
{
return v___y_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_sat___boxed(lean_object* v_c_317_, lean_object* v_t_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Lean_Omega_Constraint_sat(v_c_317_, v_t_318_);
lean_dec(v_t_318_);
lean_dec_ref(v_c_317_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_map(lean_object* v_c_321_, lean_object* v_f_322_){
_start:
{
lean_object* v_lowerBound_323_; lean_object* v_upperBound_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_354_; 
v_lowerBound_323_ = lean_ctor_get(v_c_321_, 0);
v_upperBound_324_ = lean_ctor_get(v_c_321_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_c_321_);
if (v_isSharedCheck_354_ == 0)
{
v___x_326_ = v_c_321_;
v_isShared_327_ = v_isSharedCheck_354_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_upperBound_324_);
lean_inc(v_lowerBound_323_);
lean_dec(v_c_321_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_354_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___y_329_; 
if (lean_obj_tag(v_lowerBound_323_) == 0)
{
v___y_329_ = v_lowerBound_323_;
goto v___jp_328_;
}
else
{
lean_object* v_val_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_353_; 
v_val_345_ = lean_ctor_get(v_lowerBound_323_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v_lowerBound_323_);
if (v_isSharedCheck_353_ == 0)
{
v___x_347_ = v_lowerBound_323_;
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_val_345_);
lean_dec(v_lowerBound_323_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
lean_inc_ref(v_f_322_);
v___x_349_ = lean_apply_1(v_f_322_, v_val_345_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_349_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
v___y_329_ = v___x_351_;
goto v___jp_328_;
}
}
}
v___jp_328_:
{
if (lean_obj_tag(v_upperBound_324_) == 0)
{
lean_object* v___x_331_; 
lean_dec_ref(v_f_322_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___y_329_);
v___x_331_ = v___x_326_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___y_329_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_upperBound_324_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
else
{
lean_object* v_val_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_344_; 
v_val_333_ = lean_ctor_get(v_upperBound_324_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v_upperBound_324_);
if (v_isSharedCheck_344_ == 0)
{
v___x_335_ = v_upperBound_324_;
v_isShared_336_ = v_isSharedCheck_344_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_val_333_);
lean_dec(v_upperBound_324_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_344_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = lean_apply_1(v_f_322_, v_val_333_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_337_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_343_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_341_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___x_339_);
lean_ctor_set(v___x_326_, 0, v___y_329_);
v___x_341_ = v___x_326_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___y_329_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate___lam__0(lean_object* v_t_355_, lean_object* v_x_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_int_add(v_x_356_, v_t_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate___lam__0___boxed(lean_object* v_t_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Omega_Constraint_translate___lam__0(v_t_358_, v_x_359_);
lean_dec(v_x_359_);
lean_dec(v_t_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate(lean_object* v_c_361_, lean_object* v_t_362_){
_start:
{
lean_object* v___f_363_; lean_object* v___x_364_; 
v___f_363_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_translate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_363_, 0, v_t_362_);
v___x_364_ = l_Lean_Omega_Constraint_map(v_c_361_, v___f_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_flip(lean_object* v_c_365_){
_start:
{
lean_object* v_lowerBound_366_; lean_object* v_upperBound_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
v_lowerBound_366_ = lean_ctor_get(v_c_365_, 0);
v_upperBound_367_ = lean_ctor_get(v_c_365_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_c_365_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v_c_365_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_upperBound_367_);
lean_inc(v_lowerBound_366_);
lean_dec(v_c_365_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_lowerBound_366_);
lean_ctor_set(v___x_369_, 0, v_upperBound_367_);
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_upperBound_367_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_lowerBound_366_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_neg(lean_object* v_c_376_){
_start:
{
lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___f_377_ = ((lean_object*)(l_Lean_Omega_Constraint_neg___closed__0));
v___x_378_ = l_Lean_Omega_Constraint_flip(v_c_376_);
v___x_379_ = l_Lean_Omega_Constraint_map(v___x_378_, v___f_377_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__0(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(1u);
v___x_384_ = lean_nat_to_int(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__1(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__0, &l_Lean_Omega_Constraint_impossible___closed__0_once, _init_l_Lean_Omega_Constraint_impossible___closed__0);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__2(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_obj_once(&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4, &l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once, _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4);
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__3(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__2, &l_Lean_Omega_Constraint_impossible___closed__2_once, _init_l_Lean_Omega_Constraint_impossible___closed__2);
v___x_390_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__1, &l_Lean_Omega_Constraint_impossible___closed__1_once, _init_l_Lean_Omega_Constraint_impossible___closed__1);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible(void){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__3, &l_Lean_Omega_Constraint_impossible___closed__3_once, _init_l_Lean_Omega_Constraint_impossible___closed__3);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_exact(lean_object* v_r_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v_r_393_);
lean_inc_ref(v___x_394_);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_isImpossible(lean_object* v_x_396_){
_start:
{
lean_object* v_lowerBound_397_; 
v_lowerBound_397_ = lean_ctor_get(v_x_396_, 0);
if (lean_obj_tag(v_lowerBound_397_) == 1)
{
lean_object* v_upperBound_398_; 
v_upperBound_398_ = lean_ctor_get(v_x_396_, 1);
if (lean_obj_tag(v_upperBound_398_) == 1)
{
lean_object* v_val_399_; lean_object* v_val_400_; uint8_t v___x_401_; 
v_val_399_ = lean_ctor_get(v_lowerBound_397_, 0);
v_val_400_ = lean_ctor_get(v_upperBound_398_, 0);
v___x_401_ = lean_int_dec_lt(v_val_400_, v_val_399_);
return v___x_401_;
}
else
{
uint8_t v___x_402_; 
v___x_402_ = 0;
return v___x_402_;
}
}
else
{
uint8_t v___x_403_; 
v___x_403_ = 0;
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_isImpossible___boxed(lean_object* v_x_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Lean_Omega_Constraint_isImpossible(v_x_404_);
lean_dec_ref(v_x_404_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_isExact(lean_object* v_x_407_){
_start:
{
lean_object* v_lowerBound_408_; 
v_lowerBound_408_ = lean_ctor_get(v_x_407_, 0);
if (lean_obj_tag(v_lowerBound_408_) == 1)
{
lean_object* v_upperBound_409_; 
v_upperBound_409_ = lean_ctor_get(v_x_407_, 1);
if (lean_obj_tag(v_upperBound_409_) == 1)
{
lean_object* v_val_410_; lean_object* v_val_411_; uint8_t v___x_412_; 
v_val_410_ = lean_ctor_get(v_lowerBound_408_, 0);
v_val_411_ = lean_ctor_get(v_upperBound_409_, 0);
v___x_412_ = lean_int_dec_eq(v_val_410_, v_val_411_);
return v___x_412_;
}
else
{
uint8_t v___x_413_; 
v___x_413_ = 0;
return v___x_413_;
}
}
else
{
uint8_t v___x_414_; 
v___x_414_ = 0;
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_isExact___boxed(lean_object* v_x_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Lean_Omega_Constraint_isExact(v_x_415_);
lean_dec_ref(v_x_415_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter___redArg(lean_object* v_x_418_, lean_object* v_h__1_419_, lean_object* v_h__2_420_){
_start:
{
lean_object* v_lowerBound_421_; 
v_lowerBound_421_ = lean_ctor_get(v_x_418_, 0);
if (lean_obj_tag(v_lowerBound_421_) == 1)
{
lean_object* v_upperBound_422_; 
v_upperBound_422_ = lean_ctor_get(v_x_418_, 1);
if (lean_obj_tag(v_upperBound_422_) == 1)
{
lean_object* v_val_423_; lean_object* v_val_424_; lean_object* v___x_425_; 
lean_inc_ref(v_upperBound_422_);
lean_inc_ref(v_lowerBound_421_);
lean_dec(v_h__2_420_);
lean_dec_ref(v_x_418_);
v_val_423_ = lean_ctor_get(v_lowerBound_421_, 0);
lean_inc(v_val_423_);
lean_dec_ref(v_lowerBound_421_);
v_val_424_ = lean_ctor_get(v_upperBound_422_, 0);
lean_inc(v_val_424_);
lean_dec_ref(v_upperBound_422_);
v___x_425_ = lean_apply_2(v_h__1_419_, v_val_423_, v_val_424_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; 
lean_dec(v_h__1_419_);
v___x_426_ = lean_apply_2(v_h__2_420_, v_x_418_, lean_box(0));
return v___x_426_;
}
}
else
{
lean_object* v___x_427_; 
lean_dec(v_h__1_419_);
v___x_427_ = lean_apply_2(v_h__2_420_, v_x_418_, lean_box(0));
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter(lean_object* v_motive_428_, lean_object* v_x_429_, lean_object* v_h__1_430_, lean_object* v_h__2_431_){
_start:
{
lean_object* v_lowerBound_432_; 
v_lowerBound_432_ = lean_ctor_get(v_x_429_, 0);
if (lean_obj_tag(v_lowerBound_432_) == 1)
{
lean_object* v_upperBound_433_; 
v_upperBound_433_ = lean_ctor_get(v_x_429_, 1);
if (lean_obj_tag(v_upperBound_433_) == 1)
{
lean_object* v_val_434_; lean_object* v_val_435_; lean_object* v___x_436_; 
lean_inc_ref(v_upperBound_433_);
lean_inc_ref(v_lowerBound_432_);
lean_dec(v_h__2_431_);
lean_dec_ref(v_x_429_);
v_val_434_ = lean_ctor_get(v_lowerBound_432_, 0);
lean_inc(v_val_434_);
lean_dec_ref(v_lowerBound_432_);
v_val_435_ = lean_ctor_get(v_upperBound_433_, 0);
lean_inc(v_val_435_);
lean_dec_ref(v_upperBound_433_);
v___x_436_ = lean_apply_2(v_h__1_430_, v_val_434_, v_val_435_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; 
lean_dec(v_h__1_430_);
v___x_437_ = lean_apply_2(v_h__2_431_, v_x_429_, lean_box(0));
return v___x_437_;
}
}
else
{
lean_object* v___x_438_; 
lean_dec(v_h__1_430_);
v___x_438_ = lean_apply_2(v_h__2_431_, v_x_429_, lean_box(0));
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale___lam__0(lean_object* v_k_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_int_mul(v_k_439_, v_x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale___lam__0___boxed(lean_object* v_k_442_, lean_object* v_x_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Omega_Constraint_scale___lam__0(v_k_442_, v_x_443_);
lean_dec(v_x_443_);
lean_dec(v_k_442_);
return v_res_444_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_scale___closed__0(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__2, &l_Lean_Omega_Constraint_impossible___closed__2_once, _init_l_Lean_Omega_Constraint_impossible___closed__2);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale(lean_object* v_k_447_, lean_object* v_c_448_){
_start:
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_obj_once(&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4, &l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once, _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4);
v___x_450_ = lean_int_dec_eq(v_k_447_, v___x_449_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; 
v___x_451_ = lean_int_dec_lt(v___x_449_, v_k_447_);
if (v___x_451_ == 0)
{
lean_object* v___f_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___f_452_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_scale___lam__0___boxed), 2, 1);
lean_closure_set(v___f_452_, 0, v_k_447_);
v___x_453_ = l_Lean_Omega_Constraint_flip(v_c_448_);
v___x_454_ = l_Lean_Omega_Constraint_map(v___x_453_, v___f_452_);
return v___x_454_;
}
else
{
lean_object* v___f_455_; lean_object* v___x_456_; 
v___f_455_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_scale___lam__0___boxed), 2, 1);
lean_closure_set(v___f_455_, 0, v_k_447_);
v___x_456_ = l_Lean_Omega_Constraint_map(v_c_448_, v___f_455_);
return v___x_456_;
}
}
else
{
uint8_t v___x_457_; 
lean_dec(v_k_447_);
v___x_457_ = l_Lean_Omega_Constraint_isImpossible(v_c_448_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
lean_dec_ref(v_c_448_);
v___x_458_ = lean_obj_once(&l_Lean_Omega_Constraint_scale___closed__0, &l_Lean_Omega_Constraint_scale___closed__0_once, _init_l_Lean_Omega_Constraint_scale___closed__0);
return v___x_458_;
}
else
{
return v_c_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_add(lean_object* v_x_459_, lean_object* v_y_460_){
_start:
{
lean_object* v_lowerBound_461_; lean_object* v_upperBound_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_504_; 
v_lowerBound_461_ = lean_ctor_get(v_x_459_, 0);
v_upperBound_462_ = lean_ctor_get(v_x_459_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_x_459_);
if (v_isSharedCheck_504_ == 0)
{
v___x_464_ = v_x_459_;
v_isShared_465_ = v_isSharedCheck_504_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_upperBound_462_);
lean_inc(v_lowerBound_461_);
lean_dec(v_x_459_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_504_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___y_467_; 
if (lean_obj_tag(v_lowerBound_461_) == 0)
{
v___y_467_ = v_lowerBound_461_;
goto v___jp_466_;
}
else
{
lean_object* v_lowerBound_493_; 
v_lowerBound_493_ = lean_ctor_get(v_y_460_, 0);
lean_inc(v_lowerBound_493_);
if (lean_obj_tag(v_lowerBound_493_) == 0)
{
lean_dec_ref(v_lowerBound_461_);
v___y_467_ = v_lowerBound_493_;
goto v___jp_466_;
}
else
{
lean_object* v_val_494_; lean_object* v_val_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
v_val_494_ = lean_ctor_get(v_lowerBound_461_, 0);
lean_inc(v_val_494_);
lean_dec_ref(v_lowerBound_461_);
v_val_495_ = lean_ctor_get(v_lowerBound_493_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v_lowerBound_493_);
if (v_isSharedCheck_503_ == 0)
{
v___x_497_ = v_lowerBound_493_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_val_495_);
lean_dec(v_lowerBound_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_int_add(v_val_494_, v_val_495_);
lean_dec(v_val_495_);
lean_dec(v_val_494_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_499_);
v___x_501_ = v___x_497_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
v___y_467_ = v___x_501_;
goto v___jp_466_;
}
}
}
}
v___jp_466_:
{
if (lean_obj_tag(v_upperBound_462_) == 0)
{
lean_object* v___x_469_; 
lean_dec_ref(v_y_460_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___y_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___y_467_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_upperBound_462_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
else
{
lean_object* v_upperBound_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_491_; 
lean_del_object(v___x_464_);
v_upperBound_471_ = lean_ctor_get(v_y_460_, 1);
v_isSharedCheck_491_ = !lean_is_exclusive(v_y_460_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; 
v_unused_492_ = lean_ctor_get(v_y_460_, 0);
lean_dec(v_unused_492_);
v___x_473_ = v_y_460_;
v_isShared_474_ = v_isSharedCheck_491_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_upperBound_471_);
lean_dec(v_y_460_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_491_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
if (lean_obj_tag(v_upperBound_471_) == 0)
{
lean_object* v___x_476_; 
lean_dec_ref(v_upperBound_462_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___y_467_);
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___y_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_upperBound_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
else
{
lean_object* v_val_478_; lean_object* v_val_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_490_; 
v_val_478_ = lean_ctor_get(v_upperBound_462_, 0);
lean_inc(v_val_478_);
lean_dec_ref(v_upperBound_462_);
v_val_479_ = lean_ctor_get(v_upperBound_471_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_upperBound_471_);
if (v_isSharedCheck_490_ == 0)
{
v___x_481_ = v_upperBound_471_;
v_isShared_482_ = v_isSharedCheck_490_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_val_479_);
lean_dec(v_upperBound_471_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_490_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = lean_int_add(v_val_478_, v_val_479_);
lean_dec(v_val_479_);
lean_dec(v_val_478_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_489_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_485_);
lean_ctor_set(v___x_473_, 0, v___y_467_);
v___x_487_ = v___x_473_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___y_467_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_485_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combo(lean_object* v_a_505_, lean_object* v_x_506_, lean_object* v_b_507_, lean_object* v_y_508_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = l_Lean_Omega_Constraint_scale(v_a_505_, v_x_506_);
v___x_510_ = l_Lean_Omega_Constraint_scale(v_b_507_, v_y_508_);
v___x_511_ = l_Lean_Omega_Constraint_add(v___x_509_, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__0(lean_object* v_x_512_, lean_object* v_y_513_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = lean_int_dec_le(v_x_512_, v_y_513_);
if (v___x_514_ == 0)
{
lean_inc(v_x_512_);
return v_x_512_;
}
else
{
lean_inc(v_y_513_);
return v_y_513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__0___boxed(lean_object* v_x_515_, lean_object* v_y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Omega_Constraint_combine___lam__0(v_x_515_, v_y_516_);
lean_dec(v_y_516_);
lean_dec(v_x_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__1(lean_object* v_x_518_, lean_object* v_y_519_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = lean_int_dec_le(v_x_518_, v_y_519_);
if (v___x_520_ == 0)
{
lean_inc(v_y_519_);
return v_y_519_;
}
else
{
lean_inc(v_x_518_);
return v_x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__1___boxed(lean_object* v_x_521_, lean_object* v_y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Omega_Constraint_combine___lam__1(v_x_521_, v_y_522_);
lean_dec(v_y_522_);
lean_dec(v_x_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine(lean_object* v_x_526_, lean_object* v_y_527_){
_start:
{
lean_object* v_lowerBound_528_; lean_object* v_upperBound_529_; lean_object* v_lowerBound_530_; lean_object* v_upperBound_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_542_; 
v_lowerBound_528_ = lean_ctor_get(v_x_526_, 0);
lean_inc(v_lowerBound_528_);
v_upperBound_529_ = lean_ctor_get(v_x_526_, 1);
lean_inc(v_upperBound_529_);
lean_dec_ref(v_x_526_);
v_lowerBound_530_ = lean_ctor_get(v_y_527_, 0);
v_upperBound_531_ = lean_ctor_get(v_y_527_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_y_527_);
if (v_isSharedCheck_542_ == 0)
{
v___x_533_ = v_y_527_;
v_isShared_534_ = v_isSharedCheck_542_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_upperBound_531_);
lean_inc(v_lowerBound_530_);
lean_dec(v_y_527_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_542_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___f_535_; lean_object* v___f_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___f_535_ = ((lean_object*)(l_Lean_Omega_Constraint_combine___closed__0));
v___f_536_ = ((lean_object*)(l_Lean_Omega_Constraint_combine___closed__1));
v___x_537_ = l_Option_merge___redArg(v___f_535_, v_lowerBound_528_, v_lowerBound_530_);
v___x_538_ = l_Option_merge___redArg(v___f_536_, v_upperBound_529_, v_upperBound_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_538_);
lean_ctor_set(v___x_533_, 0, v___x_537_);
v___x_540_ = v___x_533_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Option_merge_match__1_splitter___redArg(lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_h__1_545_, lean_object* v_h__2_546_, lean_object* v_h__3_547_, lean_object* v_h__4_548_){
_start:
{
if (lean_obj_tag(v_x_543_) == 0)
{
lean_dec(v_h__4_548_);
lean_dec(v_h__2_546_);
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v_h__3_547_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_apply_1(v_h__1_545_, v___x_549_);
return v___x_550_;
}
else
{
lean_object* v_val_551_; lean_object* v___x_552_; 
lean_dec(v_h__1_545_);
v_val_551_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_val_551_);
lean_dec_ref(v_x_544_);
v___x_552_ = lean_apply_1(v_h__3_547_, v_val_551_);
return v___x_552_;
}
}
else
{
lean_dec(v_h__3_547_);
lean_dec(v_h__1_545_);
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_val_553_; lean_object* v___x_554_; 
lean_dec(v_h__4_548_);
v_val_553_ = lean_ctor_get(v_x_543_, 0);
lean_inc(v_val_553_);
lean_dec_ref(v_x_543_);
v___x_554_ = lean_apply_1(v_h__2_546_, v_val_553_);
return v___x_554_;
}
else
{
lean_object* v_val_555_; lean_object* v_val_556_; lean_object* v___x_557_; 
lean_dec(v_h__2_546_);
v_val_555_ = lean_ctor_get(v_x_543_, 0);
lean_inc(v_val_555_);
lean_dec_ref(v_x_543_);
v_val_556_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_val_556_);
lean_dec_ref(v_x_544_);
v___x_557_ = lean_apply_2(v_h__4_548_, v_val_555_, v_val_556_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Option_merge_match__1_splitter(lean_object* v_00_u03b1_558_, lean_object* v_motive_559_, lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_h__1_562_, lean_object* v_h__2_563_, lean_object* v_h__3_564_, lean_object* v_h__4_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l___private_Init_Omega_Constraint_0__Option_merge_match__1_splitter___redArg(v_x_560_, v_x_561_, v_h__1_562_, v_h__2_563_, v_h__3_564_, v_h__4_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_div(lean_object* v_c_567_, lean_object* v_k_568_){
_start:
{
lean_object* v_lowerBound_569_; lean_object* v_upperBound_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_604_; 
v_lowerBound_569_ = lean_ctor_get(v_c_567_, 0);
v_upperBound_570_ = lean_ctor_get(v_c_567_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_c_567_);
if (v_isSharedCheck_604_ == 0)
{
v___x_572_ = v_c_567_;
v_isShared_573_ = v_isSharedCheck_604_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_upperBound_570_);
lean_inc(v_lowerBound_569_);
lean_dec(v_c_567_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_604_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___y_575_; 
if (lean_obj_tag(v_lowerBound_569_) == 0)
{
v___y_575_ = v_lowerBound_569_;
goto v___jp_574_;
}
else
{
lean_object* v_val_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_603_; 
v_val_592_ = lean_ctor_get(v_lowerBound_569_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v_lowerBound_569_);
if (v_isSharedCheck_603_ == 0)
{
v___x_594_ = v_lowerBound_569_;
v_isShared_595_ = v_isSharedCheck_603_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_val_592_);
lean_dec(v_lowerBound_569_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_603_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_596_ = lean_int_neg(v_val_592_);
lean_dec(v_val_592_);
lean_inc(v_k_568_);
v___x_597_ = lean_nat_to_int(v_k_568_);
v___x_598_ = lean_int_ediv(v___x_596_, v___x_597_);
lean_dec(v___x_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_int_neg(v___x_598_);
lean_dec(v___x_598_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_599_);
v___x_601_ = v___x_594_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
v___y_575_ = v___x_601_;
goto v___jp_574_;
}
}
}
v___jp_574_:
{
if (lean_obj_tag(v_upperBound_570_) == 0)
{
lean_object* v___x_577_; 
lean_dec(v_k_568_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___y_575_);
v___x_577_ = v___x_572_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___y_575_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_upperBound_570_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
else
{
lean_object* v_val_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_591_; 
v_val_579_ = lean_ctor_get(v_upperBound_570_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_upperBound_570_);
if (v_isSharedCheck_591_ == 0)
{
v___x_581_ = v_upperBound_570_;
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_val_579_);
lean_dec(v_upperBound_570_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_583_ = lean_nat_to_int(v_k_568_);
v___x_584_ = lean_int_ediv(v_val_579_, v___x_583_);
lean_dec(v___x_583_);
lean_dec(v_val_579_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_584_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_590_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_588_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v___x_586_);
lean_ctor_set(v___x_572_, 0, v___y_575_);
v___x_588_ = v___x_572_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___y_575_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_sat_x27(lean_object* v_c_605_, lean_object* v_x_606_, lean_object* v_y_607_){
_start:
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = l_Lean_Omega_IntList_dot(v_x_606_, v_y_607_);
v___x_609_ = l_Lean_Omega_Constraint_sat(v_c_605_, v___x_608_);
lean_dec(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_sat_x27___boxed(lean_object* v_c_610_, lean_object* v_x_611_, lean_object* v_y_612_){
_start:
{
uint8_t v_res_613_; lean_object* v_r_614_; 
v_res_613_ = l_Lean_Omega_Constraint_sat_x27(v_c_610_, v_x_611_, v_y_612_);
lean_dec(v_x_611_);
lean_dec_ref(v_c_610_);
v_r_614_ = lean_box(v_res_613_);
return v_r_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_normalize_x3f(lean_object* v_x_615_){
_start:
{
lean_object* v_fst_616_; lean_object* v_snd_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_646_; 
v_fst_616_ = lean_ctor_get(v_x_615_, 0);
v_snd_617_ = lean_ctor_get(v_x_615_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_646_ == 0)
{
v___x_619_ = v_x_615_;
v_isShared_620_ = v_isSharedCheck_646_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_snd_617_);
lean_inc(v_fst_616_);
lean_dec(v_x_615_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_646_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_gcd_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_gcd_621_ = l_Lean_Omega_IntList_gcd(v_snd_617_);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_nat_dec_eq(v_gcd_621_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_dec_eq(v_gcd_621_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
lean_inc(v_gcd_621_);
v___x_626_ = l_Lean_Omega_Constraint_div(v_fst_616_, v_gcd_621_);
v___x_627_ = lean_nat_to_int(v_gcd_621_);
v___x_628_ = l_Lean_Omega_IntList_sdiv(v_snd_617_, v___x_627_);
lean_dec(v___x_627_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_628_);
lean_ctor_set(v___x_619_, 0, v___x_626_);
v___x_630_ = v___x_619_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_628_);
v___x_630_ = v_reuseFailAlloc_632_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; 
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
else
{
lean_object* v___x_633_; 
lean_dec(v_gcd_621_);
lean_del_object(v___x_619_);
lean_dec(v_snd_617_);
lean_dec(v_fst_616_);
v___x_633_ = lean_box(0);
return v___x_633_;
}
}
else
{
lean_object* v___x_634_; uint8_t v___x_635_; 
lean_dec(v_gcd_621_);
v___x_634_ = lean_obj_once(&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4, &l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once, _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4);
v___x_635_ = l_Lean_Omega_Constraint_sat(v_fst_616_, v___x_634_);
lean_dec(v_fst_616_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = l_Lean_Omega_Constraint_impossible;
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_636_);
v___x_638_ = v___x_619_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_snd_617_);
v___x_638_ = v_reuseFailAlloc_640_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; 
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
else
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = ((lean_object*)(l_Lean_Omega_Constraint_trivial));
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_641_);
v___x_643_ = v___x_619_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_snd_617_);
v___x_643_ = v_reuseFailAlloc_645_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; 
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_normalize(lean_object* v_p_647_){
_start:
{
lean_object* v___x_648_; 
lean_inc_ref(v_p_647_);
v___x_648_ = l_Lean_Omega_normalize_x3f(v_p_647_);
if (lean_obj_tag(v___x_648_) == 0)
{
return v_p_647_;
}
else
{
lean_object* v_val_649_; 
lean_dec_ref(v_p_647_);
v_val_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_649_);
lean_dec_ref(v___x_648_);
return v_val_649_;
}
}
}
static lean_object* _init_l_Lean_Omega_positivize_x3f___closed__0(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__0, &l_Lean_Omega_Constraint_impossible___closed__0_once, _init_l_Lean_Omega_Constraint_impossible___closed__0);
v___x_651_ = lean_int_neg(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_positivize_x3f(lean_object* v_x_652_){
_start:
{
lean_object* v_fst_653_; lean_object* v_snd_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_669_; 
v_fst_653_ = lean_ctor_get(v_x_652_, 0);
v_snd_654_ = lean_ctor_get(v_x_652_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_669_ == 0)
{
v___x_656_ = v_x_652_;
v_isShared_657_ = v_isSharedCheck_669_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_snd_654_);
lean_inc(v_fst_653_);
lean_dec(v_x_652_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_669_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_obj_once(&l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4, &l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4_once, _init_l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__4);
lean_inc(v_snd_654_);
v___x_659_ = l_Lean_Omega_IntList_leading(v_snd_654_);
v___x_660_ = lean_int_dec_le(v___x_658_, v___x_659_);
lean_dec(v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_661_ = l_Lean_Omega_Constraint_neg(v_fst_653_);
v___x_662_ = lean_obj_once(&l_Lean_Omega_positivize_x3f___closed__0, &l_Lean_Omega_positivize_x3f___closed__0_once, _init_l_Lean_Omega_positivize_x3f___closed__0);
v___x_663_ = l_Lean_Omega_IntList_smul(v_snd_654_, v___x_662_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v___x_663_);
lean_ctor_set(v___x_656_, 0, v___x_661_);
v___x_665_ = v___x_656_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_663_);
v___x_665_ = v_reuseFailAlloc_667_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
else
{
lean_object* v___x_668_; 
lean_del_object(v___x_656_);
lean_dec(v_snd_654_);
lean_dec(v_fst_653_);
v___x_668_ = lean_box(0);
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidy_x3f(lean_object* v_x_670_){
_start:
{
lean_object* v___x_671_; 
lean_inc_ref(v_x_670_);
v___x_671_ = l_Lean_Omega_positivize_x3f(v_x_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Omega_normalize_x3f(v_x_670_);
return v___x_672_;
}
else
{
lean_object* v_val_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v_x_670_);
v_val_673_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_681_ == 0)
{
v___x_675_ = v___x_671_;
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_val_673_);
lean_dec(v___x_671_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = l_Lean_Omega_normalize(v_val_673_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidy(lean_object* v_p_682_){
_start:
{
lean_object* v___x_683_; 
lean_inc_ref(v_p_682_);
v___x_683_ = l_Lean_Omega_tidy_x3f(v_p_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
return v_p_682_;
}
else
{
lean_object* v_val_684_; 
lean_dec_ref(v_p_682_);
v_val_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_val_684_);
lean_dec_ref(v___x_683_);
return v_val_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidyConstraint(lean_object* v_s_685_, lean_object* v_x_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_fst_689_; 
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_s_685_);
lean_ctor_set(v___x_687_, 1, v_x_686_);
v___x_688_ = l_Lean_Omega_tidy(v___x_687_);
v_fst_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_fst_689_);
lean_dec_ref(v___x_688_);
return v_fst_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidyCoeffs(lean_object* v_s_690_, lean_object* v_x_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_snd_694_; 
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_s_690_);
lean_ctor_set(v___x_692_, 1, v_x_691_);
v___x_693_ = l_Lean_Omega_tidy(v___x_692_);
v_snd_694_ = lean_ctor_get(v___x_693_, 1);
lean_inc(v_snd_694_);
lean_dec_ref(v___x_693_);
return v_snd_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter___redArg(lean_object* v_x_695_, lean_object* v_h__1_696_, lean_object* v_h__2_697_){
_start:
{
if (lean_obj_tag(v_x_695_) == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec(v_h__2_697_);
v___x_698_ = lean_box(0);
v___x_699_ = lean_apply_1(v_h__1_696_, v___x_698_);
return v___x_699_;
}
else
{
lean_object* v_val_700_; lean_object* v_fst_701_; lean_object* v_snd_702_; lean_object* v___x_703_; 
lean_dec(v_h__1_696_);
v_val_700_ = lean_ctor_get(v_x_695_, 0);
lean_inc(v_val_700_);
lean_dec_ref(v_x_695_);
v_fst_701_ = lean_ctor_get(v_val_700_, 0);
lean_inc(v_fst_701_);
v_snd_702_ = lean_ctor_get(v_val_700_, 1);
lean_inc(v_snd_702_);
lean_dec(v_val_700_);
v___x_703_ = lean_apply_2(v_h__2_697_, v_fst_701_, v_snd_702_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter(lean_object* v_motive_704_, lean_object* v_x_705_, lean_object* v_h__1_706_, lean_object* v_h__2_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter___redArg(v_x_705_, v_h__1_706_, v_h__2_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term___lam__0(lean_object* v_m_709_, lean_object* v_x_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Int_bmod(v_x_710_, v_m_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term___lam__0___boxed(lean_object* v_m_712_, lean_object* v_x_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Omega_bmod__div__term___lam__0(v_m_712_, v_x_713_);
lean_dec(v_x_713_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term(lean_object* v_m_715_, lean_object* v_a_716_, lean_object* v_b_717_){
_start:
{
lean_object* v___f_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_inc(v_m_715_);
v___f_718_ = lean_alloc_closure((void*)(l_Lean_Omega_bmod__div__term___lam__0___boxed), 2, 1);
lean_closure_set(v___f_718_, 0, v_m_715_);
lean_inc(v_b_717_);
v___x_719_ = l_Lean_Omega_IntList_dot(v_a_716_, v_b_717_);
lean_inc(v_m_715_);
v___x_720_ = l_Int_bmod(v___x_719_, v_m_715_);
lean_dec(v___x_719_);
v___x_721_ = lean_box(0);
v___x_722_ = l_List_mapTR_loop___redArg(v___f_718_, v_a_716_, v___x_721_);
v___x_723_ = l_Lean_Omega_IntList_dot(v___x_722_, v_b_717_);
lean_dec(v___x_722_);
v___x_724_ = lean_int_sub(v___x_720_, v___x_723_);
lean_dec(v___x_723_);
lean_dec(v___x_720_);
v___x_725_ = lean_nat_to_int(v_m_715_);
v___x_726_ = lean_int_ediv(v___x_724_, v___x_725_);
lean_dec(v___x_725_);
lean_dec(v___x_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_bmod__coeffs_spec__0(lean_object* v_m_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
if (lean_obj_tag(v_a_728_) == 0)
{
lean_object* v___x_730_; 
lean_dec(v_m_727_);
v___x_730_ = l_List_reverse___redArg(v_a_729_);
return v___x_730_;
}
else
{
lean_object* v_head_731_; lean_object* v_tail_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_741_; 
v_head_731_ = lean_ctor_get(v_a_728_, 0);
v_tail_732_ = lean_ctor_get(v_a_728_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_a_728_);
if (v_isSharedCheck_741_ == 0)
{
v___x_734_ = v_a_728_;
v_isShared_735_ = v_isSharedCheck_741_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_tail_732_);
lean_inc(v_head_731_);
lean_dec(v_a_728_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_741_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
lean_inc(v_m_727_);
v___x_736_ = l_Int_bmod(v_head_731_, v_m_727_);
lean_dec(v_head_731_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v_a_729_);
lean_ctor_set(v___x_734_, 0, v___x_736_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_a_729_);
v___x_738_ = v_reuseFailAlloc_740_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
v_a_728_ = v_tail_732_;
v_a_729_ = v___x_738_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__coeffs(lean_object* v_m_742_, lean_object* v_i_743_, lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_745_ = lean_box(0);
lean_inc(v_m_742_);
v___x_746_ = l_List_mapTR_loop___at___00Lean_Omega_bmod__coeffs_spec__0(v_m_742_, v_x_744_, v___x_745_);
v___x_747_ = lean_nat_to_int(v_m_742_);
v___x_748_ = l_Lean_Omega_IntList_set(v___x_746_, v_i_743_, v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__coeffs___boxed(lean_object* v_m_749_, lean_object* v_i_750_, lean_object* v_x_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Omega_bmod__coeffs(v_m_749_, v_i_750_, v_x_751_);
lean_dec(v_i_750_);
return v_res_752_;
}
}
lean_object* runtime_initialize_Init_Omega_Coeffs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega_Int(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Omega_Constraint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Omega_Coeffs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Omega_Constraint_impossible = _init_l_Lean_Omega_Constraint_impossible();
lean_mark_persistent(l_Lean_Omega_Constraint_impossible);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Omega_Constraint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Omega_Coeffs(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Omega_Int(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Omega_Constraint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Omega_Coeffs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega_Constraint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Omega_Constraint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Omega_Constraint(builtin);
}
#ifdef __cplusplus
}
#endif
