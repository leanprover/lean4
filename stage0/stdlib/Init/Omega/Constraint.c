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
static const lean_closure_object l___private_Init_Omega_Constraint_0__Lean_Omega_instAppendString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Internal_append___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instAppendString___closed__0 = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_instAppendString___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instAppendString = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_instAppendString___closed__0_value;
static lean_once_cell_t l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0;
static const lean_string_object l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1 = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___closed__0 = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___closed__0 = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt = (const lean_object*)&l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___closed__0_value;
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
static lean_object* _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0(void){
_start:
{
lean_object* v_natZero_21_; lean_object* v_intZero_22_; 
v_natZero_21_ = lean_unsigned_to_nat(0u);
v_intZero_22_ = lean_nat_to_int(v_natZero_21_);
return v_intZero_22_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0(lean_object* v_x_24_){
_start:
{
lean_object* v_intZero_25_; uint8_t v_isNeg_26_; 
v_intZero_25_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_26_ = lean_int_dec_lt(v_x_24_, v_intZero_25_);
if (v_isNeg_26_ == 0)
{
lean_object* v_a_27_; lean_object* v___x_28_; 
v_a_27_ = lean_nat_abs(v_x_24_);
v___x_28_ = l_Nat_reprFast(v_a_27_);
return v___x_28_;
}
else
{
lean_object* v_abs_29_; lean_object* v_one_30_; lean_object* v_a_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_abs_29_ = lean_nat_abs(v_x_24_);
v_one_30_ = lean_unsigned_to_nat(1u);
v_a_31_ = lean_nat_sub(v_abs_29_, v_one_30_);
lean_dec(v_abs_29_);
v___x_32_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_33_ = lean_nat_add(v_a_31_, v_one_30_);
lean_dec(v_a_31_);
v___x_34_ = l_Nat_reprFast(v___x_33_);
v___x_35_ = lean_string_append(v___x_32_, v___x_34_);
lean_dec_ref(v___x_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___boxed(lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0(v_x_36_);
lean_dec(v_x_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0(lean_object* v_i_40_, lean_object* v_prec_41_){
_start:
{
lean_object* v___y_43_; lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_47_ = lean_int_dec_lt(v_i_40_, v___x_46_);
if (v___x_47_ == 0)
{
if (v___x_47_ == 0)
{
lean_object* v_a_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_a_48_ = lean_nat_abs(v_i_40_);
v___x_49_ = l_Nat_reprFast(v_a_48_);
v___x_50_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v_abs_51_; lean_object* v_one_52_; lean_object* v_a_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_abs_51_ = lean_nat_abs(v_i_40_);
v_one_52_ = lean_unsigned_to_nat(1u);
v_a_53_ = lean_nat_sub(v_abs_51_, v_one_52_);
lean_dec(v_abs_51_);
v___x_54_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_55_ = lean_nat_add(v_a_53_, v_one_52_);
lean_dec(v_a_53_);
v___x_56_ = l_Nat_reprFast(v___x_55_);
v___x_57_ = lean_string_append(v___x_54_, v___x_56_);
lean_dec_ref(v___x_56_);
v___x_58_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
else
{
if (v___x_47_ == 0)
{
lean_object* v_a_59_; lean_object* v___x_60_; 
v_a_59_ = lean_nat_abs(v_i_40_);
v___x_60_ = l_Nat_reprFast(v_a_59_);
v___y_43_ = v___x_60_;
goto v___jp_42_;
}
else
{
lean_object* v_abs_61_; lean_object* v_one_62_; lean_object* v_a_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_abs_61_ = lean_nat_abs(v_i_40_);
v_one_62_ = lean_unsigned_to_nat(1u);
v_a_63_ = lean_nat_sub(v_abs_61_, v_one_62_);
lean_dec(v_abs_61_);
v___x_64_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_65_ = lean_nat_add(v_a_63_, v_one_62_);
lean_dec(v_a_63_);
v___x_66_ = l_Nat_reprFast(v___x_65_);
v___x_67_ = lean_string_append(v___x_64_, v___x_66_);
lean_dec_ref(v___x_66_);
v___y_43_ = v___x_67_;
goto v___jp_42_;
}
}
v___jp_42_:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_44_, 0, v___y_43_);
v___x_45_ = l_Repr_addAppParen(v___x_44_, v_prec_41_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0___boxed(lean_object* v_i_68_, lean_object* v_prec_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0(v_i_68_, v_prec_69_);
lean_dec(v_prec_69_);
lean_dec(v_i_68_);
return v_res_70_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
if (lean_obj_tag(v_x_74_) == 0)
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
else
{
if (lean_obj_tag(v_x_74_) == 0)
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
else
{
lean_object* v_val_78_; lean_object* v_val_79_; uint8_t v___x_80_; 
v_val_78_ = lean_ctor_get(v_x_73_, 0);
v_val_79_ = lean_ctor_get(v_x_74_, 0);
v___x_80_ = lean_int_dec_eq(v_val_78_, v_val_79_);
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0___boxed(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_x_81_, v_x_82_);
lean_dec(v_x_82_);
lean_dec(v_x_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_instBEqConstraint_beq(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_lowerBound_87_; lean_object* v_upperBound_88_; lean_object* v_lowerBound_89_; lean_object* v_upperBound_90_; uint8_t v___x_91_; 
v_lowerBound_87_ = lean_ctor_get(v_x_85_, 0);
v_upperBound_88_ = lean_ctor_get(v_x_85_, 1);
v_lowerBound_89_ = lean_ctor_get(v_x_86_, 0);
v_upperBound_90_ = lean_ctor_get(v_x_86_, 1);
v___x_91_ = l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_lowerBound_87_, v_lowerBound_89_);
if (v___x_91_ == 0)
{
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = l_Option_instBEq_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_upperBound_88_, v_upperBound_90_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instBEqConstraint_beq___boxed(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Lean_Omega_instBEqConstraint_beq(v_x_93_, v_x_94_);
lean_dec_ref(v_x_94_);
lean_dec_ref(v_x_93_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqConstraint_decEq(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
lean_object* v_lowerBound_101_; lean_object* v_upperBound_102_; lean_object* v_lowerBound_103_; lean_object* v_upperBound_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_lowerBound_101_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_lowerBound_101_);
v_upperBound_102_ = lean_ctor_get(v_x_99_, 1);
lean_inc(v_upperBound_102_);
lean_dec_ref(v_x_99_);
v_lowerBound_103_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_lowerBound_103_);
v_upperBound_104_ = lean_ctor_get(v_x_100_, 1);
lean_inc(v_upperBound_104_);
lean_dec_ref(v_x_100_);
v___x_105_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc_ref(v___x_105_);
v___x_106_ = l_Option_instDecidableEq___redArg(v___x_105_, v_lowerBound_101_, v_lowerBound_103_);
if (v___x_106_ == 0)
{
lean_dec_ref(v___x_105_);
lean_dec(v_upperBound_104_);
lean_dec(v_upperBound_102_);
return v___x_106_;
}
else
{
uint8_t v___x_107_; 
v___x_107_ = l_Option_instDecidableEq___redArg(v___x_105_, v_upperBound_102_, v_upperBound_104_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqConstraint_decEq___boxed(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_x_108_, v_x_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqConstraint(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_x_112_, v_x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqConstraint___boxed(lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Lean_Omega_instDecidableEqConstraint(v_x_115_, v_x_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__1));
return v___x_127_;
}
else
{
lean_object* v_val_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_170_; 
v_val_128_ = lean_ctor_get(v_x_125_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_170_ == 0)
{
v___x_130_ = v_x_125_;
v_isShared_131_ = v_isSharedCheck_170_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_val_128_);
lean_dec(v_x_125_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_170_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___y_134_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_132_ = ((lean_object*)(l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__3));
v___x_137_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_138_ = lean_int_dec_lt(v_val_128_, v___x_137_);
if (v___x_138_ == 0)
{
if (v___x_138_ == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
v_a_139_ = lean_nat_abs(v_val_128_);
lean_dec(v_val_128_);
v___x_140_ = l_Nat_reprFast(v_a_139_);
if (v_isShared_131_ == 0)
{
lean_ctor_set_tag(v___x_130_, 3);
lean_ctor_set(v___x_130_, 0, v___x_140_);
v___x_142_ = v___x_130_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
v___y_134_ = v___x_142_;
goto v___jp_133_;
}
}
else
{
lean_object* v_abs_144_; lean_object* v_one_145_; lean_object* v_a_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v_abs_144_ = lean_nat_abs(v_val_128_);
lean_dec(v_val_128_);
v_one_145_ = lean_unsigned_to_nat(1u);
v_a_146_ = lean_nat_sub(v_abs_144_, v_one_145_);
lean_dec(v_abs_144_);
v___x_147_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_148_ = lean_nat_add(v_a_146_, v_one_145_);
lean_dec(v_a_146_);
v___x_149_ = l_Nat_reprFast(v___x_148_);
v___x_150_ = lean_string_append(v___x_147_, v___x_149_);
lean_dec_ref(v___x_149_);
if (v_isShared_131_ == 0)
{
lean_ctor_set_tag(v___x_130_, 3);
lean_ctor_set(v___x_130_, 0, v___x_150_);
v___x_152_ = v___x_130_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
v___y_134_ = v___x_152_;
goto v___jp_133_;
}
}
}
else
{
lean_object* v___x_154_; lean_object* v___y_156_; 
v___x_154_ = lean_unsigned_to_nat(1024u);
if (v___x_138_ == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; 
v_a_161_ = lean_nat_abs(v_val_128_);
lean_dec(v_val_128_);
v___x_162_ = l_Nat_reprFast(v_a_161_);
v___y_156_ = v___x_162_;
goto v___jp_155_;
}
else
{
lean_object* v_abs_163_; lean_object* v_one_164_; lean_object* v_a_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_abs_163_ = lean_nat_abs(v_val_128_);
lean_dec(v_val_128_);
v_one_164_ = lean_unsigned_to_nat(1u);
v_a_165_ = lean_nat_sub(v_abs_163_, v_one_164_);
lean_dec(v_abs_163_);
v___x_166_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_167_ = lean_nat_add(v_a_165_, v_one_164_);
lean_dec(v_a_165_);
v___x_168_ = l_Nat_reprFast(v___x_167_);
v___x_169_ = lean_string_append(v___x_166_, v___x_168_);
lean_dec_ref(v___x_168_);
v___y_156_ = v___x_169_;
goto v___jp_155_;
}
v___jp_155_:
{
lean_object* v___x_158_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set_tag(v___x_130_, 3);
lean_ctor_set(v___x_130_, 0, v___y_156_);
v___x_158_ = v___x_130_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___y_156_);
v___x_158_ = v_reuseFailAlloc_160_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; 
v___x_159_ = l_Repr_addAppParen(v___x_158_, v___x_154_);
v___y_134_ = v___x_159_;
goto v___jp_133_;
}
}
}
v___jp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_132_);
lean_ctor_set(v___x_135_, 1, v___y_134_);
v___x_136_ = l_Repr_addAppParen(v___x_135_, v_x_126_);
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___boxed(lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(v_x_171_, v_x_172_);
lean_dec(v_x_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Omega_instReprConstraint_repr_spec__1(lean_object* v_a_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_nat_to_int(v_a_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_unsigned_to_nat(14u);
v___x_190_ = lean_nat_to_int(v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__0));
v___x_199_ = lean_string_length(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_obj_once(&l_Lean_Omega_instReprConstraint_repr___redArg___closed__13, &l_Lean_Omega_instReprConstraint_repr___redArg___closed__13_once, _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__13);
v___x_201_ = lean_nat_to_int(v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr___redArg(lean_object* v_x_206_){
_start:
{
lean_object* v_lowerBound_207_; lean_object* v_upperBound_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_241_; 
v_lowerBound_207_ = lean_ctor_get(v_x_206_, 0);
v_upperBound_208_ = lean_ctor_get(v_x_206_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_241_ == 0)
{
v___x_210_ = v_x_206_;
v_isShared_211_ = v_isSharedCheck_241_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_upperBound_208_);
lean_inc(v_lowerBound_207_);
lean_dec(v_x_206_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_241_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_212_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__5));
v___x_213_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__6));
v___x_214_ = lean_obj_once(&l_Lean_Omega_instReprConstraint_repr___redArg___closed__7, &l_Lean_Omega_instReprConstraint_repr___redArg___closed__7_once, _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__7);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(v_lowerBound_207_, v___x_215_);
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 4);
lean_ctor_set(v___x_210_, 1, v___x_216_);
lean_ctor_set(v___x_210_, 0, v___x_214_);
v___x_218_ = v___x_210_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_240_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_219_ = 0;
v___x_220_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*1, v___x_219_);
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_213_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__9));
v___x_223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_box(1);
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__11));
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_212_);
v___x_229_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(v_upperBound_208_, v___x_215_);
v___x_230_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_214_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v___x_219_);
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_228_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_obj_once(&l_Lean_Omega_instReprConstraint_repr___redArg___closed__14, &l_Lean_Omega_instReprConstraint_repr___redArg___closed__14_once, _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__14);
v___x_234_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__15));
v___x_235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_232_);
v___x_236_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__16));
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_233_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*1, v___x_219_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr(lean_object* v_x_242_, lean_object* v_prec_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Omega_instReprConstraint_repr___redArg(v_x_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr___boxed(lean_object* v_x_245_, lean_object* v_prec_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Omega_instReprConstraint_repr(v_x_245_, v_prec_246_);
lean_dec(v_prec_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_instToString___private__1(lean_object* v_x_259_){
_start:
{
lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v_lowerBound_266_; 
v_lowerBound_266_ = lean_ctor_get(v_x_259_, 0);
if (lean_obj_tag(v_lowerBound_266_) == 0)
{
lean_object* v_upperBound_267_; 
v_upperBound_267_ = lean_ctor_get(v_x_259_, 1);
if (lean_obj_tag(v_upperBound_267_) == 0)
{
lean_object* v___x_268_; 
v___x_268_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__1));
return v___x_268_;
}
else
{
lean_object* v_val_269_; lean_object* v___x_270_; lean_object* v___y_272_; lean_object* v_intZero_276_; uint8_t v_isNeg_277_; 
v_val_269_ = lean_ctor_get(v_upperBound_267_, 0);
v___x_270_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__2));
v_intZero_276_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_277_ = lean_int_dec_lt(v_val_269_, v_intZero_276_);
if (v_isNeg_277_ == 0)
{
lean_object* v_a_278_; lean_object* v___x_279_; 
v_a_278_ = lean_nat_abs(v_val_269_);
v___x_279_ = l_Nat_reprFast(v_a_278_);
v___y_272_ = v___x_279_;
goto v___jp_271_;
}
else
{
lean_object* v_abs_280_; lean_object* v_one_281_; lean_object* v_a_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_abs_280_ = lean_nat_abs(v_val_269_);
v_one_281_ = lean_unsigned_to_nat(1u);
v_a_282_ = lean_nat_sub(v_abs_280_, v_one_281_);
lean_dec(v_abs_280_);
v___x_283_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_284_ = lean_nat_add(v_a_282_, v_one_281_);
lean_dec(v_a_282_);
v___x_285_ = l_Nat_reprFast(v___x_284_);
v___x_286_ = lean_string_append(v___x_283_, v___x_285_);
lean_dec_ref(v___x_285_);
v___y_272_ = v___x_286_;
goto v___jp_271_;
}
v___jp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_string_append(v___x_270_, v___y_272_);
lean_dec_ref(v___y_272_);
v___x_274_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__0));
v___x_275_ = lean_string_append(v___x_273_, v___x_274_);
return v___x_275_;
}
}
}
else
{
lean_object* v_upperBound_287_; 
v_upperBound_287_ = lean_ctor_get(v_x_259_, 1);
if (lean_obj_tag(v_upperBound_287_) == 0)
{
lean_object* v_val_288_; lean_object* v___x_289_; lean_object* v___y_291_; lean_object* v_intZero_295_; uint8_t v_isNeg_296_; 
v_val_288_ = lean_ctor_get(v_lowerBound_266_, 0);
v___x_289_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__3));
v_intZero_295_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_296_ = lean_int_dec_lt(v_val_288_, v_intZero_295_);
if (v_isNeg_296_ == 0)
{
lean_object* v_a_297_; lean_object* v___x_298_; 
v_a_297_ = lean_nat_abs(v_val_288_);
v___x_298_ = l_Nat_reprFast(v_a_297_);
v___y_291_ = v___x_298_;
goto v___jp_290_;
}
else
{
lean_object* v_abs_299_; lean_object* v_one_300_; lean_object* v_a_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_abs_299_ = lean_nat_abs(v_val_288_);
v_one_300_ = lean_unsigned_to_nat(1u);
v_a_301_ = lean_nat_sub(v_abs_299_, v_one_300_);
lean_dec(v_abs_299_);
v___x_302_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_303_ = lean_nat_add(v_a_301_, v_one_300_);
lean_dec(v_a_301_);
v___x_304_ = l_Nat_reprFast(v___x_303_);
v___x_305_ = lean_string_append(v___x_302_, v___x_304_);
lean_dec_ref(v___x_304_);
v___y_291_ = v___x_305_;
goto v___jp_290_;
}
v___jp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_string_append(v___x_289_, v___y_291_);
lean_dec_ref(v___y_291_);
v___x_293_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__4));
v___x_294_ = lean_string_append(v___x_292_, v___x_293_);
return v___x_294_;
}
}
else
{
lean_object* v_val_306_; lean_object* v_val_307_; uint8_t v___x_308_; 
v_val_306_ = lean_ctor_get(v_lowerBound_266_, 0);
v_val_307_ = lean_ctor_get(v_upperBound_287_, 0);
v___x_308_ = lean_int_dec_lt(v_val_307_, v_val_306_);
if (v___x_308_ == 0)
{
uint8_t v___x_309_; 
v___x_309_ = lean_int_dec_eq(v_val_306_, v_val_307_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___y_312_; lean_object* v_intZero_327_; uint8_t v_isNeg_328_; 
v___x_310_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__3));
v_intZero_327_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_328_ = lean_int_dec_lt(v_val_306_, v_intZero_327_);
if (v_isNeg_328_ == 0)
{
lean_object* v_a_329_; lean_object* v___x_330_; 
v_a_329_ = lean_nat_abs(v_val_306_);
v___x_330_ = l_Nat_reprFast(v_a_329_);
v___y_312_ = v___x_330_;
goto v___jp_311_;
}
else
{
lean_object* v_abs_331_; lean_object* v_one_332_; lean_object* v_a_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_abs_331_ = lean_nat_abs(v_val_306_);
v_one_332_ = lean_unsigned_to_nat(1u);
v_a_333_ = lean_nat_sub(v_abs_331_, v_one_332_);
lean_dec(v_abs_331_);
v___x_334_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_335_ = lean_nat_add(v_a_333_, v_one_332_);
lean_dec(v_a_333_);
v___x_336_ = l_Nat_reprFast(v___x_335_);
v___x_337_ = lean_string_append(v___x_334_, v___x_336_);
lean_dec_ref(v___x_336_);
v___y_312_ = v___x_337_;
goto v___jp_311_;
}
v___jp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v_intZero_316_; uint8_t v_isNeg_317_; 
v___x_313_ = lean_string_append(v___x_310_, v___y_312_);
lean_dec_ref(v___y_312_);
v___x_314_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__5));
v___x_315_ = lean_string_append(v___x_313_, v___x_314_);
v_intZero_316_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_317_ = lean_int_dec_lt(v_val_307_, v_intZero_316_);
if (v_isNeg_317_ == 0)
{
lean_object* v_a_318_; lean_object* v___x_319_; 
v_a_318_ = lean_nat_abs(v_val_307_);
v___x_319_ = l_Nat_reprFast(v_a_318_);
v___y_261_ = v___x_315_;
v___y_262_ = v___x_319_;
goto v___jp_260_;
}
else
{
lean_object* v_abs_320_; lean_object* v_one_321_; lean_object* v_a_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_abs_320_ = lean_nat_abs(v_val_307_);
v_one_321_ = lean_unsigned_to_nat(1u);
v_a_322_ = lean_nat_sub(v_abs_320_, v_one_321_);
lean_dec(v_abs_320_);
v___x_323_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_324_ = lean_nat_add(v_a_322_, v_one_321_);
lean_dec(v_a_322_);
v___x_325_ = l_Nat_reprFast(v___x_324_);
v___x_326_ = lean_string_append(v___x_323_, v___x_325_);
lean_dec_ref(v___x_325_);
v___y_261_ = v___x_315_;
v___y_262_ = v___x_326_;
goto v___jp_260_;
}
}
}
else
{
lean_object* v___x_338_; lean_object* v___y_340_; lean_object* v_intZero_344_; uint8_t v_isNeg_345_; 
v___x_338_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__6));
v_intZero_344_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_345_ = lean_int_dec_lt(v_val_306_, v_intZero_344_);
if (v_isNeg_345_ == 0)
{
lean_object* v_a_346_; lean_object* v___x_347_; 
v_a_346_ = lean_nat_abs(v_val_306_);
v___x_347_ = l_Nat_reprFast(v_a_346_);
v___y_340_ = v___x_347_;
goto v___jp_339_;
}
else
{
lean_object* v_abs_348_; lean_object* v_one_349_; lean_object* v_a_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_abs_348_ = lean_nat_abs(v_val_306_);
v_one_349_ = lean_unsigned_to_nat(1u);
v_a_350_ = lean_nat_sub(v_abs_348_, v_one_349_);
lean_dec(v_abs_348_);
v___x_351_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_352_ = lean_nat_add(v_a_350_, v_one_349_);
lean_dec(v_a_350_);
v___x_353_ = l_Nat_reprFast(v___x_352_);
v___x_354_ = lean_string_append(v___x_351_, v___x_353_);
lean_dec_ref(v___x_353_);
v___y_340_ = v___x_354_;
goto v___jp_339_;
}
v___jp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_string_append(v___x_338_, v___y_340_);
lean_dec_ref(v___y_340_);
v___x_342_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__7));
v___x_343_ = lean_string_append(v___x_341_, v___x_342_);
return v___x_343_;
}
}
}
else
{
lean_object* v___x_355_; 
v___x_355_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__8));
return v___x_355_;
}
}
}
v___jp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_string_append(v___y_261_, v___y_262_);
lean_dec_ref(v___y_262_);
v___x_264_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__0));
v___x_265_ = lean_string_append(v___x_263_, v___x_264_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_instToString___private__1___boxed(lean_object* v_x_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Omega_Constraint_instToString___private__1(v_x_356_);
lean_dec_ref(v_x_356_);
return v_res_357_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_sat(lean_object* v_c_360_, lean_object* v_t_361_){
_start:
{
lean_object* v_lowerBound_362_; lean_object* v_upperBound_363_; uint8_t v___y_365_; 
v_lowerBound_362_ = lean_ctor_get(v_c_360_, 0);
v_upperBound_363_ = lean_ctor_get(v_c_360_, 1);
if (lean_obj_tag(v_lowerBound_362_) == 0)
{
uint8_t v___x_368_; 
v___x_368_ = 1;
v___y_365_ = v___x_368_;
goto v___jp_364_;
}
else
{
lean_object* v_val_369_; uint8_t v___x_370_; 
v_val_369_ = lean_ctor_get(v_lowerBound_362_, 0);
v___x_370_ = lean_int_dec_le(v_val_369_, v_t_361_);
if (v___x_370_ == 0)
{
return v___x_370_;
}
else
{
v___y_365_ = v___x_370_;
goto v___jp_364_;
}
}
v___jp_364_:
{
if (lean_obj_tag(v_upperBound_363_) == 0)
{
return v___y_365_;
}
else
{
lean_object* v_val_366_; uint8_t v___x_367_; 
v_val_366_ = lean_ctor_get(v_upperBound_363_, 0);
v___x_367_ = lean_int_dec_le(v_t_361_, v_val_366_);
if (v___x_367_ == 0)
{
return v___x_367_;
}
else
{
return v___y_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_sat___boxed(lean_object* v_c_371_, lean_object* v_t_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Lean_Omega_Constraint_sat(v_c_371_, v_t_372_);
lean_dec(v_t_372_);
lean_dec_ref(v_c_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_map(lean_object* v_c_375_, lean_object* v_f_376_){
_start:
{
lean_object* v_lowerBound_377_; lean_object* v_upperBound_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_408_; 
v_lowerBound_377_ = lean_ctor_get(v_c_375_, 0);
v_upperBound_378_ = lean_ctor_get(v_c_375_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v_c_375_);
if (v_isSharedCheck_408_ == 0)
{
v___x_380_ = v_c_375_;
v_isShared_381_ = v_isSharedCheck_408_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_upperBound_378_);
lean_inc(v_lowerBound_377_);
lean_dec(v_c_375_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_408_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___y_383_; 
if (lean_obj_tag(v_lowerBound_377_) == 0)
{
v___y_383_ = v_lowerBound_377_;
goto v___jp_382_;
}
else
{
lean_object* v_val_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_407_; 
v_val_399_ = lean_ctor_get(v_lowerBound_377_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_lowerBound_377_);
if (v_isSharedCheck_407_ == 0)
{
v___x_401_ = v_lowerBound_377_;
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_val_399_);
lean_dec(v_lowerBound_377_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
lean_inc_ref(v_f_376_);
v___x_403_ = lean_apply_1(v_f_376_, v_val_399_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_403_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
v___y_383_ = v___x_405_;
goto v___jp_382_;
}
}
}
v___jp_382_:
{
if (lean_obj_tag(v_upperBound_378_) == 0)
{
lean_object* v___x_385_; 
lean_dec_ref(v_f_376_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___y_383_);
v___x_385_ = v___x_380_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___y_383_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_upperBound_378_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_object* v_val_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_398_; 
v_val_387_ = lean_ctor_get(v_upperBound_378_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_upperBound_378_);
if (v_isSharedCheck_398_ == 0)
{
v___x_389_ = v_upperBound_378_;
v_isShared_390_ = v_isSharedCheck_398_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_val_387_);
lean_dec(v_upperBound_378_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_398_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = lean_apply_1(v_f_376_, v_val_387_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_391_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_397_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v___x_393_);
lean_ctor_set(v___x_380_, 0, v___y_383_);
v___x_395_ = v___x_380_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___y_383_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate___lam__0(lean_object* v_t_409_, lean_object* v_x_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_int_add(v_x_410_, v_t_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate___lam__0___boxed(lean_object* v_t_412_, lean_object* v_x_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Omega_Constraint_translate___lam__0(v_t_412_, v_x_413_);
lean_dec(v_x_413_);
lean_dec(v_t_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate(lean_object* v_c_415_, lean_object* v_t_416_){
_start:
{
lean_object* v___f_417_; lean_object* v___x_418_; 
v___f_417_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_translate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_417_, 0, v_t_416_);
v___x_418_ = l_Lean_Omega_Constraint_map(v_c_415_, v___f_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_flip(lean_object* v_c_419_){
_start:
{
lean_object* v_lowerBound_420_; lean_object* v_upperBound_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_lowerBound_420_ = lean_ctor_get(v_c_419_, 0);
v_upperBound_421_ = lean_ctor_get(v_c_419_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_c_419_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v_c_419_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_upperBound_421_);
lean_inc(v_lowerBound_420_);
lean_dec(v_c_419_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_lowerBound_420_);
lean_ctor_set(v___x_423_, 0, v_upperBound_421_);
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_upperBound_421_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_lowerBound_420_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_neg(lean_object* v_c_430_){
_start:
{
lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___f_431_ = ((lean_object*)(l_Lean_Omega_Constraint_neg___closed__0));
v___x_432_ = l_Lean_Omega_Constraint_flip(v_c_430_);
v___x_433_ = l_Lean_Omega_Constraint_map(v___x_432_, v___f_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__0(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_to_int(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__1(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__0, &l_Lean_Omega_Constraint_impossible___closed__0_once, _init_l_Lean_Omega_Constraint_impossible___closed__0);
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__2(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__3(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__2, &l_Lean_Omega_Constraint_impossible___closed__2_once, _init_l_Lean_Omega_Constraint_impossible___closed__2);
v___x_444_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__1, &l_Lean_Omega_Constraint_impossible___closed__1_once, _init_l_Lean_Omega_Constraint_impossible___closed__1);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible(void){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__3, &l_Lean_Omega_Constraint_impossible___closed__3_once, _init_l_Lean_Omega_Constraint_impossible___closed__3);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_exact(lean_object* v_r_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_r_447_);
lean_inc_ref(v___x_448_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_isImpossible(lean_object* v_x_450_){
_start:
{
lean_object* v_lowerBound_451_; 
v_lowerBound_451_ = lean_ctor_get(v_x_450_, 0);
if (lean_obj_tag(v_lowerBound_451_) == 1)
{
lean_object* v_upperBound_452_; 
v_upperBound_452_ = lean_ctor_get(v_x_450_, 1);
if (lean_obj_tag(v_upperBound_452_) == 1)
{
lean_object* v_val_453_; lean_object* v_val_454_; uint8_t v___x_455_; 
v_val_453_ = lean_ctor_get(v_lowerBound_451_, 0);
v_val_454_ = lean_ctor_get(v_upperBound_452_, 0);
v___x_455_ = lean_int_dec_lt(v_val_454_, v_val_453_);
return v___x_455_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
}
else
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_isImpossible___boxed(lean_object* v_x_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_Lean_Omega_Constraint_isImpossible(v_x_458_);
lean_dec_ref(v_x_458_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_isExact(lean_object* v_x_461_){
_start:
{
lean_object* v_lowerBound_462_; 
v_lowerBound_462_ = lean_ctor_get(v_x_461_, 0);
if (lean_obj_tag(v_lowerBound_462_) == 1)
{
lean_object* v_upperBound_463_; 
v_upperBound_463_ = lean_ctor_get(v_x_461_, 1);
if (lean_obj_tag(v_upperBound_463_) == 1)
{
lean_object* v_val_464_; lean_object* v_val_465_; uint8_t v___x_466_; 
v_val_464_ = lean_ctor_get(v_lowerBound_462_, 0);
v_val_465_ = lean_ctor_get(v_upperBound_463_, 0);
v___x_466_ = lean_int_dec_eq(v_val_464_, v_val_465_);
return v___x_466_;
}
else
{
uint8_t v___x_467_; 
v___x_467_ = 0;
return v___x_467_;
}
}
else
{
uint8_t v___x_468_; 
v___x_468_ = 0;
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_isExact___boxed(lean_object* v_x_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Lean_Omega_Constraint_isExact(v_x_469_);
lean_dec_ref(v_x_469_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter___redArg(lean_object* v_x_472_, lean_object* v_h__1_473_, lean_object* v_h__2_474_){
_start:
{
lean_object* v_lowerBound_475_; 
v_lowerBound_475_ = lean_ctor_get(v_x_472_, 0);
if (lean_obj_tag(v_lowerBound_475_) == 1)
{
lean_object* v_upperBound_476_; 
v_upperBound_476_ = lean_ctor_get(v_x_472_, 1);
if (lean_obj_tag(v_upperBound_476_) == 1)
{
lean_object* v_val_477_; lean_object* v_val_478_; lean_object* v___x_479_; 
lean_inc_ref(v_upperBound_476_);
lean_inc_ref(v_lowerBound_475_);
lean_dec(v_h__2_474_);
lean_dec_ref(v_x_472_);
v_val_477_ = lean_ctor_get(v_lowerBound_475_, 0);
lean_inc(v_val_477_);
lean_dec_ref(v_lowerBound_475_);
v_val_478_ = lean_ctor_get(v_upperBound_476_, 0);
lean_inc(v_val_478_);
lean_dec_ref(v_upperBound_476_);
v___x_479_ = lean_apply_2(v_h__1_473_, v_val_477_, v_val_478_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; 
lean_dec(v_h__1_473_);
v___x_480_ = lean_apply_2(v_h__2_474_, v_x_472_, lean_box(0));
return v___x_480_;
}
}
else
{
lean_object* v___x_481_; 
lean_dec(v_h__1_473_);
v___x_481_ = lean_apply_2(v_h__2_474_, v_x_472_, lean_box(0));
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter(lean_object* v_motive_482_, lean_object* v_x_483_, lean_object* v_h__1_484_, lean_object* v_h__2_485_){
_start:
{
lean_object* v_lowerBound_486_; 
v_lowerBound_486_ = lean_ctor_get(v_x_483_, 0);
if (lean_obj_tag(v_lowerBound_486_) == 1)
{
lean_object* v_upperBound_487_; 
v_upperBound_487_ = lean_ctor_get(v_x_483_, 1);
if (lean_obj_tag(v_upperBound_487_) == 1)
{
lean_object* v_val_488_; lean_object* v_val_489_; lean_object* v___x_490_; 
lean_inc_ref(v_upperBound_487_);
lean_inc_ref(v_lowerBound_486_);
lean_dec(v_h__2_485_);
lean_dec_ref(v_x_483_);
v_val_488_ = lean_ctor_get(v_lowerBound_486_, 0);
lean_inc(v_val_488_);
lean_dec_ref(v_lowerBound_486_);
v_val_489_ = lean_ctor_get(v_upperBound_487_, 0);
lean_inc(v_val_489_);
lean_dec_ref(v_upperBound_487_);
v___x_490_ = lean_apply_2(v_h__1_484_, v_val_488_, v_val_489_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; 
lean_dec(v_h__1_484_);
v___x_491_ = lean_apply_2(v_h__2_485_, v_x_483_, lean_box(0));
return v___x_491_;
}
}
else
{
lean_object* v___x_492_; 
lean_dec(v_h__1_484_);
v___x_492_ = lean_apply_2(v_h__2_485_, v_x_483_, lean_box(0));
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale___lam__0(lean_object* v_k_493_, lean_object* v_x_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_int_mul(v_k_493_, v_x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale___lam__0___boxed(lean_object* v_k_496_, lean_object* v_x_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Omega_Constraint_scale___lam__0(v_k_496_, v_x_497_);
lean_dec(v_x_497_);
lean_dec(v_k_496_);
return v_res_498_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_scale___closed__0(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__2, &l_Lean_Omega_Constraint_impossible___closed__2_once, _init_l_Lean_Omega_Constraint_impossible___closed__2);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale(lean_object* v_k_501_, lean_object* v_c_502_){
_start:
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_504_ = lean_int_dec_eq(v_k_501_, v___x_503_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
v___x_505_ = lean_int_dec_lt(v___x_503_, v_k_501_);
if (v___x_505_ == 0)
{
lean_object* v___f_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___f_506_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_scale___lam__0___boxed), 2, 1);
lean_closure_set(v___f_506_, 0, v_k_501_);
v___x_507_ = l_Lean_Omega_Constraint_flip(v_c_502_);
v___x_508_ = l_Lean_Omega_Constraint_map(v___x_507_, v___f_506_);
return v___x_508_;
}
else
{
lean_object* v___f_509_; lean_object* v___x_510_; 
v___f_509_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_scale___lam__0___boxed), 2, 1);
lean_closure_set(v___f_509_, 0, v_k_501_);
v___x_510_ = l_Lean_Omega_Constraint_map(v_c_502_, v___f_509_);
return v___x_510_;
}
}
else
{
uint8_t v___x_511_; 
lean_dec(v_k_501_);
v___x_511_ = l_Lean_Omega_Constraint_isImpossible(v_c_502_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
lean_dec_ref(v_c_502_);
v___x_512_ = lean_obj_once(&l_Lean_Omega_Constraint_scale___closed__0, &l_Lean_Omega_Constraint_scale___closed__0_once, _init_l_Lean_Omega_Constraint_scale___closed__0);
return v___x_512_;
}
else
{
return v_c_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_add(lean_object* v_x_513_, lean_object* v_y_514_){
_start:
{
lean_object* v_lowerBound_515_; lean_object* v_upperBound_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_558_; 
v_lowerBound_515_ = lean_ctor_get(v_x_513_, 0);
v_upperBound_516_ = lean_ctor_get(v_x_513_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_x_513_);
if (v_isSharedCheck_558_ == 0)
{
v___x_518_ = v_x_513_;
v_isShared_519_ = v_isSharedCheck_558_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_upperBound_516_);
lean_inc(v_lowerBound_515_);
lean_dec(v_x_513_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_558_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___y_521_; 
if (lean_obj_tag(v_lowerBound_515_) == 0)
{
v___y_521_ = v_lowerBound_515_;
goto v___jp_520_;
}
else
{
lean_object* v_lowerBound_547_; 
v_lowerBound_547_ = lean_ctor_get(v_y_514_, 0);
lean_inc(v_lowerBound_547_);
if (lean_obj_tag(v_lowerBound_547_) == 0)
{
lean_dec_ref(v_lowerBound_515_);
v___y_521_ = v_lowerBound_547_;
goto v___jp_520_;
}
else
{
lean_object* v_val_548_; lean_object* v_val_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_557_; 
v_val_548_ = lean_ctor_get(v_lowerBound_515_, 0);
lean_inc(v_val_548_);
lean_dec_ref(v_lowerBound_515_);
v_val_549_ = lean_ctor_get(v_lowerBound_547_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v_lowerBound_547_);
if (v_isSharedCheck_557_ == 0)
{
v___x_551_ = v_lowerBound_547_;
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_val_549_);
lean_dec(v_lowerBound_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_int_add(v_val_548_, v_val_549_);
lean_dec(v_val_549_);
lean_dec(v_val_548_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
v___y_521_ = v___x_555_;
goto v___jp_520_;
}
}
}
}
v___jp_520_:
{
if (lean_obj_tag(v_upperBound_516_) == 0)
{
lean_object* v___x_523_; 
lean_dec_ref(v_y_514_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___y_521_);
v___x_523_ = v___x_518_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___y_521_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_upperBound_516_);
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
lean_object* v_upperBound_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_545_; 
lean_del_object(v___x_518_);
v_upperBound_525_ = lean_ctor_get(v_y_514_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_y_514_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v_y_514_, 0);
lean_dec(v_unused_546_);
v___x_527_ = v_y_514_;
v_isShared_528_ = v_isSharedCheck_545_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_upperBound_525_);
lean_dec(v_y_514_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_545_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
if (lean_obj_tag(v_upperBound_525_) == 0)
{
lean_object* v___x_530_; 
lean_dec_ref(v_upperBound_516_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___y_521_);
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___y_521_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_upperBound_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
else
{
lean_object* v_val_532_; lean_object* v_val_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_544_; 
v_val_532_ = lean_ctor_get(v_upperBound_516_, 0);
lean_inc(v_val_532_);
lean_dec_ref(v_upperBound_516_);
v_val_533_ = lean_ctor_get(v_upperBound_525_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_upperBound_525_);
if (v_isSharedCheck_544_ == 0)
{
v___x_535_ = v_upperBound_525_;
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_val_533_);
lean_dec(v_upperBound_525_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_int_add(v_val_532_, v_val_533_);
lean_dec(v_val_533_);
lean_dec(v_val_532_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_537_);
v___x_539_ = v___x_535_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_543_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v___x_539_);
lean_ctor_set(v___x_527_, 0, v___y_521_);
v___x_541_ = v___x_527_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___y_521_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_539_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combo(lean_object* v_a_559_, lean_object* v_x_560_, lean_object* v_b_561_, lean_object* v_y_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = l_Lean_Omega_Constraint_scale(v_a_559_, v_x_560_);
v___x_564_ = l_Lean_Omega_Constraint_scale(v_b_561_, v_y_562_);
v___x_565_ = l_Lean_Omega_Constraint_add(v___x_563_, v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__0(lean_object* v_x_566_, lean_object* v_y_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = lean_int_dec_le(v_x_566_, v_y_567_);
if (v___x_568_ == 0)
{
lean_inc(v_x_566_);
return v_x_566_;
}
else
{
lean_inc(v_y_567_);
return v_y_567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__0___boxed(lean_object* v_x_569_, lean_object* v_y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Omega_Constraint_combine___lam__0(v_x_569_, v_y_570_);
lean_dec(v_y_570_);
lean_dec(v_x_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__1(lean_object* v_x_572_, lean_object* v_y_573_){
_start:
{
uint8_t v___x_574_; 
v___x_574_ = lean_int_dec_le(v_x_572_, v_y_573_);
if (v___x_574_ == 0)
{
lean_inc(v_y_573_);
return v_y_573_;
}
else
{
lean_inc(v_x_572_);
return v_x_572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__1___boxed(lean_object* v_x_575_, lean_object* v_y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Omega_Constraint_combine___lam__1(v_x_575_, v_y_576_);
lean_dec(v_y_576_);
lean_dec(v_x_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine(lean_object* v_x_580_, lean_object* v_y_581_){
_start:
{
lean_object* v_lowerBound_582_; lean_object* v_upperBound_583_; lean_object* v_lowerBound_584_; lean_object* v_upperBound_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_596_; 
v_lowerBound_582_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_lowerBound_582_);
v_upperBound_583_ = lean_ctor_get(v_x_580_, 1);
lean_inc(v_upperBound_583_);
lean_dec_ref(v_x_580_);
v_lowerBound_584_ = lean_ctor_get(v_y_581_, 0);
v_upperBound_585_ = lean_ctor_get(v_y_581_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_y_581_);
if (v_isSharedCheck_596_ == 0)
{
v___x_587_ = v_y_581_;
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_upperBound_585_);
lean_inc(v_lowerBound_584_);
lean_dec(v_y_581_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___f_589_ = ((lean_object*)(l_Lean_Omega_Constraint_combine___closed__0));
v___f_590_ = ((lean_object*)(l_Lean_Omega_Constraint_combine___closed__1));
v___x_591_ = l_Option_merge___redArg(v___f_589_, v_lowerBound_582_, v_lowerBound_584_);
v___x_592_ = l_Option_merge___redArg(v___f_590_, v_upperBound_583_, v_upperBound_585_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_592_);
lean_ctor_set(v___x_587_, 0, v___x_591_);
v___x_594_ = v___x_587_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Option_merge_match__1_splitter___redArg(lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_h__1_599_, lean_object* v_h__2_600_, lean_object* v_h__3_601_, lean_object* v_h__4_602_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_dec(v_h__4_602_);
lean_dec(v_h__2_600_);
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v_h__3_601_);
v___x_603_ = lean_box(0);
v___x_604_ = lean_apply_1(v_h__1_599_, v___x_603_);
return v___x_604_;
}
else
{
lean_object* v_val_605_; lean_object* v___x_606_; 
lean_dec(v_h__1_599_);
v_val_605_ = lean_ctor_get(v_x_598_, 0);
lean_inc(v_val_605_);
lean_dec_ref(v_x_598_);
v___x_606_ = lean_apply_1(v_h__3_601_, v_val_605_);
return v___x_606_;
}
}
else
{
lean_dec(v_h__3_601_);
lean_dec(v_h__1_599_);
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v_val_607_; lean_object* v___x_608_; 
lean_dec(v_h__4_602_);
v_val_607_ = lean_ctor_get(v_x_597_, 0);
lean_inc(v_val_607_);
lean_dec_ref(v_x_597_);
v___x_608_ = lean_apply_1(v_h__2_600_, v_val_607_);
return v___x_608_;
}
else
{
lean_object* v_val_609_; lean_object* v_val_610_; lean_object* v___x_611_; 
lean_dec(v_h__2_600_);
v_val_609_ = lean_ctor_get(v_x_597_, 0);
lean_inc(v_val_609_);
lean_dec_ref(v_x_597_);
v_val_610_ = lean_ctor_get(v_x_598_, 0);
lean_inc(v_val_610_);
lean_dec_ref(v_x_598_);
v___x_611_ = lean_apply_2(v_h__4_602_, v_val_609_, v_val_610_);
return v___x_611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Option_merge_match__1_splitter(lean_object* v_00_u03b1_612_, lean_object* v_motive_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_h__1_616_, lean_object* v_h__2_617_, lean_object* v_h__3_618_, lean_object* v_h__4_619_){
_start:
{
if (lean_obj_tag(v_x_614_) == 0)
{
lean_dec(v_h__4_619_);
lean_dec(v_h__2_617_);
if (lean_obj_tag(v_x_615_) == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_h__3_618_);
v___x_620_ = lean_box(0);
v___x_621_ = lean_apply_1(v_h__1_616_, v___x_620_);
return v___x_621_;
}
else
{
lean_object* v_val_622_; lean_object* v___x_623_; 
lean_dec(v_h__1_616_);
v_val_622_ = lean_ctor_get(v_x_615_, 0);
lean_inc(v_val_622_);
lean_dec_ref(v_x_615_);
v___x_623_ = lean_apply_1(v_h__3_618_, v_val_622_);
return v___x_623_;
}
}
else
{
lean_dec(v_h__3_618_);
lean_dec(v_h__1_616_);
if (lean_obj_tag(v_x_615_) == 0)
{
lean_object* v_val_624_; lean_object* v___x_625_; 
lean_dec(v_h__4_619_);
v_val_624_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_val_624_);
lean_dec_ref(v_x_614_);
v___x_625_ = lean_apply_1(v_h__2_617_, v_val_624_);
return v___x_625_;
}
else
{
lean_object* v_val_626_; lean_object* v_val_627_; lean_object* v___x_628_; 
lean_dec(v_h__2_617_);
v_val_626_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_val_626_);
lean_dec_ref(v_x_614_);
v_val_627_ = lean_ctor_get(v_x_615_, 0);
lean_inc(v_val_627_);
lean_dec_ref(v_x_615_);
v___x_628_ = lean_apply_2(v_h__4_619_, v_val_626_, v_val_627_);
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_div(lean_object* v_c_629_, lean_object* v_k_630_){
_start:
{
lean_object* v_lowerBound_631_; lean_object* v_upperBound_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_666_; 
v_lowerBound_631_ = lean_ctor_get(v_c_629_, 0);
v_upperBound_632_ = lean_ctor_get(v_c_629_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_c_629_);
if (v_isSharedCheck_666_ == 0)
{
v___x_634_ = v_c_629_;
v_isShared_635_ = v_isSharedCheck_666_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_upperBound_632_);
lean_inc(v_lowerBound_631_);
lean_dec(v_c_629_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_666_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___y_637_; 
if (lean_obj_tag(v_lowerBound_631_) == 0)
{
v___y_637_ = v_lowerBound_631_;
goto v___jp_636_;
}
else
{
lean_object* v_val_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_665_; 
v_val_654_ = lean_ctor_get(v_lowerBound_631_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_lowerBound_631_);
if (v_isSharedCheck_665_ == 0)
{
v___x_656_ = v_lowerBound_631_;
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_val_654_);
lean_dec(v_lowerBound_631_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_658_ = lean_int_neg(v_val_654_);
lean_dec(v_val_654_);
lean_inc(v_k_630_);
v___x_659_ = lean_nat_to_int(v_k_630_);
v___x_660_ = lean_int_ediv(v___x_658_, v___x_659_);
lean_dec(v___x_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_int_neg(v___x_660_);
lean_dec(v___x_660_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_661_);
v___x_663_ = v___x_656_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v___y_637_ = v___x_663_;
goto v___jp_636_;
}
}
}
v___jp_636_:
{
if (lean_obj_tag(v_upperBound_632_) == 0)
{
lean_object* v___x_639_; 
lean_dec(v_k_630_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___y_637_);
v___x_639_ = v___x_634_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___y_637_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_upperBound_632_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_653_; 
v_val_641_ = lean_ctor_get(v_upperBound_632_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_upperBound_632_);
if (v_isSharedCheck_653_ == 0)
{
v___x_643_ = v_upperBound_632_;
v_isShared_644_ = v_isSharedCheck_653_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_dec(v_upperBound_632_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_653_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_645_ = lean_nat_to_int(v_k_630_);
v___x_646_ = lean_int_ediv(v_val_641_, v___x_645_);
lean_dec(v___x_645_);
lean_dec(v_val_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_646_);
v___x_648_ = v___x_643_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_650_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_648_);
lean_ctor_set(v___x_634_, 0, v___y_637_);
v___x_650_ = v___x_634_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___y_637_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_sat_x27(lean_object* v_c_667_, lean_object* v_x_668_, lean_object* v_y_669_){
_start:
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = l_Lean_Omega_IntList_dot(v_x_668_, v_y_669_);
v___x_671_ = l_Lean_Omega_Constraint_sat(v_c_667_, v___x_670_);
lean_dec(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_sat_x27___boxed(lean_object* v_c_672_, lean_object* v_x_673_, lean_object* v_y_674_){
_start:
{
uint8_t v_res_675_; lean_object* v_r_676_; 
v_res_675_ = l_Lean_Omega_Constraint_sat_x27(v_c_672_, v_x_673_, v_y_674_);
lean_dec(v_x_673_);
lean_dec_ref(v_c_672_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_normalize_x3f(lean_object* v_x_677_){
_start:
{
lean_object* v_fst_678_; lean_object* v_snd_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_708_; 
v_fst_678_ = lean_ctor_get(v_x_677_, 0);
v_snd_679_ = lean_ctor_get(v_x_677_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_x_677_);
if (v_isSharedCheck_708_ == 0)
{
v___x_681_ = v_x_677_;
v_isShared_682_ = v_isSharedCheck_708_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snd_679_);
lean_inc(v_fst_678_);
lean_dec(v_x_677_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_708_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_gcd_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_gcd_683_ = l_Lean_Omega_IntList_gcd(v_snd_679_);
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = lean_nat_dec_eq(v_gcd_683_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_dec_eq(v_gcd_683_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
lean_inc(v_gcd_683_);
v___x_688_ = l_Lean_Omega_Constraint_div(v_fst_678_, v_gcd_683_);
v___x_689_ = lean_nat_to_int(v_gcd_683_);
v___x_690_ = l_Lean_Omega_IntList_sdiv(v_snd_679_, v___x_689_);
lean_dec(v___x_689_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_690_);
lean_ctor_set(v___x_681_, 0, v___x_688_);
v___x_692_ = v___x_681_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_690_);
v___x_692_ = v_reuseFailAlloc_694_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
else
{
lean_object* v___x_695_; 
lean_dec(v_gcd_683_);
lean_del_object(v___x_681_);
lean_dec(v_snd_679_);
lean_dec(v_fst_678_);
v___x_695_ = lean_box(0);
return v___x_695_;
}
}
else
{
lean_object* v___x_696_; uint8_t v___x_697_; 
lean_dec(v_gcd_683_);
v___x_696_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_697_ = l_Lean_Omega_Constraint_sat(v_fst_678_, v___x_696_);
lean_dec(v_fst_678_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = l_Lean_Omega_Constraint_impossible;
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_698_);
v___x_700_ = v___x_681_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_snd_679_);
v___x_700_ = v_reuseFailAlloc_702_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = ((lean_object*)(l_Lean_Omega_Constraint_trivial));
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_703_);
v___x_705_ = v___x_681_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_snd_679_);
v___x_705_ = v_reuseFailAlloc_707_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_normalize(lean_object* v_p_709_){
_start:
{
lean_object* v___x_710_; 
lean_inc_ref(v_p_709_);
v___x_710_ = l_Lean_Omega_normalize_x3f(v_p_709_);
if (lean_obj_tag(v___x_710_) == 0)
{
return v_p_709_;
}
else
{
lean_object* v_val_711_; 
lean_dec_ref(v_p_709_);
v_val_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_val_711_);
lean_dec_ref(v___x_710_);
return v_val_711_;
}
}
}
static lean_object* _init_l_Lean_Omega_positivize_x3f___closed__0(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__0, &l_Lean_Omega_Constraint_impossible___closed__0_once, _init_l_Lean_Omega_Constraint_impossible___closed__0);
v___x_713_ = lean_int_neg(v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_positivize_x3f(lean_object* v_x_714_){
_start:
{
lean_object* v_fst_715_; lean_object* v_snd_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_731_; 
v_fst_715_ = lean_ctor_get(v_x_714_, 0);
v_snd_716_ = lean_ctor_get(v_x_714_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_714_);
if (v_isSharedCheck_731_ == 0)
{
v___x_718_ = v_x_714_;
v_isShared_719_ = v_isSharedCheck_731_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_snd_716_);
lean_inc(v_fst_715_);
lean_dec(v_x_714_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_731_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_720_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
lean_inc(v_snd_716_);
v___x_721_ = l_Lean_Omega_IntList_leading(v_snd_716_);
v___x_722_ = lean_int_dec_le(v___x_720_, v___x_721_);
lean_dec(v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_723_ = l_Lean_Omega_Constraint_neg(v_fst_715_);
v___x_724_ = lean_obj_once(&l_Lean_Omega_positivize_x3f___closed__0, &l_Lean_Omega_positivize_x3f___closed__0_once, _init_l_Lean_Omega_positivize_x3f___closed__0);
v___x_725_ = l_Lean_Omega_IntList_smul(v_snd_716_, v___x_724_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_725_);
lean_ctor_set(v___x_718_, 0, v___x_723_);
v___x_727_ = v___x_718_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_725_);
v___x_727_ = v_reuseFailAlloc_729_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
else
{
lean_object* v___x_730_; 
lean_del_object(v___x_718_);
lean_dec(v_snd_716_);
lean_dec(v_fst_715_);
v___x_730_ = lean_box(0);
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidy_x3f(lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; 
lean_inc_ref(v_x_732_);
v___x_733_ = l_Lean_Omega_positivize_x3f(v_x_732_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Omega_normalize_x3f(v_x_732_);
return v___x_734_;
}
else
{
lean_object* v_val_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v_x_732_);
v_val_735_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_743_ == 0)
{
v___x_737_ = v___x_733_;
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_val_735_);
lean_dec(v___x_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = l_Lean_Omega_normalize(v_val_735_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidy(lean_object* v_p_744_){
_start:
{
lean_object* v___x_745_; 
lean_inc_ref(v_p_744_);
v___x_745_ = l_Lean_Omega_tidy_x3f(v_p_744_);
if (lean_obj_tag(v___x_745_) == 0)
{
return v_p_744_;
}
else
{
lean_object* v_val_746_; 
lean_dec_ref(v_p_744_);
v_val_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_746_);
lean_dec_ref(v___x_745_);
return v_val_746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidyConstraint(lean_object* v_s_747_, lean_object* v_x_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_fst_751_; 
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_s_747_);
lean_ctor_set(v___x_749_, 1, v_x_748_);
v___x_750_ = l_Lean_Omega_tidy(v___x_749_);
v_fst_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_fst_751_);
lean_dec_ref(v___x_750_);
return v_fst_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidyCoeffs(lean_object* v_s_752_, lean_object* v_x_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_snd_756_; 
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_s_752_);
lean_ctor_set(v___x_754_, 1, v_x_753_);
v___x_755_ = l_Lean_Omega_tidy(v___x_754_);
v_snd_756_ = lean_ctor_get(v___x_755_, 1);
lean_inc(v_snd_756_);
lean_dec_ref(v___x_755_);
return v_snd_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter___redArg(lean_object* v_x_757_, lean_object* v_h__1_758_, lean_object* v_h__2_759_){
_start:
{
if (lean_obj_tag(v_x_757_) == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec(v_h__2_759_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_apply_1(v_h__1_758_, v___x_760_);
return v___x_761_;
}
else
{
lean_object* v_val_762_; lean_object* v_fst_763_; lean_object* v_snd_764_; lean_object* v___x_765_; 
lean_dec(v_h__1_758_);
v_val_762_ = lean_ctor_get(v_x_757_, 0);
lean_inc(v_val_762_);
lean_dec_ref(v_x_757_);
v_fst_763_ = lean_ctor_get(v_val_762_, 0);
lean_inc(v_fst_763_);
v_snd_764_ = lean_ctor_get(v_val_762_, 1);
lean_inc(v_snd_764_);
lean_dec(v_val_762_);
v___x_765_ = lean_apply_2(v_h__2_759_, v_fst_763_, v_snd_764_);
return v___x_765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter(lean_object* v_motive_766_, lean_object* v_x_767_, lean_object* v_h__1_768_, lean_object* v_h__2_769_){
_start:
{
if (lean_obj_tag(v_x_767_) == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec(v_h__2_769_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_apply_1(v_h__1_768_, v___x_770_);
return v___x_771_;
}
else
{
lean_object* v_val_772_; lean_object* v_fst_773_; lean_object* v_snd_774_; lean_object* v___x_775_; 
lean_dec(v_h__1_768_);
v_val_772_ = lean_ctor_get(v_x_767_, 0);
lean_inc(v_val_772_);
lean_dec_ref(v_x_767_);
v_fst_773_ = lean_ctor_get(v_val_772_, 0);
lean_inc(v_fst_773_);
v_snd_774_ = lean_ctor_get(v_val_772_, 1);
lean_inc(v_snd_774_);
lean_dec(v_val_772_);
v___x_775_ = lean_apply_2(v_h__2_769_, v_fst_773_, v_snd_774_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term___lam__0(lean_object* v_m_776_, lean_object* v_x_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Int_bmod(v_x_777_, v_m_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term___lam__0___boxed(lean_object* v_m_779_, lean_object* v_x_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Omega_bmod__div__term___lam__0(v_m_779_, v_x_780_);
lean_dec(v_x_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term(lean_object* v_m_782_, lean_object* v_a_783_, lean_object* v_b_784_){
_start:
{
lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_inc(v_m_782_);
v___f_785_ = lean_alloc_closure((void*)(l_Lean_Omega_bmod__div__term___lam__0___boxed), 2, 1);
lean_closure_set(v___f_785_, 0, v_m_782_);
lean_inc(v_b_784_);
v___x_786_ = l_Lean_Omega_IntList_dot(v_a_783_, v_b_784_);
lean_inc(v_m_782_);
v___x_787_ = l_Int_bmod(v___x_786_, v_m_782_);
lean_dec(v___x_786_);
v___x_788_ = lean_box(0);
v___x_789_ = l_List_mapTR_loop___redArg(v___f_785_, v_a_783_, v___x_788_);
v___x_790_ = l_Lean_Omega_IntList_dot(v___x_789_, v_b_784_);
lean_dec(v___x_789_);
v___x_791_ = lean_int_sub(v___x_787_, v___x_790_);
lean_dec(v___x_790_);
lean_dec(v___x_787_);
v___x_792_ = lean_nat_to_int(v_m_782_);
v___x_793_ = lean_int_ediv(v___x_791_, v___x_792_);
lean_dec(v___x_792_);
lean_dec(v___x_791_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_bmod__coeffs_spec__0(lean_object* v_m_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
if (lean_obj_tag(v_a_795_) == 0)
{
lean_object* v___x_797_; 
lean_dec(v_m_794_);
v___x_797_ = l_List_reverse___redArg(v_a_796_);
return v___x_797_;
}
else
{
lean_object* v_head_798_; lean_object* v_tail_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_808_; 
v_head_798_ = lean_ctor_get(v_a_795_, 0);
v_tail_799_ = lean_ctor_get(v_a_795_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_a_795_);
if (v_isSharedCheck_808_ == 0)
{
v___x_801_ = v_a_795_;
v_isShared_802_ = v_isSharedCheck_808_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_tail_799_);
lean_inc(v_head_798_);
lean_dec(v_a_795_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_808_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
lean_inc(v_m_794_);
v___x_803_ = l_Int_bmod(v_head_798_, v_m_794_);
lean_dec(v_head_798_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v_a_796_);
lean_ctor_set(v___x_801_, 0, v___x_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_a_796_);
v___x_805_ = v_reuseFailAlloc_807_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
v_a_795_ = v_tail_799_;
v_a_796_ = v___x_805_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__coeffs(lean_object* v_m_809_, lean_object* v_i_810_, lean_object* v_x_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_812_ = lean_box(0);
lean_inc(v_m_809_);
v___x_813_ = l_List_mapTR_loop___at___00Lean_Omega_bmod__coeffs_spec__0(v_m_809_, v_x_811_, v___x_812_);
v___x_814_ = lean_nat_to_int(v_m_809_);
v___x_815_ = l_Lean_Omega_IntList_set(v___x_813_, v_i_810_, v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__coeffs___boxed(lean_object* v_m_816_, lean_object* v_i_817_, lean_object* v_x_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Omega_bmod__coeffs(v_m_816_, v_i_817_, v_x_818_);
lean_dec(v_i_817_);
return v_res_819_;
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
