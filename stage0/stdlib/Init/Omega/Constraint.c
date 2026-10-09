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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0___boxed(lean_object*, lean_object*);
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
uint8_t l_Lean_Omega_LowerBound_sat(lean_object* v_b_1_, lean_object* v_t_2_){
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
LEAN_EXPORT void l_Lean_Omega_LowerBound_sat_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_1_ = stack[0].m_obj;
lean_object* v_t_2_ = stack[1].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_Lean_Omega_LowerBound_sat(v_b_1_, v_t_2_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_Omega_LowerBound_sat___boxed(lean_object* v_b_7_, lean_object* v_t_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Lean_Omega_LowerBound_sat(v_b_7_, v_t_8_);
lean_dec(v_t_8_);
lean_dec(v_b_7_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
uint8_t l_Lean_Omega_UpperBound_sat(lean_object* v_b_11_, lean_object* v_t_12_){
_start:
{
if (lean_obj_tag(v_b_11_) == 0)
{
uint8_t v___x_13_; 
v___x_13_ = 1;
return v___x_13_;
}
else
{
lean_object* v_val_14_; uint8_t v___x_15_; 
v_val_14_ = lean_ctor_get(v_b_11_, 0);
v___x_15_ = lean_int_dec_le(v_t_12_, v_val_14_);
return v___x_15_;
}
}
}
LEAN_EXPORT void l_Lean_Omega_UpperBound_sat_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_11_ = stack[0].m_obj;
lean_object* v_t_12_ = stack[1].m_obj;
uint8_t v_res_16_;
v_res_16_ = l_Lean_Omega_UpperBound_sat(v_b_11_, v_t_12_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Omega_UpperBound_sat___boxed(lean_object* v_b_17_, lean_object* v_t_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Lean_Omega_UpperBound_sat(v_b_17_, v_t_18_);
lean_dec(v_t_18_);
lean_dec(v_b_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
static lean_object* _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0(void){
_start:
{
lean_object* v_natZero_23_; lean_object* v_intZero_24_; 
v_natZero_23_ = lean_unsigned_to_nat(0u);
v_intZero_24_ = lean_nat_to_int(v_natZero_23_);
return v_intZero_24_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0(lean_object* v_x_26_){
_start:
{
lean_object* v_intZero_27_; uint8_t v_isNeg_28_; 
v_intZero_27_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_28_ = lean_int_dec_lt(v_x_26_, v_intZero_27_);
if (v_isNeg_28_ == 0)
{
lean_object* v_a_29_; lean_object* v___x_30_; 
v_a_29_ = lean_nat_abs(v_x_26_);
v___x_30_ = l_Nat_reprFast(v_a_29_);
return v___x_30_;
}
else
{
lean_object* v_abs_31_; lean_object* v_one_32_; lean_object* v_a_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_abs_31_ = lean_nat_abs(v_x_26_);
v_one_32_ = lean_unsigned_to_nat(1u);
v_a_33_ = lean_nat_sub(v_abs_31_, v_one_32_);
lean_dec(v_abs_31_);
v___x_34_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_35_ = lean_nat_add(v_a_33_, v_one_32_);
lean_dec(v_a_33_);
v___x_36_ = l_Nat_reprFast(v___x_35_);
v___x_37_ = lean_string_append(v___x_34_, v___x_36_);
lean_dec_ref(v___x_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___boxed(lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0(v_x_38_);
lean_dec(v_x_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0(lean_object* v_i_42_, lean_object* v_prec_43_){
_start:
{
lean_object* v___y_45_; lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_49_ = lean_int_dec_lt(v_i_42_, v___x_48_);
if (v___x_49_ == 0)
{
if (v___x_49_ == 0)
{
lean_object* v_a_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_a_50_ = lean_nat_abs(v_i_42_);
v___x_51_ = l_Nat_reprFast(v_a_50_);
v___x_52_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
else
{
lean_object* v_abs_53_; lean_object* v_one_54_; lean_object* v_a_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_abs_53_ = lean_nat_abs(v_i_42_);
v_one_54_ = lean_unsigned_to_nat(1u);
v_a_55_ = lean_nat_sub(v_abs_53_, v_one_54_);
lean_dec(v_abs_53_);
v___x_56_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_57_ = lean_nat_add(v_a_55_, v_one_54_);
lean_dec(v_a_55_);
v___x_58_ = l_Nat_reprFast(v___x_57_);
v___x_59_ = lean_string_append(v___x_56_, v___x_58_);
lean_dec_ref(v___x_58_);
v___x_60_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
else
{
if (v___x_49_ == 0)
{
lean_object* v_a_61_; lean_object* v___x_62_; 
v_a_61_ = lean_nat_abs(v_i_42_);
v___x_62_ = l_Nat_reprFast(v_a_61_);
v___y_45_ = v___x_62_;
goto v___jp_44_;
}
else
{
lean_object* v_abs_63_; lean_object* v_one_64_; lean_object* v_a_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_abs_63_ = lean_nat_abs(v_i_42_);
v_one_64_ = lean_unsigned_to_nat(1u);
v_a_65_ = lean_nat_sub(v_abs_63_, v_one_64_);
lean_dec(v_abs_63_);
v___x_66_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_67_ = lean_nat_add(v_a_65_, v_one_64_);
lean_dec(v_a_65_);
v___x_68_ = l_Nat_reprFast(v___x_67_);
v___x_69_ = lean_string_append(v___x_66_, v___x_68_);
lean_dec_ref(v___x_68_);
v___y_45_ = v___x_69_;
goto v___jp_44_;
}
}
v___jp_44_:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_46_, 0, v___y_45_);
v___x_47_ = l_Repr_addAppParen(v___x_46_, v_prec_43_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0___boxed(lean_object* v_i_70_, lean_object* v_prec_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Init_Omega_Constraint_0__Lean_Omega_instReprInt___lam__0(v_i_70_, v_prec_71_);
lean_dec(v_prec_71_);
lean_dec(v_i_70_);
return v_res_72_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
if (lean_obj_tag(v_x_76_) == 0)
{
uint8_t v___x_77_; 
v___x_77_ = 1;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
else
{
if (lean_obj_tag(v_x_76_) == 0)
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
else
{
lean_object* v_val_80_; lean_object* v_val_81_; uint8_t v___x_82_; 
v_val_80_ = lean_ctor_get(v_x_75_, 0);
v_val_81_ = lean_ctor_get(v_x_76_, 0);
v___x_82_ = lean_int_dec_eq(v_val_80_, v_val_81_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_75_ = stack[0].m_obj;
lean_object* v_x_76_ = stack[1].m_obj;
uint8_t v_res_83_;
v_res_83_ = l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_x_75_, v_x_76_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0___boxed(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_x_84_, v_x_85_);
lean_dec(v_x_85_);
lean_dec(v_x_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
uint8_t l_Lean_Omega_instBEqConstraint_beq(lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
lean_object* v_lowerBound_90_; lean_object* v_upperBound_91_; lean_object* v_lowerBound_92_; lean_object* v_upperBound_93_; uint8_t v___x_94_; 
v_lowerBound_90_ = lean_ctor_get(v_x_88_, 0);
v_upperBound_91_ = lean_ctor_get(v_x_88_, 1);
v_lowerBound_92_ = lean_ctor_get(v_x_89_, 0);
v_upperBound_93_ = lean_ctor_get(v_x_89_, 1);
v___x_94_ = l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_lowerBound_90_, v_lowerBound_92_);
if (v___x_94_ == 0)
{
return v___x_94_;
}
else
{
uint8_t v___x_95_; 
v___x_95_ = l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_upperBound_91_, v_upperBound_93_);
return v___x_95_;
}
}
}
LEAN_EXPORT void l_Lean_Omega_instBEqConstraint_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_88_ = stack[0].m_obj;
lean_object* v_x_89_ = stack[1].m_obj;
uint8_t v_res_96_;
v_res_96_ = l_Lean_Omega_instBEqConstraint_beq(v_x_88_, v_x_89_);
stack->m_num = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_Omega_instBEqConstraint_beq___boxed(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Lean_Omega_instBEqConstraint_beq(v_x_97_, v_x_98_);
lean_dec_ref(v_x_98_);
lean_dec_ref(v_x_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
uint8_t l_Lean_Omega_instDecidableEqConstraint_decEq(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
lean_object* v_lowerBound_105_; lean_object* v_upperBound_106_; lean_object* v_lowerBound_107_; lean_object* v_upperBound_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v_lowerBound_105_ = lean_ctor_get(v_x_103_, 0);
lean_inc(v_lowerBound_105_);
v_upperBound_106_ = lean_ctor_get(v_x_103_, 1);
lean_inc(v_upperBound_106_);
lean_dec_ref(v_x_103_);
v_lowerBound_107_ = lean_ctor_get(v_x_104_, 0);
lean_inc(v_lowerBound_107_);
v_upperBound_108_ = lean_ctor_get(v_x_104_, 1);
lean_inc(v_upperBound_108_);
lean_dec_ref(v_x_104_);
v___x_109_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc_ref(v___x_109_);
v___x_110_ = l_Option_instDecidableEq___redArg(v___x_109_, v_lowerBound_105_, v_lowerBound_107_);
if (v___x_110_ == 0)
{
lean_dec_ref(v___x_109_);
lean_dec(v_upperBound_108_);
lean_dec(v_upperBound_106_);
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = l_Option_instDecidableEq___redArg(v___x_109_, v_upperBound_106_, v_upperBound_108_);
return v___x_111_;
}
}
}
LEAN_EXPORT void l_Lean_Omega_instDecidableEqConstraint_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_103_ = stack[0].m_obj;
lean_object* v_x_104_ = stack[1].m_obj;
uint8_t v_res_112_;
v_res_112_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_x_103_, v_x_104_);
stack->m_num = v_res_112_;
}
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqConstraint_decEq___boxed(lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_x_113_, v_x_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
uint8_t l_Lean_Omega_instDecidableEqConstraint(lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_x_117_, v_x_118_);
return v___x_119_;
}
}
LEAN_EXPORT void l_Lean_Omega_instDecidableEqConstraint_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_117_ = stack[0].m_obj;
lean_object* v_x_118_ = stack[1].m_obj;
uint8_t v_res_120_;
v_res_120_ = l_Lean_Omega_instDecidableEqConstraint(v_x_117_, v_x_118_);
stack->m_num = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqConstraint___boxed(lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lean_Omega_instDecidableEqConstraint(v_x_121_, v_x_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
lean_object* v___x_133_; 
v___x_133_ = ((lean_object*)(l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__1));
return v___x_133_;
}
else
{
lean_object* v_val_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_176_; 
v_val_134_ = lean_ctor_get(v_x_131_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_176_ == 0)
{
v___x_136_ = v_x_131_;
v_isShared_137_ = v_isSharedCheck_176_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_val_134_);
lean_dec(v_x_131_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_176_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___y_140_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_138_ = ((lean_object*)(l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___closed__3));
v___x_143_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_144_ = lean_int_dec_lt(v_val_134_, v___x_143_);
if (v___x_144_ == 0)
{
if (v___x_144_ == 0)
{
lean_object* v_a_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
v_a_145_ = lean_nat_abs(v_val_134_);
lean_dec(v_val_134_);
v___x_146_ = l_Nat_reprFast(v_a_145_);
if (v_isShared_137_ == 0)
{
lean_ctor_set_tag(v___x_136_, 3);
lean_ctor_set(v___x_136_, 0, v___x_146_);
v___x_148_ = v___x_136_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
v___y_140_ = v___x_148_;
goto v___jp_139_;
}
}
else
{
lean_object* v_abs_150_; lean_object* v_one_151_; lean_object* v_a_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v_abs_150_ = lean_nat_abs(v_val_134_);
lean_dec(v_val_134_);
v_one_151_ = lean_unsigned_to_nat(1u);
v_a_152_ = lean_nat_sub(v_abs_150_, v_one_151_);
lean_dec(v_abs_150_);
v___x_153_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_154_ = lean_nat_add(v_a_152_, v_one_151_);
lean_dec(v_a_152_);
v___x_155_ = l_Nat_reprFast(v___x_154_);
v___x_156_ = lean_string_append(v___x_153_, v___x_155_);
lean_dec_ref(v___x_155_);
if (v_isShared_137_ == 0)
{
lean_ctor_set_tag(v___x_136_, 3);
lean_ctor_set(v___x_136_, 0, v___x_156_);
v___x_158_ = v___x_136_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
v___y_140_ = v___x_158_;
goto v___jp_139_;
}
}
}
else
{
lean_object* v___x_160_; lean_object* v___y_162_; 
v___x_160_ = lean_unsigned_to_nat(1024u);
if (v___x_144_ == 0)
{
lean_object* v_a_167_; lean_object* v___x_168_; 
v_a_167_ = lean_nat_abs(v_val_134_);
lean_dec(v_val_134_);
v___x_168_ = l_Nat_reprFast(v_a_167_);
v___y_162_ = v___x_168_;
goto v___jp_161_;
}
else
{
lean_object* v_abs_169_; lean_object* v_one_170_; lean_object* v_a_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_abs_169_ = lean_nat_abs(v_val_134_);
lean_dec(v_val_134_);
v_one_170_ = lean_unsigned_to_nat(1u);
v_a_171_ = lean_nat_sub(v_abs_169_, v_one_170_);
lean_dec(v_abs_169_);
v___x_172_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_173_ = lean_nat_add(v_a_171_, v_one_170_);
lean_dec(v_a_171_);
v___x_174_ = l_Nat_reprFast(v___x_173_);
v___x_175_ = lean_string_append(v___x_172_, v___x_174_);
lean_dec_ref(v___x_174_);
v___y_162_ = v___x_175_;
goto v___jp_161_;
}
v___jp_161_:
{
lean_object* v___x_164_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set_tag(v___x_136_, 3);
lean_ctor_set(v___x_136_, 0, v___y_162_);
v___x_164_ = v___x_136_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___y_162_);
v___x_164_ = v_reuseFailAlloc_166_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; 
v___x_165_ = l_Repr_addAppParen(v___x_164_, v___x_160_);
v___y_140_ = v___x_165_;
goto v___jp_139_;
}
}
}
v___jp_139_:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_138_);
lean_ctor_set(v___x_141_, 1, v___y_140_);
v___x_142_ = l_Repr_addAppParen(v___x_141_, v_x_132_);
return v___x_142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0___boxed(lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(v_x_177_, v_x_178_);
lean_dec(v_x_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Omega_instReprConstraint_repr_spec__1(lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_nat_to_int(v_a_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_unsigned_to_nat(14u);
v___x_196_ = lean_nat_to_int(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__0));
v___x_205_ = lean_string_length(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Lean_Omega_instReprConstraint_repr___redArg___closed__13, &l_Lean_Omega_instReprConstraint_repr___redArg___closed__13_once, _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__13);
v___x_207_ = lean_nat_to_int(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr___redArg(lean_object* v_x_212_){
_start:
{
lean_object* v_lowerBound_213_; lean_object* v_upperBound_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_247_; 
v_lowerBound_213_ = lean_ctor_get(v_x_212_, 0);
v_upperBound_214_ = lean_ctor_get(v_x_212_, 1);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_212_);
if (v_isSharedCheck_247_ == 0)
{
v___x_216_ = v_x_212_;
v_isShared_217_ = v_isSharedCheck_247_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_upperBound_214_);
lean_inc(v_lowerBound_213_);
lean_dec(v_x_212_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_247_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_218_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__5));
v___x_219_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__6));
v___x_220_ = lean_obj_once(&l_Lean_Omega_instReprConstraint_repr___redArg___closed__7, &l_Lean_Omega_instReprConstraint_repr___redArg___closed__7_once, _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__7);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(v_lowerBound_213_, v___x_221_);
if (v_isShared_217_ == 0)
{
lean_ctor_set_tag(v___x_216_, 4);
lean_ctor_set(v___x_216_, 1, v___x_222_);
lean_ctor_set(v___x_216_, 0, v___x_220_);
v___x_224_ = v___x_216_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_246_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_225_ = 0;
v___x_226_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v___x_225_);
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_219_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__9));
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_box(1);
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__11));
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_218_);
v___x_235_ = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(v_upperBound_214_, v___x_221_);
v___x_236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_220_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_225_);
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_234_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_obj_once(&l_Lean_Omega_instReprConstraint_repr___redArg___closed__14, &l_Lean_Omega_instReprConstraint_repr___redArg___closed__14_once, _init_l_Lean_Omega_instReprConstraint_repr___redArg___closed__14);
v___x_240_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__15));
v___x_241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_238_);
v___x_242_ = ((lean_object*)(l_Lean_Omega_instReprConstraint_repr___redArg___closed__16));
v___x_243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_239_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_225_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr(lean_object* v_x_248_, lean_object* v_prec_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Omega_instReprConstraint_repr___redArg(v_x_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprConstraint_repr___boxed(lean_object* v_x_251_, lean_object* v_prec_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Omega_instReprConstraint_repr(v_x_251_, v_prec_252_);
lean_dec(v_prec_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_instToString___private__1(lean_object* v_x_265_){
_start:
{
lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v_lowerBound_272_; 
v_lowerBound_272_ = lean_ctor_get(v_x_265_, 0);
if (lean_obj_tag(v_lowerBound_272_) == 0)
{
lean_object* v_upperBound_273_; 
v_upperBound_273_ = lean_ctor_get(v_x_265_, 1);
if (lean_obj_tag(v_upperBound_273_) == 0)
{
lean_object* v___x_274_; 
v___x_274_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__1));
return v___x_274_;
}
else
{
lean_object* v_val_275_; lean_object* v___x_276_; lean_object* v___y_278_; lean_object* v_intZero_282_; uint8_t v_isNeg_283_; 
v_val_275_ = lean_ctor_get(v_upperBound_273_, 0);
v___x_276_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__2));
v_intZero_282_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_283_ = lean_int_dec_lt(v_val_275_, v_intZero_282_);
if (v_isNeg_283_ == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; 
v_a_284_ = lean_nat_abs(v_val_275_);
v___x_285_ = l_Nat_reprFast(v_a_284_);
v___y_278_ = v___x_285_;
goto v___jp_277_;
}
else
{
lean_object* v_abs_286_; lean_object* v_one_287_; lean_object* v_a_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_abs_286_ = lean_nat_abs(v_val_275_);
v_one_287_ = lean_unsigned_to_nat(1u);
v_a_288_ = lean_nat_sub(v_abs_286_, v_one_287_);
lean_dec(v_abs_286_);
v___x_289_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_290_ = lean_nat_add(v_a_288_, v_one_287_);
lean_dec(v_a_288_);
v___x_291_ = l_Nat_reprFast(v___x_290_);
v___x_292_ = lean_string_append(v___x_289_, v___x_291_);
lean_dec_ref(v___x_291_);
v___y_278_ = v___x_292_;
goto v___jp_277_;
}
v___jp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_string_append(v___x_276_, v___y_278_);
lean_dec_ref(v___y_278_);
v___x_280_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__0));
v___x_281_ = lean_string_append(v___x_279_, v___x_280_);
return v___x_281_;
}
}
}
else
{
lean_object* v_upperBound_293_; 
v_upperBound_293_ = lean_ctor_get(v_x_265_, 1);
if (lean_obj_tag(v_upperBound_293_) == 0)
{
lean_object* v_val_294_; lean_object* v___x_295_; lean_object* v___y_297_; lean_object* v_intZero_301_; uint8_t v_isNeg_302_; 
v_val_294_ = lean_ctor_get(v_lowerBound_272_, 0);
v___x_295_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__3));
v_intZero_301_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_302_ = lean_int_dec_lt(v_val_294_, v_intZero_301_);
if (v_isNeg_302_ == 0)
{
lean_object* v_a_303_; lean_object* v___x_304_; 
v_a_303_ = lean_nat_abs(v_val_294_);
v___x_304_ = l_Nat_reprFast(v_a_303_);
v___y_297_ = v___x_304_;
goto v___jp_296_;
}
else
{
lean_object* v_abs_305_; lean_object* v_one_306_; lean_object* v_a_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_abs_305_ = lean_nat_abs(v_val_294_);
v_one_306_ = lean_unsigned_to_nat(1u);
v_a_307_ = lean_nat_sub(v_abs_305_, v_one_306_);
lean_dec(v_abs_305_);
v___x_308_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_309_ = lean_nat_add(v_a_307_, v_one_306_);
lean_dec(v_a_307_);
v___x_310_ = l_Nat_reprFast(v___x_309_);
v___x_311_ = lean_string_append(v___x_308_, v___x_310_);
lean_dec_ref(v___x_310_);
v___y_297_ = v___x_311_;
goto v___jp_296_;
}
v___jp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_string_append(v___x_295_, v___y_297_);
lean_dec_ref(v___y_297_);
v___x_299_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__4));
v___x_300_ = lean_string_append(v___x_298_, v___x_299_);
return v___x_300_;
}
}
else
{
lean_object* v_val_312_; lean_object* v_val_313_; uint8_t v___x_314_; 
v_val_312_ = lean_ctor_get(v_lowerBound_272_, 0);
v_val_313_ = lean_ctor_get(v_upperBound_293_, 0);
v___x_314_ = lean_int_dec_lt(v_val_313_, v_val_312_);
if (v___x_314_ == 0)
{
uint8_t v___x_315_; 
v___x_315_ = lean_int_dec_eq(v_val_312_, v_val_313_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___y_318_; lean_object* v_intZero_333_; uint8_t v_isNeg_334_; 
v___x_316_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__3));
v_intZero_333_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_334_ = lean_int_dec_lt(v_val_312_, v_intZero_333_);
if (v_isNeg_334_ == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; 
v_a_335_ = lean_nat_abs(v_val_312_);
v___x_336_ = l_Nat_reprFast(v_a_335_);
v___y_318_ = v___x_336_;
goto v___jp_317_;
}
else
{
lean_object* v_abs_337_; lean_object* v_one_338_; lean_object* v_a_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_abs_337_ = lean_nat_abs(v_val_312_);
v_one_338_ = lean_unsigned_to_nat(1u);
v_a_339_ = lean_nat_sub(v_abs_337_, v_one_338_);
lean_dec(v_abs_337_);
v___x_340_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_341_ = lean_nat_add(v_a_339_, v_one_338_);
lean_dec(v_a_339_);
v___x_342_ = l_Nat_reprFast(v___x_341_);
v___x_343_ = lean_string_append(v___x_340_, v___x_342_);
lean_dec_ref(v___x_342_);
v___y_318_ = v___x_343_;
goto v___jp_317_;
}
v___jp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_intZero_322_; uint8_t v_isNeg_323_; 
v___x_319_ = lean_string_append(v___x_316_, v___y_318_);
lean_dec_ref(v___y_318_);
v___x_320_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__5));
v___x_321_ = lean_string_append(v___x_319_, v___x_320_);
v_intZero_322_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_323_ = lean_int_dec_lt(v_val_313_, v_intZero_322_);
if (v_isNeg_323_ == 0)
{
lean_object* v_a_324_; lean_object* v___x_325_; 
v_a_324_ = lean_nat_abs(v_val_313_);
v___x_325_ = l_Nat_reprFast(v_a_324_);
v___y_267_ = v___x_321_;
v___y_268_ = v___x_325_;
goto v___jp_266_;
}
else
{
lean_object* v_abs_326_; lean_object* v_one_327_; lean_object* v_a_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_abs_326_ = lean_nat_abs(v_val_313_);
v_one_327_ = lean_unsigned_to_nat(1u);
v_a_328_ = lean_nat_sub(v_abs_326_, v_one_327_);
lean_dec(v_abs_326_);
v___x_329_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_330_ = lean_nat_add(v_a_328_, v_one_327_);
lean_dec(v_a_328_);
v___x_331_ = l_Nat_reprFast(v___x_330_);
v___x_332_ = lean_string_append(v___x_329_, v___x_331_);
lean_dec_ref(v___x_331_);
v___y_267_ = v___x_321_;
v___y_268_ = v___x_332_;
goto v___jp_266_;
}
}
}
else
{
lean_object* v___x_344_; lean_object* v___y_346_; lean_object* v_intZero_350_; uint8_t v_isNeg_351_; 
v___x_344_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__6));
v_intZero_350_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_351_ = lean_int_dec_lt(v_val_312_, v_intZero_350_);
if (v_isNeg_351_ == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; 
v_a_352_ = lean_nat_abs(v_val_312_);
v___x_353_ = l_Nat_reprFast(v_a_352_);
v___y_346_ = v___x_353_;
goto v___jp_345_;
}
else
{
lean_object* v_abs_354_; lean_object* v_one_355_; lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_abs_354_ = lean_nat_abs(v_val_312_);
v_one_355_ = lean_unsigned_to_nat(1u);
v_a_356_ = lean_nat_sub(v_abs_354_, v_one_355_);
lean_dec(v_abs_354_);
v___x_357_ = ((lean_object*)(l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_358_ = lean_nat_add(v_a_356_, v_one_355_);
lean_dec(v_a_356_);
v___x_359_ = l_Nat_reprFast(v___x_358_);
v___x_360_ = lean_string_append(v___x_357_, v___x_359_);
lean_dec_ref(v___x_359_);
v___y_346_ = v___x_360_;
goto v___jp_345_;
}
v___jp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_string_append(v___x_344_, v___y_346_);
lean_dec_ref(v___y_346_);
v___x_348_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__7));
v___x_349_ = lean_string_append(v___x_347_, v___x_348_);
return v___x_349_;
}
}
}
else
{
lean_object* v___x_361_; 
v___x_361_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__8));
return v___x_361_;
}
}
}
v___jp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_string_append(v___y_267_, v___y_268_);
lean_dec_ref(v___y_268_);
v___x_270_ = ((lean_object*)(l_Lean_Omega_Constraint_instToString___private__1___closed__0));
v___x_271_ = lean_string_append(v___x_269_, v___x_270_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_instToString___private__1___boxed(lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Omega_Constraint_instToString___private__1(v_x_362_);
lean_dec_ref(v_x_362_);
return v_res_363_;
}
}
uint8_t l_Lean_Omega_Constraint_sat(lean_object* v_c_366_, lean_object* v_t_367_){
_start:
{
lean_object* v_lowerBound_368_; lean_object* v_upperBound_369_; 
v_lowerBound_368_ = lean_ctor_get(v_c_366_, 0);
v_upperBound_369_ = lean_ctor_get(v_c_366_, 1);
if (lean_obj_tag(v_lowerBound_368_) == 0)
{
goto v___jp_370_;
}
else
{
lean_object* v_val_374_; uint8_t v___x_375_; 
v_val_374_ = lean_ctor_get(v_lowerBound_368_, 0);
v___x_375_ = lean_int_dec_le(v_val_374_, v_t_367_);
if (v___x_375_ == 0)
{
return v___x_375_;
}
else
{
goto v___jp_370_;
}
}
v___jp_370_:
{
if (lean_obj_tag(v_upperBound_369_) == 0)
{
uint8_t v___x_371_; 
v___x_371_ = 1;
return v___x_371_;
}
else
{
lean_object* v_val_372_; uint8_t v___x_373_; 
v_val_372_ = lean_ctor_get(v_upperBound_369_, 0);
v___x_373_ = lean_int_dec_le(v_t_367_, v_val_372_);
return v___x_373_;
}
}
}
}
LEAN_EXPORT void l_Lean_Omega_Constraint_sat_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_366_ = stack[0].m_obj;
lean_object* v_t_367_ = stack[1].m_obj;
uint8_t v_res_376_;
v_res_376_ = l_Lean_Omega_Constraint_sat(v_c_366_, v_t_367_);
stack->m_num = v_res_376_;
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_sat___boxed(lean_object* v_c_377_, lean_object* v_t_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l_Lean_Omega_Constraint_sat(v_c_377_, v_t_378_);
lean_dec(v_t_378_);
lean_dec_ref(v_c_377_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_map(lean_object* v_c_381_, lean_object* v_f_382_){
_start:
{
lean_object* v_lowerBound_383_; lean_object* v_upperBound_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_414_; 
v_lowerBound_383_ = lean_ctor_get(v_c_381_, 0);
v_upperBound_384_ = lean_ctor_get(v_c_381_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_c_381_);
if (v_isSharedCheck_414_ == 0)
{
v___x_386_ = v_c_381_;
v_isShared_387_ = v_isSharedCheck_414_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_upperBound_384_);
lean_inc(v_lowerBound_383_);
lean_dec(v_c_381_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_414_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___y_389_; 
if (lean_obj_tag(v_lowerBound_383_) == 0)
{
v___y_389_ = v_lowerBound_383_;
goto v___jp_388_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
v_val_405_ = lean_ctor_get(v_lowerBound_383_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v_lowerBound_383_);
if (v_isSharedCheck_413_ == 0)
{
v___x_407_ = v_lowerBound_383_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_val_405_);
lean_dec(v_lowerBound_383_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
lean_inc_ref(v_f_382_);
v___x_409_ = lean_apply_1(v_f_382_, v_val_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
v___y_389_ = v___x_411_;
goto v___jp_388_;
}
}
}
v___jp_388_:
{
if (lean_obj_tag(v_upperBound_384_) == 0)
{
lean_object* v___x_391_; 
lean_dec_ref(v_f_382_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___y_389_);
v___x_391_ = v___x_386_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___y_389_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_upperBound_384_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
else
{
lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_404_; 
v_val_393_ = lean_ctor_get(v_upperBound_384_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v_upperBound_384_);
if (v_isSharedCheck_404_ == 0)
{
v___x_395_ = v_upperBound_384_;
v_isShared_396_ = v_isSharedCheck_404_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_dec(v_upperBound_384_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_404_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_apply_1(v_f_382_, v_val_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v___x_399_);
lean_ctor_set(v___x_386_, 0, v___y_389_);
v___x_401_ = v___x_386_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___y_389_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate___lam__0(lean_object* v_t_415_, lean_object* v_x_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_int_add(v_x_416_, v_t_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate___lam__0___boxed(lean_object* v_t_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Omega_Constraint_translate___lam__0(v_t_418_, v_x_419_);
lean_dec(v_x_419_);
lean_dec(v_t_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate(lean_object* v_c_421_, lean_object* v_t_422_){
_start:
{
lean_object* v___f_423_; lean_object* v___x_424_; 
v___f_423_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_translate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_423_, 0, v_t_422_);
v___x_424_ = l_Lean_Omega_Constraint_map(v_c_421_, v___f_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_flip(lean_object* v_c_425_){
_start:
{
lean_object* v_lowerBound_426_; lean_object* v_upperBound_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_lowerBound_426_ = lean_ctor_get(v_c_425_, 0);
v_upperBound_427_ = lean_ctor_get(v_c_425_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_c_425_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v_c_425_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_upperBound_427_);
lean_inc(v_lowerBound_426_);
lean_dec(v_c_425_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v_lowerBound_426_);
lean_ctor_set(v___x_429_, 0, v_upperBound_427_);
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_upperBound_427_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_lowerBound_426_);
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
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_neg(lean_object* v_c_436_){
_start:
{
lean_object* v___f_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___f_437_ = ((lean_object*)(l_Lean_Omega_Constraint_neg___closed__0));
v___x_438_ = l_Lean_Omega_Constraint_flip(v_c_436_);
v___x_439_ = l_Lean_Omega_Constraint_map(v___x_438_, v___f_437_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__0(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_to_int(v___x_443_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__1(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__0, &l_Lean_Omega_Constraint_impossible___closed__0_once, _init_l_Lean_Omega_Constraint_impossible___closed__0);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__2(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__3(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__2, &l_Lean_Omega_Constraint_impossible___closed__2_once, _init_l_Lean_Omega_Constraint_impossible___closed__2);
v___x_450_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__1, &l_Lean_Omega_Constraint_impossible___closed__1_once, _init_l_Lean_Omega_Constraint_impossible___closed__1);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible(void){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__3, &l_Lean_Omega_Constraint_impossible___closed__3_once, _init_l_Lean_Omega_Constraint_impossible___closed__3);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_exact(lean_object* v_r_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v_r_453_);
lean_inc_ref(v___x_454_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
return v___x_455_;
}
}
uint8_t l_Lean_Omega_Constraint_isImpossible(lean_object* v_x_456_){
_start:
{
lean_object* v_lowerBound_457_; 
v_lowerBound_457_ = lean_ctor_get(v_x_456_, 0);
if (lean_obj_tag(v_lowerBound_457_) == 1)
{
lean_object* v_upperBound_458_; 
v_upperBound_458_ = lean_ctor_get(v_x_456_, 1);
if (lean_obj_tag(v_upperBound_458_) == 1)
{
lean_object* v_val_459_; lean_object* v_val_460_; uint8_t v___x_461_; 
v_val_459_ = lean_ctor_get(v_lowerBound_457_, 0);
v_val_460_ = lean_ctor_get(v_upperBound_458_, 0);
v___x_461_ = lean_int_dec_lt(v_val_460_, v_val_459_);
return v___x_461_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = 0;
return v___x_462_;
}
}
else
{
uint8_t v___x_463_; 
v___x_463_ = 0;
return v___x_463_;
}
}
}
LEAN_EXPORT void l_Lean_Omega_Constraint_isImpossible_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_456_ = stack[0].m_obj;
uint8_t v_res_464_;
v_res_464_ = l_Lean_Omega_Constraint_isImpossible(v_x_456_);
stack->m_num = v_res_464_;
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_isImpossible___boxed(lean_object* v_x_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Lean_Omega_Constraint_isImpossible(v_x_465_);
lean_dec_ref(v_x_465_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
uint8_t l_Lean_Omega_Constraint_isExact(lean_object* v_x_468_){
_start:
{
lean_object* v_lowerBound_469_; 
v_lowerBound_469_ = lean_ctor_get(v_x_468_, 0);
if (lean_obj_tag(v_lowerBound_469_) == 1)
{
lean_object* v_upperBound_470_; 
v_upperBound_470_ = lean_ctor_get(v_x_468_, 1);
if (lean_obj_tag(v_upperBound_470_) == 1)
{
lean_object* v_val_471_; lean_object* v_val_472_; uint8_t v___x_473_; 
v_val_471_ = lean_ctor_get(v_lowerBound_469_, 0);
v_val_472_ = lean_ctor_get(v_upperBound_470_, 0);
v___x_473_ = lean_int_dec_eq(v_val_471_, v_val_472_);
return v___x_473_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = 0;
return v___x_474_;
}
}
else
{
uint8_t v___x_475_; 
v___x_475_ = 0;
return v___x_475_;
}
}
}
LEAN_EXPORT void l_Lean_Omega_Constraint_isExact_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_468_ = stack[0].m_obj;
uint8_t v_res_476_;
v_res_476_ = l_Lean_Omega_Constraint_isExact(v_x_468_);
stack->m_num = v_res_476_;
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_isExact___boxed(lean_object* v_x_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_Lean_Omega_Constraint_isExact(v_x_477_);
lean_dec_ref(v_x_477_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter___redArg(lean_object* v_x_480_, lean_object* v_h__1_481_, lean_object* v_h__2_482_){
_start:
{
lean_object* v_lowerBound_483_; 
v_lowerBound_483_ = lean_ctor_get(v_x_480_, 0);
if (lean_obj_tag(v_lowerBound_483_) == 1)
{
lean_object* v_upperBound_484_; 
v_upperBound_484_ = lean_ctor_get(v_x_480_, 1);
if (lean_obj_tag(v_upperBound_484_) == 1)
{
lean_object* v_val_485_; lean_object* v_val_486_; lean_object* v___x_487_; 
lean_inc_ref(v_upperBound_484_);
lean_inc_ref(v_lowerBound_483_);
lean_dec(v_h__2_482_);
lean_dec_ref(v_x_480_);
v_val_485_ = lean_ctor_get(v_lowerBound_483_, 0);
lean_inc(v_val_485_);
lean_dec_ref_known(v_lowerBound_483_, 1);
v_val_486_ = lean_ctor_get(v_upperBound_484_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v_upperBound_484_, 1);
v___x_487_ = lean_apply_2(v_h__1_481_, v_val_485_, v_val_486_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; 
lean_dec(v_h__1_481_);
v___x_488_ = lean_apply_2(v_h__2_482_, v_x_480_, lean_box(0));
return v___x_488_;
}
}
else
{
lean_object* v___x_489_; 
lean_dec(v_h__1_481_);
v___x_489_ = lean_apply_2(v_h__2_482_, v_x_480_, lean_box(0));
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter(lean_object* v_motive_490_, lean_object* v_x_491_, lean_object* v_h__1_492_, lean_object* v_h__2_493_){
_start:
{
lean_object* v_lowerBound_494_; 
v_lowerBound_494_ = lean_ctor_get(v_x_491_, 0);
if (lean_obj_tag(v_lowerBound_494_) == 1)
{
lean_object* v_upperBound_495_; 
v_upperBound_495_ = lean_ctor_get(v_x_491_, 1);
if (lean_obj_tag(v_upperBound_495_) == 1)
{
lean_object* v_val_496_; lean_object* v_val_497_; lean_object* v___x_498_; 
lean_inc_ref(v_upperBound_495_);
lean_inc_ref(v_lowerBound_494_);
lean_dec(v_h__2_493_);
lean_dec_ref(v_x_491_);
v_val_496_ = lean_ctor_get(v_lowerBound_494_, 0);
lean_inc(v_val_496_);
lean_dec_ref_known(v_lowerBound_494_, 1);
v_val_497_ = lean_ctor_get(v_upperBound_495_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v_upperBound_495_, 1);
v___x_498_ = lean_apply_2(v_h__1_492_, v_val_496_, v_val_497_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
lean_dec(v_h__1_492_);
v___x_499_ = lean_apply_2(v_h__2_493_, v_x_491_, lean_box(0));
return v___x_499_;
}
}
else
{
lean_object* v___x_500_; 
lean_dec(v_h__1_492_);
v___x_500_ = lean_apply_2(v_h__2_493_, v_x_491_, lean_box(0));
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale___lam__0(lean_object* v_k_501_, lean_object* v_x_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_int_mul(v_k_501_, v_x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale___lam__0___boxed(lean_object* v_k_504_, lean_object* v_x_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Omega_Constraint_scale___lam__0(v_k_504_, v_x_505_);
lean_dec(v_x_505_);
lean_dec(v_k_504_);
return v_res_506_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_scale___closed__0(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__2, &l_Lean_Omega_Constraint_impossible___closed__2_once, _init_l_Lean_Omega_Constraint_impossible___closed__2);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale(lean_object* v_k_509_, lean_object* v_c_510_){
_start:
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_512_ = lean_int_dec_eq(v_k_509_, v___x_511_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; 
v___x_513_ = lean_int_dec_lt(v___x_511_, v_k_509_);
if (v___x_513_ == 0)
{
lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_scale___lam__0___boxed), 2, 1);
lean_closure_set(v___f_514_, 0, v_k_509_);
v___x_515_ = l_Lean_Omega_Constraint_flip(v_c_510_);
v___x_516_ = l_Lean_Omega_Constraint_map(v___x_515_, v___f_514_);
return v___x_516_;
}
else
{
lean_object* v___f_517_; lean_object* v___x_518_; 
v___f_517_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_scale___lam__0___boxed), 2, 1);
lean_closure_set(v___f_517_, 0, v_k_509_);
v___x_518_ = l_Lean_Omega_Constraint_map(v_c_510_, v___f_517_);
return v___x_518_;
}
}
else
{
uint8_t v___x_519_; 
lean_dec(v_k_509_);
v___x_519_ = l_Lean_Omega_Constraint_isImpossible(v_c_510_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
lean_dec_ref(v_c_510_);
v___x_520_ = lean_obj_once(&l_Lean_Omega_Constraint_scale___closed__0, &l_Lean_Omega_Constraint_scale___closed__0_once, _init_l_Lean_Omega_Constraint_scale___closed__0);
return v___x_520_;
}
else
{
return v_c_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_add(lean_object* v_x_521_, lean_object* v_y_522_){
_start:
{
lean_object* v_lowerBound_523_; lean_object* v_upperBound_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_566_; 
v_lowerBound_523_ = lean_ctor_get(v_x_521_, 0);
v_upperBound_524_ = lean_ctor_get(v_x_521_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_x_521_);
if (v_isSharedCheck_566_ == 0)
{
v___x_526_ = v_x_521_;
v_isShared_527_ = v_isSharedCheck_566_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_upperBound_524_);
lean_inc(v_lowerBound_523_);
lean_dec(v_x_521_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_566_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___y_529_; 
if (lean_obj_tag(v_lowerBound_523_) == 0)
{
v___y_529_ = v_lowerBound_523_;
goto v___jp_528_;
}
else
{
lean_object* v_lowerBound_555_; 
v_lowerBound_555_ = lean_ctor_get(v_y_522_, 0);
lean_inc(v_lowerBound_555_);
if (lean_obj_tag(v_lowerBound_555_) == 0)
{
lean_dec_ref_known(v_lowerBound_523_, 1);
v___y_529_ = v_lowerBound_555_;
goto v___jp_528_;
}
else
{
lean_object* v_val_556_; lean_object* v_val_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_565_; 
v_val_556_ = lean_ctor_get(v_lowerBound_523_, 0);
lean_inc(v_val_556_);
lean_dec_ref_known(v_lowerBound_523_, 1);
v_val_557_ = lean_ctor_get(v_lowerBound_555_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_lowerBound_555_);
if (v_isSharedCheck_565_ == 0)
{
v___x_559_ = v_lowerBound_555_;
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_val_557_);
lean_dec(v_lowerBound_555_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_int_add(v_val_556_, v_val_557_);
lean_dec(v_val_557_);
lean_dec(v_val_556_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
v___y_529_ = v___x_563_;
goto v___jp_528_;
}
}
}
}
v___jp_528_:
{
if (lean_obj_tag(v_upperBound_524_) == 0)
{
lean_object* v___x_531_; 
lean_dec_ref(v_y_522_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___y_529_);
v___x_531_ = v___x_526_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___y_529_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_upperBound_524_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
else
{
lean_object* v_upperBound_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_553_; 
lean_del_object(v___x_526_);
v_upperBound_533_ = lean_ctor_get(v_y_522_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_y_522_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v_y_522_, 0);
lean_dec(v_unused_554_);
v___x_535_ = v_y_522_;
v_isShared_536_ = v_isSharedCheck_553_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_upperBound_533_);
lean_dec(v_y_522_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_553_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
if (lean_obj_tag(v_upperBound_533_) == 0)
{
lean_object* v___x_538_; 
lean_dec_ref_known(v_upperBound_524_, 1);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___y_529_);
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___y_529_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_upperBound_533_);
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
lean_object* v_val_540_; lean_object* v_val_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_552_; 
v_val_540_ = lean_ctor_get(v_upperBound_524_, 0);
lean_inc(v_val_540_);
lean_dec_ref_known(v_upperBound_524_, 1);
v_val_541_ = lean_ctor_get(v_upperBound_533_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_upperBound_533_);
if (v_isSharedCheck_552_ == 0)
{
v___x_543_ = v_upperBound_533_;
v_isShared_544_ = v_isSharedCheck_552_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_val_541_);
lean_dec(v_upperBound_533_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_552_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_int_add(v_val_540_, v_val_541_);
lean_dec(v_val_541_);
lean_dec(v_val_540_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_551_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_549_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_547_);
lean_ctor_set(v___x_535_, 0, v___y_529_);
v___x_549_ = v___x_535_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___y_529_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
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
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combo(lean_object* v_a_567_, lean_object* v_x_568_, lean_object* v_b_569_, lean_object* v_y_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = l_Lean_Omega_Constraint_scale(v_a_567_, v_x_568_);
v___x_572_ = l_Lean_Omega_Constraint_scale(v_b_569_, v_y_570_);
v___x_573_ = l_Lean_Omega_Constraint_add(v___x_571_, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__0(lean_object* v_x_574_, lean_object* v_y_575_){
_start:
{
uint8_t v___x_576_; 
v___x_576_ = lean_int_dec_le(v_x_574_, v_y_575_);
if (v___x_576_ == 0)
{
lean_inc(v_x_574_);
return v_x_574_;
}
else
{
lean_inc(v_y_575_);
return v_y_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__0___boxed(lean_object* v_x_577_, lean_object* v_y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Omega_Constraint_combine___lam__0(v_x_577_, v_y_578_);
lean_dec(v_y_578_);
lean_dec(v_x_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__1(lean_object* v_x_580_, lean_object* v_y_581_){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = lean_int_dec_le(v_x_580_, v_y_581_);
if (v___x_582_ == 0)
{
lean_inc(v_y_581_);
return v_y_581_;
}
else
{
lean_inc(v_x_580_);
return v_x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__1___boxed(lean_object* v_x_583_, lean_object* v_y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Omega_Constraint_combine___lam__1(v_x_583_, v_y_584_);
lean_dec(v_y_584_);
lean_dec(v_x_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine(lean_object* v_x_588_, lean_object* v_y_589_){
_start:
{
lean_object* v_lowerBound_590_; lean_object* v_upperBound_591_; lean_object* v_lowerBound_592_; lean_object* v_upperBound_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_604_; 
v_lowerBound_590_ = lean_ctor_get(v_x_588_, 0);
lean_inc(v_lowerBound_590_);
v_upperBound_591_ = lean_ctor_get(v_x_588_, 1);
lean_inc(v_upperBound_591_);
lean_dec_ref(v_x_588_);
v_lowerBound_592_ = lean_ctor_get(v_y_589_, 0);
v_upperBound_593_ = lean_ctor_get(v_y_589_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_y_589_);
if (v_isSharedCheck_604_ == 0)
{
v___x_595_ = v_y_589_;
v_isShared_596_ = v_isSharedCheck_604_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_upperBound_593_);
lean_inc(v_lowerBound_592_);
lean_dec(v_y_589_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_604_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___f_597_ = ((lean_object*)(l_Lean_Omega_Constraint_combine___closed__0));
v___f_598_ = ((lean_object*)(l_Lean_Omega_Constraint_combine___closed__1));
v___x_599_ = l_Option_merge___redArg(v___f_597_, v_lowerBound_590_, v_lowerBound_592_);
v___x_600_ = l_Option_merge___redArg(v___f_598_, v_upperBound_591_, v_upperBound_593_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v___x_600_);
lean_ctor_set(v___x_595_, 0, v___x_599_);
v___x_602_ = v___x_595_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_div(lean_object* v_c_605_, lean_object* v_k_606_){
_start:
{
lean_object* v_lowerBound_607_; lean_object* v_upperBound_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_642_; 
v_lowerBound_607_ = lean_ctor_get(v_c_605_, 0);
v_upperBound_608_ = lean_ctor_get(v_c_605_, 1);
v_isSharedCheck_642_ = !lean_is_exclusive(v_c_605_);
if (v_isSharedCheck_642_ == 0)
{
v___x_610_ = v_c_605_;
v_isShared_611_ = v_isSharedCheck_642_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_upperBound_608_);
lean_inc(v_lowerBound_607_);
lean_dec(v_c_605_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_642_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___y_613_; 
if (lean_obj_tag(v_lowerBound_607_) == 0)
{
v___y_613_ = v_lowerBound_607_;
goto v___jp_612_;
}
else
{
lean_object* v_val_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_641_; 
v_val_630_ = lean_ctor_get(v_lowerBound_607_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_lowerBound_607_);
if (v_isSharedCheck_641_ == 0)
{
v___x_632_ = v_lowerBound_607_;
v_isShared_633_ = v_isSharedCheck_641_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_val_630_);
lean_dec(v_lowerBound_607_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_641_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_634_ = lean_int_neg(v_val_630_);
lean_dec(v_val_630_);
lean_inc(v_k_606_);
v___x_635_ = lean_nat_to_int(v_k_606_);
v___x_636_ = lean_int_ediv(v___x_634_, v___x_635_);
lean_dec(v___x_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_int_neg(v___x_636_);
lean_dec(v___x_636_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_637_);
v___x_639_ = v___x_632_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
v___y_613_ = v___x_639_;
goto v___jp_612_;
}
}
}
v___jp_612_:
{
if (lean_obj_tag(v_upperBound_608_) == 0)
{
lean_object* v___x_615_; 
lean_dec(v_k_606_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___y_613_);
v___x_615_ = v___x_610_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___y_613_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_upperBound_608_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
else
{
lean_object* v_val_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_629_; 
v_val_617_ = lean_ctor_get(v_upperBound_608_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_upperBound_608_);
if (v_isSharedCheck_629_ == 0)
{
v___x_619_ = v_upperBound_608_;
v_isShared_620_ = v_isSharedCheck_629_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_val_617_);
lean_dec(v_upperBound_608_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_629_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_621_ = lean_nat_to_int(v_k_606_);
v___x_622_ = lean_int_ediv(v_val_617_, v___x_621_);
lean_dec(v___x_621_);
lean_dec(v_val_617_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_622_);
v___x_624_ = v___x_619_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_628_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 1, v___x_624_);
lean_ctor_set(v___x_610_, 0, v___y_613_);
v___x_626_ = v___x_610_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___y_613_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
}
}
uint8_t l_Lean_Omega_Constraint_sat_x27(lean_object* v_c_643_, lean_object* v_x_644_, lean_object* v_y_645_){
_start:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = l_Lean_Omega_IntList_dot(v_x_644_, v_y_645_);
v___x_647_ = l_Lean_Omega_Constraint_sat(v_c_643_, v___x_646_);
lean_dec(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT void l_Lean_Omega_Constraint_sat_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_643_ = stack[0].m_obj;
lean_object* v_x_644_ = stack[1].m_obj;
lean_object* v_y_645_ = stack[2].m_obj;
uint8_t v_res_648_;
v_res_648_ = l_Lean_Omega_Constraint_sat_x27(v_c_643_, v_x_644_, v_y_645_);
stack->m_num = v_res_648_;
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_sat_x27___boxed(lean_object* v_c_649_, lean_object* v_x_650_, lean_object* v_y_651_){
_start:
{
uint8_t v_res_652_; lean_object* v_r_653_; 
v_res_652_ = l_Lean_Omega_Constraint_sat_x27(v_c_649_, v_x_650_, v_y_651_);
lean_dec(v_x_650_);
lean_dec_ref(v_c_649_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_normalize_x3f(lean_object* v_x_654_){
_start:
{
lean_object* v_fst_655_; lean_object* v_snd_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_685_; 
v_fst_655_ = lean_ctor_get(v_x_654_, 0);
v_snd_656_ = lean_ctor_get(v_x_654_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_685_ == 0)
{
v___x_658_ = v_x_654_;
v_isShared_659_ = v_isSharedCheck_685_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_snd_656_);
lean_inc(v_fst_655_);
lean_dec(v_x_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_685_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_gcd_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_gcd_660_ = l_Lean_Omega_IntList_gcd(v_snd_656_);
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = lean_nat_dec_eq(v_gcd_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_dec_eq(v_gcd_660_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
lean_inc(v_gcd_660_);
v___x_665_ = l_Lean_Omega_Constraint_div(v_fst_655_, v_gcd_660_);
v___x_666_ = lean_nat_to_int(v_gcd_660_);
v___x_667_ = l_Lean_Omega_IntList_sdiv(v_snd_656_, v___x_666_);
lean_dec(v___x_666_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_667_);
lean_ctor_set(v___x_658_, 0, v___x_665_);
v___x_669_ = v___x_658_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_667_);
v___x_669_ = v_reuseFailAlloc_671_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
else
{
lean_object* v___x_672_; 
lean_dec(v_gcd_660_);
lean_del_object(v___x_658_);
lean_dec(v_snd_656_);
lean_dec(v_fst_655_);
v___x_672_ = lean_box(0);
return v___x_672_;
}
}
else
{
lean_object* v___x_673_; uint8_t v___x_674_; 
lean_dec(v_gcd_660_);
v___x_673_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_674_ = l_Lean_Omega_Constraint_sat(v_fst_655_, v___x_673_);
lean_dec(v_fst_655_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = l_Lean_Omega_Constraint_impossible;
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_675_);
v___x_677_ = v___x_658_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_snd_656_);
v___x_677_ = v_reuseFailAlloc_679_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; 
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
else
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = ((lean_object*)(l_Lean_Omega_Constraint_trivial));
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_680_);
v___x_682_ = v___x_658_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_snd_656_);
v___x_682_ = v_reuseFailAlloc_684_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; 
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_normalize(lean_object* v_p_686_){
_start:
{
lean_object* v___x_687_; 
lean_inc_ref(v_p_686_);
v___x_687_ = l_Lean_Omega_normalize_x3f(v_p_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
return v_p_686_;
}
else
{
lean_object* v_val_688_; 
lean_dec_ref(v_p_686_);
v_val_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v___x_687_, 1);
return v_val_688_;
}
}
}
static lean_object* _init_l_Lean_Omega_positivize_x3f___closed__0(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__0, &l_Lean_Omega_Constraint_impossible___closed__0_once, _init_l_Lean_Omega_Constraint_impossible___closed__0);
v___x_690_ = lean_int_neg(v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_positivize_x3f(lean_object* v_x_691_){
_start:
{
lean_object* v_fst_692_; lean_object* v_snd_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_708_; 
v_fst_692_ = lean_ctor_get(v_x_691_, 0);
v_snd_693_ = lean_ctor_get(v_x_691_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_x_691_);
if (v_isSharedCheck_708_ == 0)
{
v___x_695_ = v_x_691_;
v_isShared_696_ = v_isSharedCheck_708_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_snd_693_);
lean_inc(v_fst_692_);
lean_dec(v_x_691_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_708_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_697_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_698_ = l_Lean_Omega_IntList_leading(v_snd_693_);
v___x_699_ = lean_int_dec_le(v___x_697_, v___x_698_);
lean_dec(v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_700_ = l_Lean_Omega_Constraint_neg(v_fst_692_);
v___x_701_ = lean_obj_once(&l_Lean_Omega_positivize_x3f___closed__0, &l_Lean_Omega_positivize_x3f___closed__0_once, _init_l_Lean_Omega_positivize_x3f___closed__0);
v___x_702_ = l_Lean_Omega_IntList_smul(v_snd_693_, v___x_701_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v___x_702_);
lean_ctor_set(v___x_695_, 0, v___x_700_);
v___x_704_ = v___x_695_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_702_);
v___x_704_ = v_reuseFailAlloc_706_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; 
v___x_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
else
{
lean_object* v___x_707_; 
lean_del_object(v___x_695_);
lean_dec(v_snd_693_);
lean_dec(v_fst_692_);
v___x_707_ = lean_box(0);
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidy_x3f(lean_object* v_x_709_){
_start:
{
lean_object* v___x_710_; 
lean_inc_ref(v_x_709_);
v___x_710_ = l_Lean_Omega_positivize_x3f(v_x_709_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Omega_normalize_x3f(v_x_709_);
return v___x_711_;
}
else
{
lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref(v_x_709_);
v_val_712_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_720_ == 0)
{
v___x_714_ = v___x_710_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_dec(v___x_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = l_Lean_Omega_normalize(v_val_712_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidy(lean_object* v_p_721_){
_start:
{
lean_object* v___x_722_; 
lean_inc_ref(v_p_721_);
v___x_722_ = l_Lean_Omega_tidy_x3f(v_p_721_);
if (lean_obj_tag(v___x_722_) == 0)
{
return v_p_721_;
}
else
{
lean_object* v_val_723_; 
lean_dec_ref(v_p_721_);
v_val_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_val_723_);
lean_dec_ref_known(v___x_722_, 1);
return v_val_723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidyConstraint(lean_object* v_s_724_, lean_object* v_x_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_fst_728_; 
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_s_724_);
lean_ctor_set(v___x_726_, 1, v_x_725_);
v___x_727_ = l_Lean_Omega_tidy(v___x_726_);
v_fst_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_fst_728_);
lean_dec_ref(v___x_727_);
return v_fst_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidyCoeffs(lean_object* v_s_729_, lean_object* v_x_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_snd_733_; 
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_s_729_);
lean_ctor_set(v___x_731_, 1, v_x_730_);
v___x_732_ = l_Lean_Omega_tidy(v___x_731_);
v_snd_733_ = lean_ctor_get(v___x_732_, 1);
lean_inc(v_snd_733_);
lean_dec_ref(v___x_732_);
return v_snd_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter___redArg(lean_object* v_x_734_, lean_object* v_h__1_735_, lean_object* v_h__2_736_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; 
lean_dec(v_h__2_736_);
v___x_737_ = lean_box(0);
v___x_738_ = lean_apply_1(v_h__1_735_, v___x_737_);
return v___x_738_;
}
else
{
lean_object* v_val_739_; lean_object* v_fst_740_; lean_object* v_snd_741_; lean_object* v___x_742_; 
lean_dec(v_h__1_735_);
v_val_739_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v_x_734_, 1);
v_fst_740_ = lean_ctor_get(v_val_739_, 0);
lean_inc(v_fst_740_);
v_snd_741_ = lean_ctor_get(v_val_739_, 1);
lean_inc(v_snd_741_);
lean_dec(v_val_739_);
v___x_742_ = lean_apply_2(v_h__2_736_, v_fst_740_, v_snd_741_);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter(lean_object* v_motive_743_, lean_object* v_x_744_, lean_object* v_h__1_745_, lean_object* v_h__2_746_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec(v_h__2_746_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_apply_1(v_h__1_745_, v___x_747_);
return v___x_748_;
}
else
{
lean_object* v_val_749_; lean_object* v_fst_750_; lean_object* v_snd_751_; lean_object* v___x_752_; 
lean_dec(v_h__1_745_);
v_val_749_ = lean_ctor_get(v_x_744_, 0);
lean_inc(v_val_749_);
lean_dec_ref_known(v_x_744_, 1);
v_fst_750_ = lean_ctor_get(v_val_749_, 0);
lean_inc(v_fst_750_);
v_snd_751_ = lean_ctor_get(v_val_749_, 1);
lean_inc(v_snd_751_);
lean_dec(v_val_749_);
v___x_752_ = lean_apply_2(v_h__2_746_, v_fst_750_, v_snd_751_);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term___lam__0(lean_object* v_m_753_, lean_object* v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Int_bmod(v_x_754_, v_m_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term___lam__0___boxed(lean_object* v_m_756_, lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Omega_bmod__div__term___lam__0(v_m_756_, v_x_757_);
lean_dec(v_x_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term(lean_object* v_m_759_, lean_object* v_a_760_, lean_object* v_b_761_){
_start:
{
lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_inc_n(v_m_759_, 2);
v___f_762_ = lean_alloc_closure((void*)(l_Lean_Omega_bmod__div__term___lam__0___boxed), 2, 1);
lean_closure_set(v___f_762_, 0, v_m_759_);
lean_inc(v_b_761_);
v___x_763_ = l_Lean_Omega_IntList_dot(v_a_760_, v_b_761_);
v___x_764_ = l_Int_bmod(v___x_763_, v_m_759_);
lean_dec(v___x_763_);
v___x_765_ = lean_box(0);
v___x_766_ = l_List_mapTR_loop___redArg(v___f_762_, v_a_760_, v___x_765_);
v___x_767_ = l_Lean_Omega_IntList_dot(v___x_766_, v_b_761_);
lean_dec(v___x_766_);
v___x_768_ = lean_int_sub(v___x_764_, v___x_767_);
lean_dec(v___x_767_);
lean_dec(v___x_764_);
v___x_769_ = lean_nat_to_int(v_m_759_);
v___x_770_ = lean_int_ediv(v___x_768_, v___x_769_);
lean_dec(v___x_769_);
lean_dec(v___x_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_bmod__coeffs_spec__0(lean_object* v_m_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
if (lean_obj_tag(v_a_772_) == 0)
{
lean_object* v___x_774_; 
lean_dec(v_m_771_);
v___x_774_ = l_List_reverse___redArg(v_a_773_);
return v___x_774_;
}
else
{
lean_object* v_head_775_; lean_object* v_tail_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_785_; 
v_head_775_ = lean_ctor_get(v_a_772_, 0);
v_tail_776_ = lean_ctor_get(v_a_772_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_a_772_);
if (v_isSharedCheck_785_ == 0)
{
v___x_778_ = v_a_772_;
v_isShared_779_ = v_isSharedCheck_785_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_tail_776_);
lean_inc(v_head_775_);
lean_dec(v_a_772_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_785_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_inc(v_m_771_);
v___x_780_ = l_Int_bmod(v_head_775_, v_m_771_);
lean_dec(v_head_775_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_a_773_);
lean_ctor_set(v___x_778_, 0, v___x_780_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_a_773_);
v___x_782_ = v_reuseFailAlloc_784_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
v_a_772_ = v_tail_776_;
v_a_773_ = v___x_782_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__coeffs(lean_object* v_m_786_, lean_object* v_i_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_789_ = lean_box(0);
lean_inc(v_m_786_);
v___x_790_ = l_List_mapTR_loop___at___00Lean_Omega_bmod__coeffs_spec__0(v_m_786_, v_x_788_, v___x_789_);
v___x_791_ = lean_nat_to_int(v_m_786_);
v___x_792_ = l_Lean_Omega_IntList_set(v___x_790_, v_i_787_, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__coeffs___boxed(lean_object* v_m_793_, lean_object* v_i_794_, lean_object* v_x_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Omega_bmod__coeffs(v_m_793_, v_i_794_, v_x_795_);
lean_dec(v_i_794_);
return v_res_796_;
}
}
lean_object* runtime_initialize_Init_Omega_Coeffs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega_Int(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Omega_Constraint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
