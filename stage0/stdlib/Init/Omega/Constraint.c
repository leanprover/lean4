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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(lean_object* v_x_73_, lean_object* v_x_74_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0___boxed(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_x_81_, v_x_82_);
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
v___x_91_ = l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_lowerBound_87_, v_lowerBound_89_);
if (v___x_91_ == 0)
{
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = l_instBEqOption_beq___at___00Lean_Omega_instBEqConstraint_beq_spec__0(v_upperBound_88_, v_upperBound_90_);
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
lean_object* v_lowerBound_362_; lean_object* v_upperBound_363_; 
v_lowerBound_362_ = lean_ctor_get(v_c_360_, 0);
v_upperBound_363_ = lean_ctor_get(v_c_360_, 1);
if (lean_obj_tag(v_lowerBound_362_) == 0)
{
goto v___jp_364_;
}
else
{
lean_object* v_val_368_; uint8_t v___x_369_; 
v_val_368_ = lean_ctor_get(v_lowerBound_362_, 0);
v___x_369_ = lean_int_dec_le(v_val_368_, v_t_361_);
if (v___x_369_ == 0)
{
return v___x_369_;
}
else
{
goto v___jp_364_;
}
}
v___jp_364_:
{
if (lean_obj_tag(v_upperBound_363_) == 0)
{
uint8_t v___x_365_; 
v___x_365_ = 1;
return v___x_365_;
}
else
{
lean_object* v_val_366_; uint8_t v___x_367_; 
v_val_366_ = lean_ctor_get(v_upperBound_363_, 0);
v___x_367_ = lean_int_dec_le(v_t_361_, v_val_366_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_sat___boxed(lean_object* v_c_370_, lean_object* v_t_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Lean_Omega_Constraint_sat(v_c_370_, v_t_371_);
lean_dec(v_t_371_);
lean_dec_ref(v_c_370_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_map(lean_object* v_c_374_, lean_object* v_f_375_){
_start:
{
lean_object* v_lowerBound_376_; lean_object* v_upperBound_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_407_; 
v_lowerBound_376_ = lean_ctor_get(v_c_374_, 0);
v_upperBound_377_ = lean_ctor_get(v_c_374_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_c_374_);
if (v_isSharedCheck_407_ == 0)
{
v___x_379_ = v_c_374_;
v_isShared_380_ = v_isSharedCheck_407_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_upperBound_377_);
lean_inc(v_lowerBound_376_);
lean_dec(v_c_374_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_407_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___y_382_; 
if (lean_obj_tag(v_lowerBound_376_) == 0)
{
v___y_382_ = v_lowerBound_376_;
goto v___jp_381_;
}
else
{
lean_object* v_val_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_val_398_ = lean_ctor_get(v_lowerBound_376_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_lowerBound_376_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v_lowerBound_376_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_val_398_);
lean_dec(v_lowerBound_376_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_inc_ref(v_f_375_);
v___x_402_ = lean_apply_1(v_f_375_, v_val_398_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
v___y_382_ = v___x_404_;
goto v___jp_381_;
}
}
}
v___jp_381_:
{
if (lean_obj_tag(v_upperBound_377_) == 0)
{
lean_object* v___x_384_; 
lean_dec_ref(v_f_375_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___y_382_);
v___x_384_ = v___x_379_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___y_382_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_upperBound_377_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
else
{
lean_object* v_val_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_397_; 
v_val_386_ = lean_ctor_get(v_upperBound_377_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v_upperBound_377_);
if (v_isSharedCheck_397_ == 0)
{
v___x_388_ = v_upperBound_377_;
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_val_386_);
lean_dec(v_upperBound_377_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = lean_apply_1(v_f_375_, v_val_386_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_390_);
v___x_392_ = v___x_388_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_396_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v___x_392_);
lean_ctor_set(v___x_379_, 0, v___y_382_);
v___x_394_ = v___x_379_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___y_382_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate___lam__0(lean_object* v_t_408_, lean_object* v_x_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_int_add(v_x_409_, v_t_408_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate___lam__0___boxed(lean_object* v_t_411_, lean_object* v_x_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Omega_Constraint_translate___lam__0(v_t_411_, v_x_412_);
lean_dec(v_x_412_);
lean_dec(v_t_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_translate(lean_object* v_c_414_, lean_object* v_t_415_){
_start:
{
lean_object* v___f_416_; lean_object* v___x_417_; 
v___f_416_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_translate___lam__0___boxed), 2, 1);
lean_closure_set(v___f_416_, 0, v_t_415_);
v___x_417_ = l_Lean_Omega_Constraint_map(v_c_414_, v___f_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_flip(lean_object* v_c_418_){
_start:
{
lean_object* v_lowerBound_419_; lean_object* v_upperBound_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
v_lowerBound_419_ = lean_ctor_get(v_c_418_, 0);
v_upperBound_420_ = lean_ctor_get(v_c_418_, 1);
v_isSharedCheck_427_ = !lean_is_exclusive(v_c_418_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v_c_418_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_upperBound_420_);
lean_inc(v_lowerBound_419_);
lean_dec(v_c_418_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 1, v_lowerBound_419_);
lean_ctor_set(v___x_422_, 0, v_upperBound_420_);
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_upperBound_420_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_lowerBound_419_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_neg(lean_object* v_c_429_){
_start:
{
lean_object* v___f_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___f_430_ = ((lean_object*)(l_Lean_Omega_Constraint_neg___closed__0));
v___x_431_ = l_Lean_Omega_Constraint_flip(v_c_429_);
v___x_432_ = l_Lean_Omega_Constraint_map(v___x_431_, v___f_430_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__0(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_nat_to_int(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__1(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__0, &l_Lean_Omega_Constraint_impossible___closed__0_once, _init_l_Lean_Omega_Constraint_impossible___closed__0);
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__2(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible___closed__3(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__2, &l_Lean_Omega_Constraint_impossible___closed__2_once, _init_l_Lean_Omega_Constraint_impossible___closed__2);
v___x_443_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__1, &l_Lean_Omega_Constraint_impossible___closed__1_once, _init_l_Lean_Omega_Constraint_impossible___closed__1);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_impossible(void){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__3, &l_Lean_Omega_Constraint_impossible___closed__3_once, _init_l_Lean_Omega_Constraint_impossible___closed__3);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_exact(lean_object* v_r_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v_r_446_);
lean_inc_ref(v___x_447_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_isImpossible(lean_object* v_x_449_){
_start:
{
lean_object* v_lowerBound_450_; 
v_lowerBound_450_ = lean_ctor_get(v_x_449_, 0);
if (lean_obj_tag(v_lowerBound_450_) == 1)
{
lean_object* v_upperBound_451_; 
v_upperBound_451_ = lean_ctor_get(v_x_449_, 1);
if (lean_obj_tag(v_upperBound_451_) == 1)
{
lean_object* v_val_452_; lean_object* v_val_453_; uint8_t v___x_454_; 
v_val_452_ = lean_ctor_get(v_lowerBound_450_, 0);
v_val_453_ = lean_ctor_get(v_upperBound_451_, 0);
v___x_454_ = lean_int_dec_lt(v_val_453_, v_val_452_);
return v___x_454_;
}
else
{
uint8_t v___x_455_; 
v___x_455_ = 0;
return v___x_455_;
}
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_isImpossible___boxed(lean_object* v_x_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Lean_Omega_Constraint_isImpossible(v_x_457_);
lean_dec_ref(v_x_457_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_isExact(lean_object* v_x_460_){
_start:
{
lean_object* v_lowerBound_461_; 
v_lowerBound_461_ = lean_ctor_get(v_x_460_, 0);
if (lean_obj_tag(v_lowerBound_461_) == 1)
{
lean_object* v_upperBound_462_; 
v_upperBound_462_ = lean_ctor_get(v_x_460_, 1);
if (lean_obj_tag(v_upperBound_462_) == 1)
{
lean_object* v_val_463_; lean_object* v_val_464_; uint8_t v___x_465_; 
v_val_463_ = lean_ctor_get(v_lowerBound_461_, 0);
v_val_464_ = lean_ctor_get(v_upperBound_462_, 0);
v___x_465_ = lean_int_dec_eq(v_val_463_, v_val_464_);
return v___x_465_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = 0;
return v___x_466_;
}
}
else
{
uint8_t v___x_467_; 
v___x_467_ = 0;
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_isExact___boxed(lean_object* v_x_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_Lean_Omega_Constraint_isExact(v_x_468_);
lean_dec_ref(v_x_468_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter___redArg(lean_object* v_x_471_, lean_object* v_h__1_472_, lean_object* v_h__2_473_){
_start:
{
lean_object* v_lowerBound_474_; 
v_lowerBound_474_ = lean_ctor_get(v_x_471_, 0);
if (lean_obj_tag(v_lowerBound_474_) == 1)
{
lean_object* v_upperBound_475_; 
v_upperBound_475_ = lean_ctor_get(v_x_471_, 1);
if (lean_obj_tag(v_upperBound_475_) == 1)
{
lean_object* v_val_476_; lean_object* v_val_477_; lean_object* v___x_478_; 
lean_inc_ref(v_upperBound_475_);
lean_inc_ref(v_lowerBound_474_);
lean_dec(v_h__2_473_);
lean_dec_ref(v_x_471_);
v_val_476_ = lean_ctor_get(v_lowerBound_474_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v_lowerBound_474_, 1);
v_val_477_ = lean_ctor_get(v_upperBound_475_, 0);
lean_inc(v_val_477_);
lean_dec_ref_known(v_upperBound_475_, 1);
v___x_478_ = lean_apply_2(v_h__1_472_, v_val_476_, v_val_477_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
lean_dec(v_h__1_472_);
v___x_479_ = lean_apply_2(v_h__2_473_, v_x_471_, lean_box(0));
return v___x_479_;
}
}
else
{
lean_object* v___x_480_; 
lean_dec(v_h__1_472_);
v___x_480_ = lean_apply_2(v_h__2_473_, v_x_471_, lean_box(0));
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_Constraint_isImpossible_match__1_splitter(lean_object* v_motive_481_, lean_object* v_x_482_, lean_object* v_h__1_483_, lean_object* v_h__2_484_){
_start:
{
lean_object* v_lowerBound_485_; 
v_lowerBound_485_ = lean_ctor_get(v_x_482_, 0);
if (lean_obj_tag(v_lowerBound_485_) == 1)
{
lean_object* v_upperBound_486_; 
v_upperBound_486_ = lean_ctor_get(v_x_482_, 1);
if (lean_obj_tag(v_upperBound_486_) == 1)
{
lean_object* v_val_487_; lean_object* v_val_488_; lean_object* v___x_489_; 
lean_inc_ref(v_upperBound_486_);
lean_inc_ref(v_lowerBound_485_);
lean_dec(v_h__2_484_);
lean_dec_ref(v_x_482_);
v_val_487_ = lean_ctor_get(v_lowerBound_485_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v_lowerBound_485_, 1);
v_val_488_ = lean_ctor_get(v_upperBound_486_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v_upperBound_486_, 1);
v___x_489_ = lean_apply_2(v_h__1_483_, v_val_487_, v_val_488_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; 
lean_dec(v_h__1_483_);
v___x_490_ = lean_apply_2(v_h__2_484_, v_x_482_, lean_box(0));
return v___x_490_;
}
}
else
{
lean_object* v___x_491_; 
lean_dec(v_h__1_483_);
v___x_491_ = lean_apply_2(v_h__2_484_, v_x_482_, lean_box(0));
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale___lam__0(lean_object* v_k_492_, lean_object* v_x_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = lean_int_mul(v_k_492_, v_x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale___lam__0___boxed(lean_object* v_k_495_, lean_object* v_x_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Omega_Constraint_scale___lam__0(v_k_495_, v_x_496_);
lean_dec(v_x_496_);
lean_dec(v_k_495_);
return v_res_497_;
}
}
static lean_object* _init_l_Lean_Omega_Constraint_scale___closed__0(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__2, &l_Lean_Omega_Constraint_impossible___closed__2_once, _init_l_Lean_Omega_Constraint_impossible___closed__2);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_scale(lean_object* v_k_500_, lean_object* v_c_501_){
_start:
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_503_ = lean_int_dec_eq(v_k_500_, v___x_502_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
v___x_504_ = lean_int_dec_lt(v___x_502_, v_k_500_);
if (v___x_504_ == 0)
{
lean_object* v___f_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___f_505_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_scale___lam__0___boxed), 2, 1);
lean_closure_set(v___f_505_, 0, v_k_500_);
v___x_506_ = l_Lean_Omega_Constraint_flip(v_c_501_);
v___x_507_ = l_Lean_Omega_Constraint_map(v___x_506_, v___f_505_);
return v___x_507_;
}
else
{
lean_object* v___f_508_; lean_object* v___x_509_; 
v___f_508_ = lean_alloc_closure((void*)(l_Lean_Omega_Constraint_scale___lam__0___boxed), 2, 1);
lean_closure_set(v___f_508_, 0, v_k_500_);
v___x_509_ = l_Lean_Omega_Constraint_map(v_c_501_, v___f_508_);
return v___x_509_;
}
}
else
{
uint8_t v___x_510_; 
lean_dec(v_k_500_);
v___x_510_ = l_Lean_Omega_Constraint_isImpossible(v_c_501_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v_c_501_);
v___x_511_ = lean_obj_once(&l_Lean_Omega_Constraint_scale___closed__0, &l_Lean_Omega_Constraint_scale___closed__0_once, _init_l_Lean_Omega_Constraint_scale___closed__0);
return v___x_511_;
}
else
{
return v_c_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_add(lean_object* v_x_512_, lean_object* v_y_513_){
_start:
{
lean_object* v_lowerBound_514_; lean_object* v_upperBound_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_557_; 
v_lowerBound_514_ = lean_ctor_get(v_x_512_, 0);
v_upperBound_515_ = lean_ctor_get(v_x_512_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_557_ == 0)
{
v___x_517_ = v_x_512_;
v_isShared_518_ = v_isSharedCheck_557_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_upperBound_515_);
lean_inc(v_lowerBound_514_);
lean_dec(v_x_512_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_557_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___y_520_; 
if (lean_obj_tag(v_lowerBound_514_) == 0)
{
v___y_520_ = v_lowerBound_514_;
goto v___jp_519_;
}
else
{
lean_object* v_lowerBound_546_; 
v_lowerBound_546_ = lean_ctor_get(v_y_513_, 0);
lean_inc(v_lowerBound_546_);
if (lean_obj_tag(v_lowerBound_546_) == 0)
{
lean_dec_ref_known(v_lowerBound_514_, 1);
v___y_520_ = v_lowerBound_546_;
goto v___jp_519_;
}
else
{
lean_object* v_val_547_; lean_object* v_val_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_556_; 
v_val_547_ = lean_ctor_get(v_lowerBound_514_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v_lowerBound_514_, 1);
v_val_548_ = lean_ctor_get(v_lowerBound_546_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_lowerBound_546_);
if (v_isSharedCheck_556_ == 0)
{
v___x_550_ = v_lowerBound_546_;
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_val_548_);
lean_dec(v_lowerBound_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_int_add(v_val_547_, v_val_548_);
lean_dec(v_val_548_);
lean_dec(v_val_547_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
v___y_520_ = v___x_554_;
goto v___jp_519_;
}
}
}
}
v___jp_519_:
{
if (lean_obj_tag(v_upperBound_515_) == 0)
{
lean_object* v___x_522_; 
lean_dec_ref(v_y_513_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___y_520_);
v___x_522_ = v___x_517_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___y_520_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_upperBound_515_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
lean_object* v_upperBound_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_544_; 
lean_del_object(v___x_517_);
v_upperBound_524_ = lean_ctor_get(v_y_513_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_y_513_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v_y_513_, 0);
lean_dec(v_unused_545_);
v___x_526_ = v_y_513_;
v_isShared_527_ = v_isSharedCheck_544_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_upperBound_524_);
lean_dec(v_y_513_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_544_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
if (lean_obj_tag(v_upperBound_524_) == 0)
{
lean_object* v___x_529_; 
lean_dec_ref_known(v_upperBound_515_, 1);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___y_520_);
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___y_520_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_upperBound_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
else
{
lean_object* v_val_531_; lean_object* v_val_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_543_; 
v_val_531_ = lean_ctor_get(v_upperBound_515_, 0);
lean_inc(v_val_531_);
lean_dec_ref_known(v_upperBound_515_, 1);
v_val_532_ = lean_ctor_get(v_upperBound_524_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_upperBound_524_);
if (v_isSharedCheck_543_ == 0)
{
v___x_534_ = v_upperBound_524_;
v_isShared_535_ = v_isSharedCheck_543_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_val_532_);
lean_dec(v_upperBound_524_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_543_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_int_add(v_val_531_, v_val_532_);
lean_dec(v_val_532_);
lean_dec(v_val_531_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_536_);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_542_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_540_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v___x_538_);
lean_ctor_set(v___x_526_, 0, v___y_520_);
v___x_540_ = v___x_526_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___y_520_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combo(lean_object* v_a_558_, lean_object* v_x_559_, lean_object* v_b_560_, lean_object* v_y_561_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = l_Lean_Omega_Constraint_scale(v_a_558_, v_x_559_);
v___x_563_ = l_Lean_Omega_Constraint_scale(v_b_560_, v_y_561_);
v___x_564_ = l_Lean_Omega_Constraint_add(v___x_562_, v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__0(lean_object* v_x_565_, lean_object* v_y_566_){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = lean_int_dec_le(v_x_565_, v_y_566_);
if (v___x_567_ == 0)
{
lean_inc(v_x_565_);
return v_x_565_;
}
else
{
lean_inc(v_y_566_);
return v_y_566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__0___boxed(lean_object* v_x_568_, lean_object* v_y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Omega_Constraint_combine___lam__0(v_x_568_, v_y_569_);
lean_dec(v_y_569_);
lean_dec(v_x_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__1(lean_object* v_x_571_, lean_object* v_y_572_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = lean_int_dec_le(v_x_571_, v_y_572_);
if (v___x_573_ == 0)
{
lean_inc(v_y_572_);
return v_y_572_;
}
else
{
lean_inc(v_x_571_);
return v_x_571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine___lam__1___boxed(lean_object* v_x_574_, lean_object* v_y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Omega_Constraint_combine___lam__1(v_x_574_, v_y_575_);
lean_dec(v_y_575_);
lean_dec(v_x_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_combine(lean_object* v_x_579_, lean_object* v_y_580_){
_start:
{
lean_object* v_lowerBound_581_; lean_object* v_upperBound_582_; lean_object* v_lowerBound_583_; lean_object* v_upperBound_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_595_; 
v_lowerBound_581_ = lean_ctor_get(v_x_579_, 0);
lean_inc(v_lowerBound_581_);
v_upperBound_582_ = lean_ctor_get(v_x_579_, 1);
lean_inc(v_upperBound_582_);
lean_dec_ref(v_x_579_);
v_lowerBound_583_ = lean_ctor_get(v_y_580_, 0);
v_upperBound_584_ = lean_ctor_get(v_y_580_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_y_580_);
if (v_isSharedCheck_595_ == 0)
{
v___x_586_ = v_y_580_;
v_isShared_587_ = v_isSharedCheck_595_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_upperBound_584_);
lean_inc(v_lowerBound_583_);
lean_dec(v_y_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_595_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___f_588_ = ((lean_object*)(l_Lean_Omega_Constraint_combine___closed__0));
v___f_589_ = ((lean_object*)(l_Lean_Omega_Constraint_combine___closed__1));
v___x_590_ = l_Option_merge___redArg(v___f_588_, v_lowerBound_581_, v_lowerBound_583_);
v___x_591_ = l_Option_merge___redArg(v___f_589_, v_upperBound_582_, v_upperBound_584_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v___x_591_);
lean_ctor_set(v___x_586_, 0, v___x_590_);
v___x_593_ = v___x_586_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Option_merge_match__1_splitter___redArg(lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_h__1_598_, lean_object* v_h__2_599_, lean_object* v_h__3_600_, lean_object* v_h__4_601_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
lean_dec(v_h__4_601_);
lean_dec(v_h__2_599_);
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_h__3_600_);
v___x_602_ = lean_box(0);
v___x_603_ = lean_apply_1(v_h__1_598_, v___x_602_);
return v___x_603_;
}
else
{
lean_object* v_val_604_; lean_object* v___x_605_; 
lean_dec(v_h__1_598_);
v_val_604_ = lean_ctor_get(v_x_597_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_x_597_, 1);
v___x_605_ = lean_apply_1(v_h__3_600_, v_val_604_);
return v___x_605_;
}
}
else
{
lean_dec(v_h__3_600_);
lean_dec(v_h__1_598_);
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v_val_606_; lean_object* v___x_607_; 
lean_dec(v_h__4_601_);
v_val_606_ = lean_ctor_get(v_x_596_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v_x_596_, 1);
v___x_607_ = lean_apply_1(v_h__2_599_, v_val_606_);
return v___x_607_;
}
else
{
lean_object* v_val_608_; lean_object* v_val_609_; lean_object* v___x_610_; 
lean_dec(v_h__2_599_);
v_val_608_ = lean_ctor_get(v_x_596_, 0);
lean_inc(v_val_608_);
lean_dec_ref_known(v_x_596_, 1);
v_val_609_ = lean_ctor_get(v_x_597_, 0);
lean_inc(v_val_609_);
lean_dec_ref_known(v_x_597_, 1);
v___x_610_ = lean_apply_2(v_h__4_601_, v_val_608_, v_val_609_);
return v___x_610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Option_merge_match__1_splitter(lean_object* v_00_u03b1_611_, lean_object* v_motive_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_, lean_object* v_h__3_617_, lean_object* v_h__4_618_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_dec(v_h__4_618_);
lean_dec(v_h__2_616_);
if (lean_obj_tag(v_x_614_) == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v_h__3_617_);
v___x_619_ = lean_box(0);
v___x_620_ = lean_apply_1(v_h__1_615_, v___x_619_);
return v___x_620_;
}
else
{
lean_object* v_val_621_; lean_object* v___x_622_; 
lean_dec(v_h__1_615_);
v_val_621_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_val_621_);
lean_dec_ref_known(v_x_614_, 1);
v___x_622_ = lean_apply_1(v_h__3_617_, v_val_621_);
return v___x_622_;
}
}
else
{
lean_dec(v_h__3_617_);
lean_dec(v_h__1_615_);
if (lean_obj_tag(v_x_614_) == 0)
{
lean_object* v_val_623_; lean_object* v___x_624_; 
lean_dec(v_h__4_618_);
v_val_623_ = lean_ctor_get(v_x_613_, 0);
lean_inc(v_val_623_);
lean_dec_ref_known(v_x_613_, 1);
v___x_624_ = lean_apply_1(v_h__2_616_, v_val_623_);
return v___x_624_;
}
else
{
lean_object* v_val_625_; lean_object* v_val_626_; lean_object* v___x_627_; 
lean_dec(v_h__2_616_);
v_val_625_ = lean_ctor_get(v_x_613_, 0);
lean_inc(v_val_625_);
lean_dec_ref_known(v_x_613_, 1);
v_val_626_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v_x_614_, 1);
v___x_627_ = lean_apply_2(v_h__4_618_, v_val_625_, v_val_626_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_div(lean_object* v_c_628_, lean_object* v_k_629_){
_start:
{
lean_object* v_lowerBound_630_; lean_object* v_upperBound_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_665_; 
v_lowerBound_630_ = lean_ctor_get(v_c_628_, 0);
v_upperBound_631_ = lean_ctor_get(v_c_628_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_c_628_);
if (v_isSharedCheck_665_ == 0)
{
v___x_633_ = v_c_628_;
v_isShared_634_ = v_isSharedCheck_665_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_upperBound_631_);
lean_inc(v_lowerBound_630_);
lean_dec(v_c_628_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_665_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___y_636_; 
if (lean_obj_tag(v_lowerBound_630_) == 0)
{
v___y_636_ = v_lowerBound_630_;
goto v___jp_635_;
}
else
{
lean_object* v_val_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_664_; 
v_val_653_ = lean_ctor_get(v_lowerBound_630_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_lowerBound_630_);
if (v_isSharedCheck_664_ == 0)
{
v___x_655_ = v_lowerBound_630_;
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_val_653_);
lean_dec(v_lowerBound_630_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_657_ = lean_int_neg(v_val_653_);
lean_dec(v_val_653_);
lean_inc(v_k_629_);
v___x_658_ = lean_nat_to_int(v_k_629_);
v___x_659_ = lean_int_ediv(v___x_657_, v___x_658_);
lean_dec(v___x_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_int_neg(v___x_659_);
lean_dec(v___x_659_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_660_);
v___x_662_ = v___x_655_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
v___y_636_ = v___x_662_;
goto v___jp_635_;
}
}
}
v___jp_635_:
{
if (lean_obj_tag(v_upperBound_631_) == 0)
{
lean_object* v___x_638_; 
lean_dec(v_k_629_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___y_636_);
v___x_638_ = v___x_633_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___y_636_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_upperBound_631_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
else
{
lean_object* v_val_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_652_; 
v_val_640_ = lean_ctor_get(v_upperBound_631_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v_upperBound_631_);
if (v_isSharedCheck_652_ == 0)
{
v___x_642_ = v_upperBound_631_;
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_val_640_);
lean_dec(v_upperBound_631_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_644_ = lean_nat_to_int(v_k_629_);
v___x_645_ = lean_int_ediv(v_val_640_, v___x_644_);
lean_dec(v___x_644_);
lean_dec(v_val_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_651_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_647_);
lean_ctor_set(v___x_633_, 0, v___y_636_);
v___x_649_ = v___x_633_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___y_636_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_Constraint_sat_x27(lean_object* v_c_666_, lean_object* v_x_667_, lean_object* v_y_668_){
_start:
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = l_Lean_Omega_IntList_dot(v_x_667_, v_y_668_);
v___x_670_ = l_Lean_Omega_Constraint_sat(v_c_666_, v___x_669_);
lean_dec(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Constraint_sat_x27___boxed(lean_object* v_c_671_, lean_object* v_x_672_, lean_object* v_y_673_){
_start:
{
uint8_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l_Lean_Omega_Constraint_sat_x27(v_c_671_, v_x_672_, v_y_673_);
lean_dec(v_x_672_);
lean_dec_ref(v_c_671_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_normalize_x3f(lean_object* v_x_676_){
_start:
{
lean_object* v_fst_677_; lean_object* v_snd_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_707_; 
v_fst_677_ = lean_ctor_get(v_x_676_, 0);
v_snd_678_ = lean_ctor_get(v_x_676_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_707_ == 0)
{
v___x_680_ = v_x_676_;
v_isShared_681_ = v_isSharedCheck_707_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_snd_678_);
lean_inc(v_fst_677_);
lean_dec(v_x_676_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_707_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_gcd_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_gcd_682_ = l_Lean_Omega_IntList_gcd(v_snd_678_);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_nat_dec_eq(v_gcd_682_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_dec_eq(v_gcd_682_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
lean_inc(v_gcd_682_);
v___x_687_ = l_Lean_Omega_Constraint_div(v_fst_677_, v_gcd_682_);
v___x_688_ = lean_nat_to_int(v_gcd_682_);
v___x_689_ = l_Lean_Omega_IntList_sdiv(v_snd_678_, v___x_688_);
lean_dec(v___x_688_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_689_);
lean_ctor_set(v___x_680_, 0, v___x_687_);
v___x_691_ = v___x_680_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_689_);
v___x_691_ = v_reuseFailAlloc_693_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; 
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
else
{
lean_object* v___x_694_; 
lean_dec(v_gcd_682_);
lean_del_object(v___x_680_);
lean_dec(v_snd_678_);
lean_dec(v_fst_677_);
v___x_694_ = lean_box(0);
return v___x_694_;
}
}
else
{
lean_object* v___x_695_; uint8_t v___x_696_; 
lean_dec(v_gcd_682_);
v___x_695_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_696_ = l_Lean_Omega_Constraint_sat(v_fst_677_, v___x_695_);
lean_dec(v_fst_677_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = l_Lean_Omega_Constraint_impossible;
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_697_);
v___x_699_ = v___x_680_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_snd_678_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; 
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
else
{
lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_702_ = ((lean_object*)(l_Lean_Omega_Constraint_trivial));
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_702_);
v___x_704_ = v___x_680_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_snd_678_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_normalize(lean_object* v_p_708_){
_start:
{
lean_object* v___x_709_; 
lean_inc_ref(v_p_708_);
v___x_709_ = l_Lean_Omega_normalize_x3f(v_p_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
return v_p_708_;
}
else
{
lean_object* v_val_710_; 
lean_dec_ref(v_p_708_);
v_val_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_val_710_);
lean_dec_ref_known(v___x_709_, 1);
return v_val_710_;
}
}
}
static lean_object* _init_l_Lean_Omega_positivize_x3f___closed__0(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_obj_once(&l_Lean_Omega_Constraint_impossible___closed__0, &l_Lean_Omega_Constraint_impossible___closed__0_once, _init_l_Lean_Omega_Constraint_impossible___closed__0);
v___x_712_ = lean_int_neg(v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_positivize_x3f(lean_object* v_x_713_){
_start:
{
lean_object* v_fst_714_; lean_object* v_snd_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_730_; 
v_fst_714_ = lean_ctor_get(v_x_713_, 0);
v_snd_715_ = lean_ctor_get(v_x_713_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_713_);
if (v_isSharedCheck_730_ == 0)
{
v___x_717_ = v_x_713_;
v_isShared_718_ = v_isSharedCheck_730_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_snd_715_);
lean_inc(v_fst_714_);
lean_dec(v_x_713_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_730_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = lean_obj_once(&l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_Constraint_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_720_ = l_Lean_Omega_IntList_leading(v_snd_715_);
v___x_721_ = lean_int_dec_le(v___x_719_, v___x_720_);
lean_dec(v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_722_ = l_Lean_Omega_Constraint_neg(v_fst_714_);
v___x_723_ = lean_obj_once(&l_Lean_Omega_positivize_x3f___closed__0, &l_Lean_Omega_positivize_x3f___closed__0_once, _init_l_Lean_Omega_positivize_x3f___closed__0);
v___x_724_ = l_Lean_Omega_IntList_smul(v_snd_715_, v___x_723_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v___x_724_);
lean_ctor_set(v___x_717_, 0, v___x_722_);
v___x_726_ = v___x_717_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_724_);
v___x_726_ = v_reuseFailAlloc_728_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
else
{
lean_object* v___x_729_; 
lean_del_object(v___x_717_);
lean_dec(v_snd_715_);
lean_dec(v_fst_714_);
v___x_729_ = lean_box(0);
return v___x_729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidy_x3f(lean_object* v_x_731_){
_start:
{
lean_object* v___x_732_; 
lean_inc_ref(v_x_731_);
v___x_732_ = l_Lean_Omega_positivize_x3f(v_x_731_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Omega_normalize_x3f(v_x_731_);
return v___x_733_;
}
else
{
lean_object* v_val_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v_x_731_);
v_val_734_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_742_ == 0)
{
v___x_736_ = v___x_732_;
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_val_734_);
lean_dec(v___x_732_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_738_ = l_Lean_Omega_normalize(v_val_734_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_738_);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidy(lean_object* v_p_743_){
_start:
{
lean_object* v___x_744_; 
lean_inc_ref(v_p_743_);
v___x_744_ = l_Lean_Omega_tidy_x3f(v_p_743_);
if (lean_obj_tag(v___x_744_) == 0)
{
return v_p_743_;
}
else
{
lean_object* v_val_745_; 
lean_dec_ref(v_p_743_);
v_val_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_val_745_);
lean_dec_ref_known(v___x_744_, 1);
return v_val_745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidyConstraint(lean_object* v_s_746_, lean_object* v_x_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_fst_750_; 
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v_s_746_);
lean_ctor_set(v___x_748_, 1, v_x_747_);
v___x_749_ = l_Lean_Omega_tidy(v___x_748_);
v_fst_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_fst_750_);
lean_dec_ref(v___x_749_);
return v_fst_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_tidyCoeffs(lean_object* v_s_751_, lean_object* v_x_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v_snd_755_; 
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_s_751_);
lean_ctor_set(v___x_753_, 1, v_x_752_);
v___x_754_ = l_Lean_Omega_tidy(v___x_753_);
v_snd_755_ = lean_ctor_get(v___x_754_, 1);
lean_inc(v_snd_755_);
lean_dec_ref(v___x_754_);
return v_snd_755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter___redArg(lean_object* v_x_756_, lean_object* v_h__1_757_, lean_object* v_h__2_758_){
_start:
{
if (lean_obj_tag(v_x_756_) == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec(v_h__2_758_);
v___x_759_ = lean_box(0);
v___x_760_ = lean_apply_1(v_h__1_757_, v___x_759_);
return v___x_760_;
}
else
{
lean_object* v_val_761_; lean_object* v_fst_762_; lean_object* v_snd_763_; lean_object* v___x_764_; 
lean_dec(v_h__1_757_);
v_val_761_ = lean_ctor_get(v_x_756_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v_x_756_, 1);
v_fst_762_ = lean_ctor_get(v_val_761_, 0);
lean_inc(v_fst_762_);
v_snd_763_ = lean_ctor_get(v_val_761_, 1);
lean_inc(v_snd_763_);
lean_dec(v_val_761_);
v___x_764_ = lean_apply_2(v_h__2_758_, v_fst_762_, v_snd_763_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Constraint_0__Lean_Omega_tidy_x3f_match__1_splitter(lean_object* v_motive_765_, lean_object* v_x_766_, lean_object* v_h__1_767_, lean_object* v_h__2_768_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec(v_h__2_768_);
v___x_769_ = lean_box(0);
v___x_770_ = lean_apply_1(v_h__1_767_, v___x_769_);
return v___x_770_;
}
else
{
lean_object* v_val_771_; lean_object* v_fst_772_; lean_object* v_snd_773_; lean_object* v___x_774_; 
lean_dec(v_h__1_767_);
v_val_771_ = lean_ctor_get(v_x_766_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v_x_766_, 1);
v_fst_772_ = lean_ctor_get(v_val_771_, 0);
lean_inc(v_fst_772_);
v_snd_773_ = lean_ctor_get(v_val_771_, 1);
lean_inc(v_snd_773_);
lean_dec(v_val_771_);
v___x_774_ = lean_apply_2(v_h__2_768_, v_fst_772_, v_snd_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term___lam__0(lean_object* v_m_775_, lean_object* v_x_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Int_bmod(v_x_776_, v_m_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term___lam__0___boxed(lean_object* v_m_778_, lean_object* v_x_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Omega_bmod__div__term___lam__0(v_m_778_, v_x_779_);
lean_dec(v_x_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__div__term(lean_object* v_m_781_, lean_object* v_a_782_, lean_object* v_b_783_){
_start:
{
lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_inc_n(v_m_781_, 2);
v___f_784_ = lean_alloc_closure((void*)(l_Lean_Omega_bmod__div__term___lam__0___boxed), 2, 1);
lean_closure_set(v___f_784_, 0, v_m_781_);
lean_inc(v_b_783_);
v___x_785_ = l_Lean_Omega_IntList_dot(v_a_782_, v_b_783_);
v___x_786_ = l_Int_bmod(v___x_785_, v_m_781_);
lean_dec(v___x_785_);
v___x_787_ = lean_box(0);
v___x_788_ = l_List_mapTR_loop___redArg(v___f_784_, v_a_782_, v___x_787_);
v___x_789_ = l_Lean_Omega_IntList_dot(v___x_788_, v_b_783_);
lean_dec(v___x_788_);
v___x_790_ = lean_int_sub(v___x_786_, v___x_789_);
lean_dec(v___x_789_);
lean_dec(v___x_786_);
v___x_791_ = lean_nat_to_int(v_m_781_);
v___x_792_ = lean_int_ediv(v___x_790_, v___x_791_);
lean_dec(v___x_791_);
lean_dec(v___x_790_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_bmod__coeffs_spec__0(lean_object* v_m_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
if (lean_obj_tag(v_a_794_) == 0)
{
lean_object* v___x_796_; 
lean_dec(v_m_793_);
v___x_796_ = l_List_reverse___redArg(v_a_795_);
return v___x_796_;
}
else
{
lean_object* v_head_797_; lean_object* v_tail_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_807_; 
v_head_797_ = lean_ctor_get(v_a_794_, 0);
v_tail_798_ = lean_ctor_get(v_a_794_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_a_794_);
if (v_isSharedCheck_807_ == 0)
{
v___x_800_ = v_a_794_;
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_tail_798_);
lean_inc(v_head_797_);
lean_dec(v_a_794_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_inc(v_m_793_);
v___x_802_ = l_Int_bmod(v_head_797_, v_m_793_);
lean_dec(v_head_797_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v_a_795_);
lean_ctor_set(v___x_800_, 0, v___x_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_a_795_);
v___x_804_ = v_reuseFailAlloc_806_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
v_a_794_ = v_tail_798_;
v_a_795_ = v___x_804_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__coeffs(lean_object* v_m_808_, lean_object* v_i_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_811_ = lean_box(0);
lean_inc(v_m_808_);
v___x_812_ = l_List_mapTR_loop___at___00Lean_Omega_bmod__coeffs_spec__0(v_m_808_, v_x_810_, v___x_811_);
v___x_813_ = lean_nat_to_int(v_m_808_);
v___x_814_ = l_Lean_Omega_IntList_set(v___x_812_, v_i_809_, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_bmod__coeffs___boxed(lean_object* v_m_815_, lean_object* v_i_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Omega_bmod__coeffs(v_m_815_, v_i_816_, v_x_817_);
lean_dec(v_i_816_);
return v_res_818_;
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
