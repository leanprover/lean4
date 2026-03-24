// Lean compiler output
// Module: Init.Omega.LinearCombo
// Imports: public import Init.Omega.Coeffs import Init.Data.Int.Lemmas import Init.Data.ToString.Macro import Init.RCases
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
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_sub(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Omega_IntList_dot(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_smul(lean_object*, lean_object*);
lean_object* l_String_Internal_append___boxed(lean_object*, lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_set(lean_object*, lean_object*, lean_object*);
lean_object* l_List_zipIdx___redArg(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Omega_IntList_neg(lean_object*);
lean_object* l_Lean_Omega_IntList_add(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Internal_append___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString___closed__0 = (const lean_object*)&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString = (const lean_object*)&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString___closed__0_value;
static lean_once_cell_t l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0;
static const lean_string_object l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1 = (const lean_object*)&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___closed__0 = (const lean_object*)&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt = (const lean_object*)&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___closed__0 = (const lean_object*)&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt = (const lean_object*)&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString__1 = (const lean_object*)&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqLinearCombo_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqLinearCombo_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqLinearCombo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqLinearCombo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Omega_instReprLinearCombo_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__5_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7;
static lean_once_cell_t l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "coeffs"};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10;
static const lean_string_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12;
static lean_once_cell_t l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13;
static const lean_ctor_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_instReprLinearCombo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_instReprLinearCombo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_instReprLinearCombo___closed__0 = (const lean_object*)&l_Lean_Omega_instReprLinearCombo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_instReprLinearCombo = (const lean_object*)&l_Lean_Omega_instReprLinearCombo___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___closed__0 = (const lean_object*)&l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___boxed(lean_object*);
static const lean_string_object l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " + "};
static const lean_object* l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__0 = (const lean_object*)&l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " * x"};
static const lean_object* l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__1 = (const lean_object*)&l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Omega_LinearCombo_instToString___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_LinearCombo_instToString___private__1___closed__0 = (const lean_object*)&l_Lean_Omega_LinearCombo_instToString___private__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_LinearCombo_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_LinearCombo_instToString___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Omega_LinearCombo_instToString___private__1___closed__0_value)} };
static const lean_object* l_Lean_Omega_LinearCombo_instToString___closed__0 = (const lean_object*)&l_Lean_Omega_LinearCombo_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_LinearCombo_instToString = (const lean_object*)&l_Lean_Omega_LinearCombo_instToString___closed__0_value;
static lean_once_cell_t l_Lean_Omega_LinearCombo_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_LinearCombo_instInhabited___closed__0;
static lean_once_cell_t l_Lean_Omega_LinearCombo_instInhabited___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_LinearCombo_instInhabited___closed__1;
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instInhabited;
LEAN_EXPORT uint8_t l_Lean_Omega_LinearCombo_isAtom___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_isAtom___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Omega_LinearCombo_isAtom_spec__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_LinearCombo_isAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_LinearCombo_isAtom___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_LinearCombo_isAtom___closed__0 = (const lean_object*)&l_Lean_Omega_LinearCombo_isAtom___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Omega_LinearCombo_isAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_isAtom___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_eval___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_coordinate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_coordinate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_add(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_LinearCombo_instAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_LinearCombo_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_LinearCombo_instAdd___closed__0 = (const lean_object*)&l_Lean_Omega_LinearCombo_instAdd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_LinearCombo_instAdd = (const lean_object*)&l_Lean_Omega_LinearCombo_instAdd___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_sub(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_LinearCombo_instSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_LinearCombo_sub, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_LinearCombo_instSub___closed__0 = (const lean_object*)&l_Lean_Omega_LinearCombo_instSub___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_LinearCombo_instSub = (const lean_object*)&l_Lean_Omega_LinearCombo_instSub___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_neg(lean_object*);
static const lean_closure_object l_Lean_Omega_LinearCombo_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_LinearCombo_neg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_LinearCombo_instNeg___closed__0 = (const lean_object*)&l_Lean_Omega_LinearCombo_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_LinearCombo_instNeg = (const lean_object*)&l_Lean_Omega_LinearCombo_instNeg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_smul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_smul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instHMulInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instHMulInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_LinearCombo_instHMulInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_LinearCombo_instHMulInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_LinearCombo_instHMulInt___closed__0 = (const lean_object*)&l_Lean_Omega_LinearCombo_instHMulInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_LinearCombo_instHMulInt = (const lean_object*)&l_Lean_Omega_LinearCombo_instHMulInt___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_mul(lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0(void){
_start:
{
lean_object* v_natZero_3_; lean_object* v_intZero_4_; 
v_natZero_3_ = lean_unsigned_to_nat(0u);
v_intZero_4_ = lean_nat_to_int(v_natZero_3_);
return v_intZero_4_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0(lean_object* v_x_6_){
_start:
{
lean_object* v_intZero_7_; uint8_t v_isNeg_8_; 
v_intZero_7_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_8_ = lean_int_dec_lt(v_x_6_, v_intZero_7_);
if (v_isNeg_8_ == 0)
{
lean_object* v_a_9_; lean_object* v___x_10_; 
v_a_9_ = lean_nat_abs(v_x_6_);
v___x_10_ = l_Nat_reprFast(v_a_9_);
return v___x_10_;
}
else
{
lean_object* v_abs_11_; lean_object* v_one_12_; lean_object* v_a_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_abs_11_ = lean_nat_abs(v_x_6_);
v_one_12_ = lean_unsigned_to_nat(1u);
v_a_13_ = lean_nat_sub(v_abs_11_, v_one_12_);
lean_dec(v_abs_11_);
v___x_14_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_15_ = lean_nat_add(v_a_13_, v_one_12_);
lean_dec(v_a_13_);
v___x_16_ = l_Nat_reprFast(v___x_15_);
v___x_17_ = lean_string_append(v___x_14_, v___x_16_);
lean_dec_ref(v___x_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___boxed(lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0(v_x_18_);
lean_dec(v_x_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___lam__0(lean_object* v_i_22_, lean_object* v_prec_23_){
_start:
{
lean_object* v___y_25_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_28_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_29_ = lean_int_dec_lt(v_i_22_, v___x_28_);
if (v___x_29_ == 0)
{
if (v___x_29_ == 0)
{
lean_object* v_a_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_a_30_ = lean_nat_abs(v_i_22_);
v___x_31_ = l_Nat_reprFast(v_a_30_);
v___x_32_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
else
{
lean_object* v_abs_33_; lean_object* v_one_34_; lean_object* v_a_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_abs_33_ = lean_nat_abs(v_i_22_);
v_one_34_ = lean_unsigned_to_nat(1u);
v_a_35_ = lean_nat_sub(v_abs_33_, v_one_34_);
lean_dec(v_abs_33_);
v___x_36_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_37_ = lean_nat_add(v_a_35_, v_one_34_);
lean_dec(v_a_35_);
v___x_38_ = l_Nat_reprFast(v___x_37_);
v___x_39_ = lean_string_append(v___x_36_, v___x_38_);
lean_dec_ref(v___x_38_);
v___x_40_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
}
else
{
if (v___x_29_ == 0)
{
lean_object* v_a_41_; lean_object* v___x_42_; 
v_a_41_ = lean_nat_abs(v_i_22_);
v___x_42_ = l_Nat_reprFast(v_a_41_);
v___y_25_ = v___x_42_;
goto v___jp_24_;
}
else
{
lean_object* v_abs_43_; lean_object* v_one_44_; lean_object* v_a_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_abs_43_ = lean_nat_abs(v_i_22_);
v_one_44_ = lean_unsigned_to_nat(1u);
v_a_45_ = lean_nat_sub(v_abs_43_, v_one_44_);
lean_dec(v_abs_43_);
v___x_46_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_47_ = lean_nat_add(v_a_45_, v_one_44_);
lean_dec(v_a_45_);
v___x_48_ = l_Nat_reprFast(v___x_47_);
v___x_49_ = lean_string_append(v___x_46_, v___x_48_);
lean_dec_ref(v___x_48_);
v___y_25_ = v___x_49_;
goto v___jp_24_;
}
}
v___jp_24_:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_26_, 0, v___y_25_);
v___x_27_ = l_Repr_addAppParen(v___x_26_, v_prec_23_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___lam__0___boxed(lean_object* v_i_50_, lean_object* v_prec_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___lam__0(v_i_50_, v_prec_51_);
lean_dec(v_prec_51_);
lean_dec(v_i_50_);
return v_res_52_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqLinearCombo_decEq(lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
lean_object* v_const_58_; lean_object* v_coeffs_59_; lean_object* v_const_60_; lean_object* v_coeffs_61_; uint8_t v___x_62_; 
v_const_58_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_const_58_);
v_coeffs_59_ = lean_ctor_get(v_x_56_, 1);
lean_inc(v_coeffs_59_);
lean_dec_ref(v_x_56_);
v_const_60_ = lean_ctor_get(v_x_57_, 0);
lean_inc(v_const_60_);
v_coeffs_61_ = lean_ctor_get(v_x_57_, 1);
lean_inc(v_coeffs_61_);
lean_dec_ref(v_x_57_);
v___x_62_ = lean_int_dec_eq(v_const_58_, v_const_60_);
lean_dec(v_const_60_);
lean_dec(v_const_58_);
if (v___x_62_ == 0)
{
lean_dec(v_coeffs_61_);
lean_dec(v_coeffs_59_);
return v___x_62_;
}
else
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_64_ = l_instDecidableEqList___redArg(v___x_63_, v_coeffs_59_, v_coeffs_61_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqLinearCombo_decEq___boxed(lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Lean_Omega_instDecidableEqLinearCombo_decEq(v_x_65_, v_x_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqLinearCombo(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = l_Lean_Omega_instDecidableEqLinearCombo_decEq(v_x_69_, v_x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqLinearCombo___boxed(lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_Lean_Omega_instDecidableEqLinearCombo(v_x_72_, v_x_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Omega_instReprLinearCombo_repr_spec__1(lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_nat_to_int(v_a_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_dec(v_x_78_);
return v_x_79_;
}
else
{
lean_object* v_head_81_; lean_object* v_tail_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_122_; 
v_head_81_ = lean_ctor_get(v_x_80_, 0);
v_tail_82_ = lean_ctor_get(v_x_80_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_122_ == 0)
{
v___x_84_ = v_x_80_;
v_isShared_85_ = v_isSharedCheck_122_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_tail_82_);
lean_inc(v_head_81_);
lean_dec(v_x_80_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_122_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
lean_inc(v_x_78_);
if (v_isShared_85_ == 0)
{
lean_ctor_set_tag(v___x_84_, 5);
lean_ctor_set(v___x_84_, 1, v_x_78_);
lean_ctor_set(v___x_84_, 0, v_x_79_);
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_x_79_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_x_78_);
v___x_87_ = v_reuseFailAlloc_121_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___y_90_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_96_ = lean_int_dec_lt(v_head_81_, v___x_95_);
if (v___x_96_ == 0)
{
if (v___x_96_ == 0)
{
lean_object* v_a_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_a_97_ = lean_nat_abs(v_head_81_);
lean_dec(v_head_81_);
v___x_98_ = l_Nat_reprFast(v_a_97_);
v___x_99_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
v___x_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_87_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v_x_79_ = v___x_100_;
v_x_80_ = v_tail_82_;
goto _start;
}
else
{
lean_object* v_abs_102_; lean_object* v_one_103_; lean_object* v_a_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_abs_102_ = lean_nat_abs(v_head_81_);
lean_dec(v_head_81_);
v_one_103_ = lean_unsigned_to_nat(1u);
v_a_104_ = lean_nat_sub(v_abs_102_, v_one_103_);
lean_dec(v_abs_102_);
v___x_105_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_106_ = lean_nat_add(v_a_104_, v_one_103_);
lean_dec(v_a_104_);
v___x_107_ = l_Nat_reprFast(v___x_106_);
v___x_108_ = lean_string_append(v___x_105_, v___x_107_);
lean_dec_ref(v___x_107_);
v___x_109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_87_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v_x_79_ = v___x_110_;
v_x_80_ = v_tail_82_;
goto _start;
}
}
else
{
if (v___x_96_ == 0)
{
lean_object* v_a_112_; lean_object* v___x_113_; 
v_a_112_ = lean_nat_abs(v_head_81_);
lean_dec(v_head_81_);
v___x_113_ = l_Nat_reprFast(v_a_112_);
v___y_90_ = v___x_113_;
goto v___jp_89_;
}
else
{
lean_object* v_abs_114_; lean_object* v_one_115_; lean_object* v_a_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_abs_114_ = lean_nat_abs(v_head_81_);
lean_dec(v_head_81_);
v_one_115_ = lean_unsigned_to_nat(1u);
v_a_116_ = lean_nat_sub(v_abs_114_, v_one_115_);
lean_dec(v_abs_114_);
v___x_117_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_118_ = lean_nat_add(v_a_116_, v_one_115_);
lean_dec(v_a_116_);
v___x_119_ = l_Nat_reprFast(v___x_118_);
v___x_120_ = lean_string_append(v___x_117_, v___x_119_);
lean_dec_ref(v___x_119_);
v___y_90_ = v___x_120_;
goto v___jp_89_;
}
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_91_, 0, v___y_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v___x_88_);
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_87_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v_x_79_ = v___x_93_;
v_x_80_ = v_tail_82_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2(lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_dec(v_x_123_);
return v_x_124_;
}
else
{
lean_object* v_head_126_; lean_object* v_tail_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_167_; 
v_head_126_ = lean_ctor_get(v_x_125_, 0);
v_tail_127_ = lean_ctor_get(v_x_125_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_167_ == 0)
{
v___x_129_ = v_x_125_;
v_isShared_130_ = v_isSharedCheck_167_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_tail_127_);
lean_inc(v_head_126_);
lean_dec(v_x_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_167_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
lean_inc(v_x_123_);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 5);
lean_ctor_set(v___x_129_, 1, v_x_123_);
lean_ctor_set(v___x_129_, 0, v_x_124_);
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_x_124_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_x_123_);
v___x_132_ = v_reuseFailAlloc_166_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v___y_135_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_140_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_141_ = lean_int_dec_lt(v_head_126_, v___x_140_);
if (v___x_141_ == 0)
{
if (v___x_141_ == 0)
{
lean_object* v_a_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_a_142_ = lean_nat_abs(v_head_126_);
lean_dec(v_head_126_);
v___x_143_ = l_Nat_reprFast(v_a_142_);
v___x_144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
v___x_145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_132_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_123_, v___x_145_, v_tail_127_);
return v___x_146_;
}
else
{
lean_object* v_abs_147_; lean_object* v_one_148_; lean_object* v_a_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_abs_147_ = lean_nat_abs(v_head_126_);
lean_dec(v_head_126_);
v_one_148_ = lean_unsigned_to_nat(1u);
v_a_149_ = lean_nat_sub(v_abs_147_, v_one_148_);
lean_dec(v_abs_147_);
v___x_150_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_151_ = lean_nat_add(v_a_149_, v_one_148_);
lean_dec(v_a_149_);
v___x_152_ = l_Nat_reprFast(v___x_151_);
v___x_153_ = lean_string_append(v___x_150_, v___x_152_);
lean_dec_ref(v___x_152_);
v___x_154_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_132_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_123_, v___x_155_, v_tail_127_);
return v___x_156_;
}
}
else
{
if (v___x_141_ == 0)
{
lean_object* v_a_157_; lean_object* v___x_158_; 
v_a_157_ = lean_nat_abs(v_head_126_);
lean_dec(v_head_126_);
v___x_158_ = l_Nat_reprFast(v_a_157_);
v___y_135_ = v___x_158_;
goto v___jp_134_;
}
else
{
lean_object* v_abs_159_; lean_object* v_one_160_; lean_object* v_a_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_abs_159_ = lean_nat_abs(v_head_126_);
lean_dec(v_head_126_);
v_one_160_ = lean_unsigned_to_nat(1u);
v_a_161_ = lean_nat_sub(v_abs_159_, v_one_160_);
lean_dec(v_abs_159_);
v___x_162_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_163_ = lean_nat_add(v_a_161_, v_one_160_);
lean_dec(v_a_161_);
v___x_164_ = l_Nat_reprFast(v___x_163_);
v___x_165_ = lean_string_append(v___x_162_, v___x_164_);
lean_dec_ref(v___x_164_);
v___y_135_ = v___x_165_;
goto v___jp_134_;
}
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_136_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_136_, 0, v___y_135_);
v___x_137_ = l_Repr_addAppParen(v___x_136_, v___x_133_);
v___x_138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_132_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_123_, v___x_138_, v_tail_127_);
return v___x_139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(lean_object* v___y_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___y_171_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_175_ = lean_int_dec_lt(v___y_168_, v___x_174_);
if (v___x_175_ == 0)
{
if (v___x_175_ == 0)
{
lean_object* v_a_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_a_176_ = lean_nat_abs(v___y_168_);
v___x_177_ = l_Nat_reprFast(v_a_176_);
v___x_178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
else
{
lean_object* v_abs_179_; lean_object* v_one_180_; lean_object* v_a_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_abs_179_ = lean_nat_abs(v___y_168_);
v_one_180_ = lean_unsigned_to_nat(1u);
v_a_181_ = lean_nat_sub(v_abs_179_, v_one_180_);
lean_dec(v_abs_179_);
v___x_182_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_183_ = lean_nat_add(v_a_181_, v_one_180_);
lean_dec(v_a_181_);
v___x_184_ = l_Nat_reprFast(v___x_183_);
v___x_185_ = lean_string_append(v___x_182_, v___x_184_);
lean_dec_ref(v___x_184_);
v___x_186_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
else
{
if (v___x_175_ == 0)
{
lean_object* v_a_187_; lean_object* v___x_188_; 
v_a_187_ = lean_nat_abs(v___y_168_);
v___x_188_ = l_Nat_reprFast(v_a_187_);
v___y_171_ = v___x_188_;
goto v___jp_170_;
}
else
{
lean_object* v_abs_189_; lean_object* v_one_190_; lean_object* v_a_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_abs_189_ = lean_nat_abs(v___y_168_);
v_one_190_ = lean_unsigned_to_nat(1u);
v_a_191_ = lean_nat_sub(v_abs_189_, v_one_190_);
lean_dec(v_abs_189_);
v___x_192_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_193_ = lean_nat_add(v_a_191_, v_one_190_);
lean_dec(v_a_191_);
v___x_194_ = l_Nat_reprFast(v___x_193_);
v___x_195_ = lean_string_append(v___x_192_, v___x_194_);
lean_dec_ref(v___x_194_);
v___y_171_ = v___x_195_;
goto v___jp_170_;
}
}
v___jp_170_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_172_, 0, v___y_171_);
v___x_173_ = l_Repr_addAppParen(v___x_172_, v___x_169_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0___boxed(lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v___y_196_);
lean_dec(v___y_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0(lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
lean_object* v___x_200_; 
lean_dec(v_x_199_);
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
lean_object* v_tail_201_; 
v_tail_201_ = lean_ctor_get(v_x_198_, 1);
if (lean_obj_tag(v_tail_201_) == 0)
{
lean_object* v_head_202_; lean_object* v___x_203_; 
lean_dec(v_x_199_);
v_head_202_ = lean_ctor_get(v_x_198_, 0);
lean_inc(v_head_202_);
lean_dec_ref(v_x_198_);
v___x_203_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v_head_202_);
lean_dec(v_head_202_);
return v___x_203_;
}
else
{
lean_object* v_head_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
lean_inc(v_tail_201_);
v_head_204_ = lean_ctor_get(v_x_198_, 0);
lean_inc(v_head_204_);
lean_dec_ref(v_x_198_);
v___x_205_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v_head_204_);
lean_dec(v_head_204_);
v___x_206_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2(v_x_199_, v___x_205_, v_tail_201_);
return v___x_206_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2));
v___x_219_ = lean_string_length(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7);
v___x_221_ = lean_nat_to_int(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(lean_object* v_a_226_){
_start:
{
if (lean_obj_tag(v_a_226_) == 0)
{
lean_object* v___x_227_; 
v___x_227_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__1));
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_228_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__5));
v___x_229_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0(v_a_226_, v___x_228_);
v___x_230_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8);
v___x_231_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__9));
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_229_);
v___x_233_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__10));
v___x_234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_230_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = l_Std_Format_fill(v___x_235_);
return v___x_236_;
}
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_unsigned_to_nat(9u);
v___x_251_ = lean_nat_to_int(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(10u);
v___x_256_ = lean_nat_to_int(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0));
v___x_259_ = lean_string_length(v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12);
v___x_261_ = lean_nat_to_int(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg(lean_object* v_x_266_){
_start:
{
lean_object* v_const_267_; lean_object* v_coeffs_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_329_; 
v_const_267_ = lean_ctor_get(v_x_266_, 0);
v_coeffs_268_ = lean_ctor_get(v_x_266_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_266_);
if (v_isSharedCheck_329_ == 0)
{
v___x_270_ = v_x_266_;
v_isShared_271_ = v_isSharedCheck_329_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_coeffs_268_);
lean_inc(v_const_267_);
lean_dec(v_x_266_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_329_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___y_276_; lean_object* v___x_302_; lean_object* v___y_304_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_272_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5));
v___x_273_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__6));
v___x_274_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_308_ = lean_int_dec_lt(v_const_267_, v___x_307_);
if (v___x_308_ == 0)
{
if (v___x_308_ == 0)
{
lean_object* v_a_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_a_309_ = lean_nat_abs(v_const_267_);
lean_dec(v_const_267_);
v___x_310_ = l_Nat_reprFast(v_a_309_);
v___x_311_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
v___y_276_ = v___x_311_;
goto v___jp_275_;
}
else
{
lean_object* v_abs_312_; lean_object* v_one_313_; lean_object* v_a_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_abs_312_ = lean_nat_abs(v_const_267_);
lean_dec(v_const_267_);
v_one_313_ = lean_unsigned_to_nat(1u);
v_a_314_ = lean_nat_sub(v_abs_312_, v_one_313_);
lean_dec(v_abs_312_);
v___x_315_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_316_ = lean_nat_add(v_a_314_, v_one_313_);
lean_dec(v_a_314_);
v___x_317_ = l_Nat_reprFast(v___x_316_);
v___x_318_ = lean_string_append(v___x_315_, v___x_317_);
lean_dec_ref(v___x_317_);
v___x_319_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
v___y_276_ = v___x_319_;
goto v___jp_275_;
}
}
else
{
if (v___x_308_ == 0)
{
lean_object* v_a_320_; lean_object* v___x_321_; 
v_a_320_ = lean_nat_abs(v_const_267_);
lean_dec(v_const_267_);
v___x_321_ = l_Nat_reprFast(v_a_320_);
v___y_304_ = v___x_321_;
goto v___jp_303_;
}
else
{
lean_object* v_abs_322_; lean_object* v_one_323_; lean_object* v_a_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_abs_322_ = lean_nat_abs(v_const_267_);
lean_dec(v_const_267_);
v_one_323_ = lean_unsigned_to_nat(1u);
v_a_324_ = lean_nat_sub(v_abs_322_, v_one_323_);
lean_dec(v_abs_322_);
v___x_325_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_326_ = lean_nat_add(v_a_324_, v_one_323_);
lean_dec(v_a_324_);
v___x_327_ = l_Nat_reprFast(v___x_326_);
v___x_328_ = lean_string_append(v___x_325_, v___x_327_);
lean_dec_ref(v___x_327_);
v___y_304_ = v___x_328_;
goto v___jp_303_;
}
}
v___jp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_271_ == 0)
{
lean_ctor_set_tag(v___x_270_, 4);
lean_ctor_set(v___x_270_, 1, v___y_276_);
lean_ctor_set(v___x_270_, 0, v___x_274_);
v___x_278_ = v___x_270_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___y_276_);
v___x_278_ = v_reuseFailAlloc_301_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_279_ = 0;
v___x_280_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set_uint8(v___x_280_, sizeof(void*)*1, v___x_279_);
v___x_281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_273_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4));
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_box(1);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__9));
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_272_);
v___x_289_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10);
v___x_290_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(v_coeffs_268_);
v___x_291_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*1, v___x_279_);
v___x_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_288_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13);
v___x_295_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__14));
v___x_296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_293_);
v___x_297_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__15));
v___x_298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_294_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set_uint8(v___x_300_, sizeof(void*)*1, v___x_279_);
return v___x_300_;
}
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_305_, 0, v___y_304_);
v___x_306_ = l_Repr_addAppParen(v___x_305_, v___x_302_);
v___y_276_ = v___x_306_;
goto v___jp_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr(lean_object* v_x_330_, lean_object* v_prec_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Omega_instReprLinearCombo_repr___redArg(v_x_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr___boxed(lean_object* v_x_333_, lean_object* v_prec_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Omega_instReprLinearCombo_repr(v_x_333_, v_prec_334_);
lean_dec(v_prec_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0(lean_object* v_a_336_, lean_object* v_n_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(v_a_336_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___boxed(lean_object* v_a_339_, lean_object* v_n_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0(v_a_339_, v_n_340_);
lean_dec(v_n_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_345_) == 0)
{
return v_x_344_;
}
else
{
lean_object* v_head_346_; lean_object* v_tail_347_; lean_object* v___x_348_; 
v_head_346_ = lean_ctor_get(v_x_345_, 0);
v_tail_347_ = lean_ctor_get(v_x_345_, 1);
v___x_348_ = lean_string_append(v_x_344_, v_head_346_);
v_x_344_ = v___x_348_;
v_x_345_ = v_tail_347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0___boxed(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(v_x_350_, v_x_351_);
lean_dec(v_x_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(lean_object* v_l_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___closed__0));
v___x_356_ = l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(v___x_355_, v_l_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___boxed(lean_object* v_l_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v_l_357_);
lean_dec(v_l_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1___lam__0(lean_object* v_x_361_){
_start:
{
lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_364_; lean_object* v___y_366_; lean_object* v_intZero_374_; uint8_t v_isNeg_375_; 
v_fst_362_ = lean_ctor_get(v_x_361_, 0);
v_snd_363_ = lean_ctor_get(v_x_361_, 1);
v___x_364_ = ((lean_object*)(l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__0));
v_intZero_374_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_375_ = lean_int_dec_lt(v_fst_362_, v_intZero_374_);
if (v_isNeg_375_ == 0)
{
lean_object* v_a_376_; lean_object* v___x_377_; 
v_a_376_ = lean_nat_abs(v_fst_362_);
v___x_377_ = l_Nat_reprFast(v_a_376_);
v___y_366_ = v___x_377_;
goto v___jp_365_;
}
else
{
lean_object* v_abs_378_; lean_object* v_one_379_; lean_object* v_a_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_abs_378_ = lean_nat_abs(v_fst_362_);
v_one_379_ = lean_unsigned_to_nat(1u);
v_a_380_ = lean_nat_sub(v_abs_378_, v_one_379_);
lean_dec(v_abs_378_);
v___x_381_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_382_ = lean_nat_add(v_a_380_, v_one_379_);
lean_dec(v_a_380_);
v___x_383_ = l_Nat_reprFast(v___x_382_);
v___x_384_ = lean_string_append(v___x_381_, v___x_383_);
lean_dec_ref(v___x_383_);
v___y_366_ = v___x_384_;
goto v___jp_365_;
}
v___jp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_367_ = lean_string_append(v___x_364_, v___y_366_);
lean_dec_ref(v___y_366_);
v___x_368_ = ((lean_object*)(l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__1));
v___x_369_ = lean_string_append(v___x_367_, v___x_368_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v_snd_363_, v___x_370_);
v___x_372_ = l_Nat_reprFast(v___x_371_);
v___x_373_ = lean_string_append(v___x_369_, v___x_372_);
lean_dec_ref(v___x_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___boxed(lean_object* v_x_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Omega_LinearCombo_instToString___private__1___lam__0(v_x_385_);
lean_dec_ref(v_x_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1(lean_object* v_lc_388_){
_start:
{
lean_object* v_const_389_; lean_object* v_coeffs_390_; lean_object* v___f_391_; lean_object* v___y_393_; lean_object* v_intZero_400_; uint8_t v_isNeg_401_; 
v_const_389_ = lean_ctor_get(v_lc_388_, 0);
lean_inc(v_const_389_);
v_coeffs_390_ = lean_ctor_get(v_lc_388_, 1);
lean_inc(v_coeffs_390_);
lean_dec_ref(v_lc_388_);
v___f_391_ = ((lean_object*)(l_Lean_Omega_LinearCombo_instToString___private__1___closed__0));
v_intZero_400_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_401_ = lean_int_dec_lt(v_const_389_, v_intZero_400_);
if (v_isNeg_401_ == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; 
v_a_402_ = lean_nat_abs(v_const_389_);
lean_dec(v_const_389_);
v___x_403_ = l_Nat_reprFast(v_a_402_);
v___y_393_ = v___x_403_;
goto v___jp_392_;
}
else
{
lean_object* v_abs_404_; lean_object* v_one_405_; lean_object* v_a_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_abs_404_ = lean_nat_abs(v_const_389_);
lean_dec(v_const_389_);
v_one_405_ = lean_unsigned_to_nat(1u);
v_a_406_ = lean_nat_sub(v_abs_404_, v_one_405_);
lean_dec(v_abs_404_);
v___x_407_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_408_ = lean_nat_add(v_a_406_, v_one_405_);
lean_dec(v_a_406_);
v___x_409_ = l_Nat_reprFast(v___x_408_);
v___x_410_ = lean_string_append(v___x_407_, v___x_409_);
lean_dec_ref(v___x_409_);
v___y_393_ = v___x_410_;
goto v___jp_392_;
}
v___jp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = l_List_zipIdx___redArg(v_coeffs_390_, v___x_394_);
v___x_396_ = lean_box(0);
v___x_397_ = l_List_mapTR_loop___redArg(v___f_391_, v___x_395_, v___x_396_);
v___x_398_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v___x_397_);
lean_dec(v___x_397_);
v___x_399_ = lean_string_append(v___y_393_, v___x_398_);
lean_dec_ref(v___x_398_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___lam__1(lean_object* v___f_411_, lean_object* v_lc_412_){
_start:
{
lean_object* v_const_413_; lean_object* v_coeffs_414_; lean_object* v___y_416_; lean_object* v_intZero_423_; uint8_t v_isNeg_424_; 
v_const_413_ = lean_ctor_get(v_lc_412_, 0);
lean_inc(v_const_413_);
v_coeffs_414_ = lean_ctor_get(v_lc_412_, 1);
lean_inc(v_coeffs_414_);
lean_dec_ref(v_lc_412_);
v_intZero_423_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_424_ = lean_int_dec_lt(v_const_413_, v_intZero_423_);
if (v_isNeg_424_ == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; 
v_a_425_ = lean_nat_abs(v_const_413_);
lean_dec(v_const_413_);
v___x_426_ = l_Nat_reprFast(v_a_425_);
v___y_416_ = v___x_426_;
goto v___jp_415_;
}
else
{
lean_object* v_abs_427_; lean_object* v_one_428_; lean_object* v_a_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_abs_427_ = lean_nat_abs(v_const_413_);
lean_dec(v_const_413_);
v_one_428_ = lean_unsigned_to_nat(1u);
v_a_429_ = lean_nat_sub(v_abs_427_, v_one_428_);
lean_dec(v_abs_427_);
v___x_430_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_431_ = lean_nat_add(v_a_429_, v_one_428_);
lean_dec(v_a_429_);
v___x_432_ = l_Nat_reprFast(v___x_431_);
v___x_433_ = lean_string_append(v___x_430_, v___x_432_);
lean_dec_ref(v___x_432_);
v___y_416_ = v___x_433_;
goto v___jp_415_;
}
v___jp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = l_List_zipIdx___redArg(v_coeffs_414_, v___x_417_);
v___x_419_ = lean_box(0);
v___x_420_ = l_List_mapTR_loop___redArg(v___f_411_, v___x_418_, v___x_419_);
v___x_421_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v___x_420_);
lean_dec(v___x_420_);
v___x_422_ = lean_string_append(v___y_416_, v___x_421_);
lean_dec_ref(v___x_421_);
return v___x_422_;
}
}
}
static lean_object* _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_to_int(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Omega_LinearCombo_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_box(0);
v___x_440_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_Omega_LinearCombo_instInhabited(void){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__1, &l_Lean_Omega_LinearCombo_instInhabited___closed__1_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__1);
return v___x_442_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_LinearCombo_isAtom___lam__0(lean_object* v_c_443_){
_start:
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_445_ = lean_int_dec_eq(v_c_443_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_447_ = lean_int_dec_eq(v_c_443_, v___x_446_);
return v___x_447_;
}
else
{
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_isAtom___lam__0___boxed(lean_object* v_c_448_){
_start:
{
uint8_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_Lean_Omega_LinearCombo_isAtom___lam__0(v_c_448_);
lean_dec(v_c_448_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Omega_LinearCombo_isAtom_spec__0(lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
if (lean_obj_tag(v_a_451_) == 0)
{
lean_object* v___x_453_; 
v___x_453_ = l_List_reverse___redArg(v_a_452_);
return v___x_453_;
}
else
{
lean_object* v_head_454_; lean_object* v_tail_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_466_; 
v_head_454_ = lean_ctor_get(v_a_451_, 0);
v_tail_455_ = lean_ctor_get(v_a_451_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_466_ == 0)
{
v___x_457_ = v_a_451_;
v_isShared_458_ = v_isSharedCheck_466_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_tail_455_);
lean_inc(v_head_454_);
lean_dec(v_a_451_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_466_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_460_ = lean_int_dec_eq(v_head_454_, v___x_459_);
if (v___x_460_ == 0)
{
lean_del_object(v___x_457_);
lean_dec(v_head_454_);
v_a_451_ = v_tail_455_;
goto _start;
}
else
{
lean_object* v___x_463_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v_a_452_);
v___x_463_ = v___x_457_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_head_454_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_a_452_);
v___x_463_ = v_reuseFailAlloc_465_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
v_a_451_ = v_tail_455_;
v_a_452_ = v___x_463_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_LinearCombo_isAtom(lean_object* v_a_468_){
_start:
{
lean_object* v_const_469_; lean_object* v_coeffs_470_; lean_object* v___f_471_; uint8_t v___y_473_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_const_469_ = lean_ctor_get(v_a_468_, 0);
lean_inc(v_const_469_);
v_coeffs_470_ = lean_ctor_get(v_a_468_, 1);
lean_inc(v_coeffs_470_);
lean_dec_ref(v_a_468_);
v___f_471_ = ((lean_object*)(l_Lean_Omega_LinearCombo_isAtom___closed__0));
v___x_475_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_476_ = lean_int_dec_eq(v_const_469_, v___x_475_);
lean_dec(v_const_469_);
if (v___x_476_ == 0)
{
v___y_473_ = v___x_476_;
goto v___jp_472_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_477_ = lean_box(0);
lean_inc(v_coeffs_470_);
v___x_478_ = l_List_filterTR_loop___at___00Lean_Omega_LinearCombo_isAtom_spec__0(v_coeffs_470_, v___x_477_);
v___x_479_ = l_List_lengthTR___redArg(v___x_478_);
lean_dec(v___x_478_);
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_dec_eq(v___x_479_, v___x_480_);
lean_dec(v___x_479_);
v___y_473_ = v___x_481_;
goto v___jp_472_;
}
v___jp_472_:
{
if (v___y_473_ == 0)
{
lean_dec(v_coeffs_470_);
return v___y_473_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = l_List_all___redArg(v_coeffs_470_, v___f_471_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_isAtom___boxed(lean_object* v_a_482_){
_start:
{
uint8_t v_res_483_; lean_object* v_r_484_; 
v_res_483_ = l_Lean_Omega_LinearCombo_isAtom(v_a_482_);
v_r_484_ = lean_box(v_res_483_);
return v_r_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_eval(lean_object* v_lc_485_, lean_object* v_values_486_){
_start:
{
lean_object* v_const_487_; lean_object* v_coeffs_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_const_487_ = lean_ctor_get(v_lc_485_, 0);
v_coeffs_488_ = lean_ctor_get(v_lc_485_, 1);
v___x_489_ = l_Lean_Omega_IntList_dot(v_coeffs_488_, v_values_486_);
v___x_490_ = lean_int_add(v_const_487_, v___x_489_);
lean_dec(v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_eval___boxed(lean_object* v_lc_491_, lean_object* v_values_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Omega_LinearCombo_eval(v_lc_491_, v_values_492_);
lean_dec_ref(v_lc_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_coordinate(lean_object* v_i_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_495_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_496_ = lean_box(0);
v___x_497_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_498_ = l_Lean_Omega_IntList_set(v___x_496_, v_i_494_, v___x_497_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_495_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_coordinate___boxed(lean_object* v_i_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Omega_LinearCombo_coordinate(v_i_500_);
lean_dec(v_i_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_add(lean_object* v_l_u2081_502_, lean_object* v_l_u2082_503_){
_start:
{
lean_object* v_const_504_; lean_object* v_coeffs_505_; lean_object* v_const_506_; lean_object* v_coeffs_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_516_; 
v_const_504_ = lean_ctor_get(v_l_u2081_502_, 0);
lean_inc(v_const_504_);
v_coeffs_505_ = lean_ctor_get(v_l_u2081_502_, 1);
lean_inc(v_coeffs_505_);
lean_dec_ref(v_l_u2081_502_);
v_const_506_ = lean_ctor_get(v_l_u2082_503_, 0);
v_coeffs_507_ = lean_ctor_get(v_l_u2082_503_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_l_u2082_503_);
if (v_isSharedCheck_516_ == 0)
{
v___x_509_ = v_l_u2082_503_;
v_isShared_510_ = v_isSharedCheck_516_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_coeffs_507_);
lean_inc(v_const_506_);
lean_dec(v_l_u2082_503_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_516_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_511_ = lean_int_add(v_const_504_, v_const_506_);
lean_dec(v_const_506_);
lean_dec(v_const_504_);
v___x_512_ = l_Lean_Omega_IntList_add(v_coeffs_505_, v_coeffs_507_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_512_);
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_514_ = v___x_509_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_sub(lean_object* v_l_u2081_519_, lean_object* v_l_u2082_520_){
_start:
{
lean_object* v_const_521_; lean_object* v_coeffs_522_; lean_object* v_const_523_; lean_object* v_coeffs_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_533_; 
v_const_521_ = lean_ctor_get(v_l_u2081_519_, 0);
lean_inc(v_const_521_);
v_coeffs_522_ = lean_ctor_get(v_l_u2081_519_, 1);
lean_inc(v_coeffs_522_);
lean_dec_ref(v_l_u2081_519_);
v_const_523_ = lean_ctor_get(v_l_u2082_520_, 0);
v_coeffs_524_ = lean_ctor_get(v_l_u2082_520_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_l_u2082_520_);
if (v_isSharedCheck_533_ == 0)
{
v___x_526_ = v_l_u2082_520_;
v_isShared_527_ = v_isSharedCheck_533_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_coeffs_524_);
lean_inc(v_const_523_);
lean_dec(v_l_u2082_520_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_533_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_528_ = lean_int_sub(v_const_521_, v_const_523_);
lean_dec(v_const_523_);
lean_dec(v_const_521_);
v___x_529_ = l_Lean_Omega_IntList_sub(v_coeffs_522_, v_coeffs_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v___x_529_);
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_531_ = v___x_526_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_neg(lean_object* v_lc_536_){
_start:
{
lean_object* v_const_537_; lean_object* v_coeffs_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_547_; 
v_const_537_ = lean_ctor_get(v_lc_536_, 0);
v_coeffs_538_ = lean_ctor_get(v_lc_536_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_lc_536_);
if (v_isSharedCheck_547_ == 0)
{
v___x_540_ = v_lc_536_;
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_coeffs_538_);
lean_inc(v_const_537_);
lean_dec(v_lc_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_542_ = lean_int_neg(v_const_537_);
lean_dec(v_const_537_);
v___x_543_ = l_Lean_Omega_IntList_neg(v_coeffs_538_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_543_);
lean_ctor_set(v___x_540_, 0, v___x_542_);
v___x_545_ = v___x_540_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_smul(lean_object* v_lc_550_, lean_object* v_i_551_){
_start:
{
lean_object* v_const_552_; lean_object* v_coeffs_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_562_; 
v_const_552_ = lean_ctor_get(v_lc_550_, 0);
v_coeffs_553_ = lean_ctor_get(v_lc_550_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_lc_550_);
if (v_isSharedCheck_562_ == 0)
{
v___x_555_ = v_lc_550_;
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_coeffs_553_);
lean_inc(v_const_552_);
lean_dec(v_lc_550_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_557_ = lean_int_mul(v_i_551_, v_const_552_);
lean_dec(v_const_552_);
v___x_558_ = l_Lean_Omega_IntList_smul(v_coeffs_553_, v_i_551_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v___x_558_);
lean_ctor_set(v___x_555_, 0, v___x_557_);
v___x_560_ = v___x_555_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_smul___boxed(lean_object* v_lc_563_, lean_object* v_i_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Omega_LinearCombo_smul(v_lc_563_, v_i_564_);
lean_dec(v_i_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instHMulInt___lam__0(lean_object* v_i_566_, lean_object* v_lc_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Omega_LinearCombo_smul(v_lc_567_, v_i_566_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instHMulInt___lam__0___boxed(lean_object* v_i_569_, lean_object* v_lc_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Omega_LinearCombo_instHMulInt___lam__0(v_i_569_, v_lc_570_);
lean_dec(v_i_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_mul(lean_object* v_l_u2081_574_, lean_object* v_l_u2082_575_){
_start:
{
lean_object* v_const_576_; lean_object* v_const_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_const_576_ = lean_ctor_get(v_l_u2082_575_, 0);
lean_inc(v_const_576_);
v_const_577_ = lean_ctor_get(v_l_u2081_574_, 0);
lean_inc(v_const_577_);
v___x_578_ = l_Lean_Omega_LinearCombo_smul(v_l_u2081_574_, v_const_576_);
v___x_579_ = l_Lean_Omega_LinearCombo_smul(v_l_u2082_575_, v_const_577_);
v___x_580_ = l_Lean_Omega_LinearCombo_add(v___x_578_, v___x_579_);
v___x_581_ = lean_int_mul(v_const_577_, v_const_576_);
lean_dec(v_const_576_);
lean_dec(v_const_577_);
v___x_582_ = lean_box(0);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = l_Lean_Omega_LinearCombo_sub(v___x_580_, v___x_583_);
return v___x_584_;
}
}
lean_object* runtime_initialize_Init_Omega_Coeffs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Omega_LinearCombo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Omega_Coeffs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Omega_LinearCombo_instInhabited = _init_l_Lean_Omega_LinearCombo_instInhabited();
lean_mark_persistent(l_Lean_Omega_LinearCombo_instInhabited);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Omega_LinearCombo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Omega_Coeffs(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Omega_LinearCombo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Omega_Coeffs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega_LinearCombo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Omega_LinearCombo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Omega_LinearCombo(builtin);
}
#ifdef __cplusplus
}
#endif
