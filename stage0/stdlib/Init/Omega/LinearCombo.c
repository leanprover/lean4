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
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqLinearCombo_decEq(lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_const_57_; lean_object* v_coeffs_58_; lean_object* v_const_59_; lean_object* v_coeffs_60_; uint8_t v___x_61_; 
v_const_57_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_const_57_);
v_coeffs_58_ = lean_ctor_get(v_x_55_, 1);
lean_inc(v_coeffs_58_);
lean_dec_ref(v_x_55_);
v_const_59_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_const_59_);
v_coeffs_60_ = lean_ctor_get(v_x_56_, 1);
lean_inc(v_coeffs_60_);
lean_dec_ref(v_x_56_);
v___x_61_ = lean_int_dec_eq(v_const_57_, v_const_59_);
lean_dec(v_const_59_);
lean_dec(v_const_57_);
if (v___x_61_ == 0)
{
lean_dec(v_coeffs_60_);
lean_dec(v_coeffs_58_);
return v___x_61_;
}
else
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_63_ = l_instDecidableEqList___redArg(v___x_62_, v_coeffs_58_, v_coeffs_60_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqLinearCombo_decEq___boxed(lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Lean_Omega_instDecidableEqLinearCombo_decEq(v_x_64_, v_x_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_instDecidableEqLinearCombo(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
uint8_t v___x_70_; 
v___x_70_ = l_Lean_Omega_instDecidableEqLinearCombo_decEq(v_x_68_, v_x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqLinearCombo___boxed(lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Lean_Omega_instDecidableEqLinearCombo(v_x_71_, v_x_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Omega_instReprLinearCombo_repr_spec__1(lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_nat_to_int(v_a_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_77_, lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_dec(v_x_77_);
return v_x_78_;
}
else
{
lean_object* v_head_80_; lean_object* v_tail_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_121_; 
v_head_80_ = lean_ctor_get(v_x_79_, 0);
v_tail_81_ = lean_ctor_get(v_x_79_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_121_ == 0)
{
v___x_83_ = v_x_79_;
v_isShared_84_ = v_isSharedCheck_121_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_tail_81_);
lean_inc(v_head_80_);
lean_dec(v_x_79_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_121_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
lean_inc(v_x_77_);
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 5);
lean_ctor_set(v___x_83_, 1, v_x_77_);
lean_ctor_set(v___x_83_, 0, v_x_78_);
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_x_78_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_x_77_);
v___x_86_ = v_reuseFailAlloc_120_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; lean_object* v___y_89_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_95_ = lean_int_dec_lt(v_head_80_, v___x_94_);
if (v___x_95_ == 0)
{
if (v___x_95_ == 0)
{
lean_object* v_a_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_a_96_ = lean_nat_abs(v_head_80_);
lean_dec(v_head_80_);
v___x_97_ = l_Nat_reprFast(v_a_96_);
v___x_98_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_86_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v_x_78_ = v___x_99_;
v_x_79_ = v_tail_81_;
goto _start;
}
else
{
lean_object* v_abs_101_; lean_object* v_one_102_; lean_object* v_a_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_abs_101_ = lean_nat_abs(v_head_80_);
lean_dec(v_head_80_);
v_one_102_ = lean_unsigned_to_nat(1u);
v_a_103_ = lean_nat_sub(v_abs_101_, v_one_102_);
lean_dec(v_abs_101_);
v___x_104_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_105_ = lean_nat_add(v_a_103_, v_one_102_);
lean_dec(v_a_103_);
v___x_106_ = l_Nat_reprFast(v___x_105_);
v___x_107_ = lean_string_append(v___x_104_, v___x_106_);
lean_dec_ref(v___x_106_);
v___x_108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_86_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v_x_78_ = v___x_109_;
v_x_79_ = v_tail_81_;
goto _start;
}
}
else
{
if (v___x_95_ == 0)
{
lean_object* v_a_111_; lean_object* v___x_112_; 
v_a_111_ = lean_nat_abs(v_head_80_);
lean_dec(v_head_80_);
v___x_112_ = l_Nat_reprFast(v_a_111_);
v___y_89_ = v___x_112_;
goto v___jp_88_;
}
else
{
lean_object* v_abs_113_; lean_object* v_one_114_; lean_object* v_a_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_abs_113_ = lean_nat_abs(v_head_80_);
lean_dec(v_head_80_);
v_one_114_ = lean_unsigned_to_nat(1u);
v_a_115_ = lean_nat_sub(v_abs_113_, v_one_114_);
lean_dec(v_abs_113_);
v___x_116_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_117_ = lean_nat_add(v_a_115_, v_one_114_);
lean_dec(v_a_115_);
v___x_118_ = l_Nat_reprFast(v___x_117_);
v___x_119_ = lean_string_append(v___x_116_, v___x_118_);
lean_dec_ref(v___x_118_);
v___y_89_ = v___x_119_;
goto v___jp_88_;
}
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_90_, 0, v___y_89_);
v___x_91_ = l_Repr_addAppParen(v___x_90_, v___x_87_);
v___x_92_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_86_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v_x_78_ = v___x_92_;
v_x_79_ = v_tail_81_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2(lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_124_) == 0)
{
lean_dec(v_x_122_);
return v_x_123_;
}
else
{
lean_object* v_head_125_; lean_object* v_tail_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_166_; 
v_head_125_ = lean_ctor_get(v_x_124_, 0);
v_tail_126_ = lean_ctor_get(v_x_124_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_124_);
if (v_isSharedCheck_166_ == 0)
{
v___x_128_ = v_x_124_;
v_isShared_129_ = v_isSharedCheck_166_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_tail_126_);
lean_inc(v_head_125_);
lean_dec(v_x_124_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_166_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
lean_inc(v_x_122_);
if (v_isShared_129_ == 0)
{
lean_ctor_set_tag(v___x_128_, 5);
lean_ctor_set(v___x_128_, 1, v_x_122_);
lean_ctor_set(v___x_128_, 0, v_x_123_);
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_x_123_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_x_122_);
v___x_131_ = v_reuseFailAlloc_165_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___y_134_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_140_ = lean_int_dec_lt(v_head_125_, v___x_139_);
if (v___x_140_ == 0)
{
if (v___x_140_ == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_a_141_ = lean_nat_abs(v_head_125_);
lean_dec(v_head_125_);
v___x_142_ = l_Nat_reprFast(v_a_141_);
v___x_143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_131_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_122_, v___x_144_, v_tail_126_);
return v___x_145_;
}
else
{
lean_object* v_abs_146_; lean_object* v_one_147_; lean_object* v_a_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_abs_146_ = lean_nat_abs(v_head_125_);
lean_dec(v_head_125_);
v_one_147_ = lean_unsigned_to_nat(1u);
v_a_148_ = lean_nat_sub(v_abs_146_, v_one_147_);
lean_dec(v_abs_146_);
v___x_149_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_150_ = lean_nat_add(v_a_148_, v_one_147_);
lean_dec(v_a_148_);
v___x_151_ = l_Nat_reprFast(v___x_150_);
v___x_152_ = lean_string_append(v___x_149_, v___x_151_);
lean_dec_ref(v___x_151_);
v___x_153_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
v___x_154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_131_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_122_, v___x_154_, v_tail_126_);
return v___x_155_;
}
}
else
{
if (v___x_140_ == 0)
{
lean_object* v_a_156_; lean_object* v___x_157_; 
v_a_156_ = lean_nat_abs(v_head_125_);
lean_dec(v_head_125_);
v___x_157_ = l_Nat_reprFast(v_a_156_);
v___y_134_ = v___x_157_;
goto v___jp_133_;
}
else
{
lean_object* v_abs_158_; lean_object* v_one_159_; lean_object* v_a_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_abs_158_ = lean_nat_abs(v_head_125_);
lean_dec(v_head_125_);
v_one_159_ = lean_unsigned_to_nat(1u);
v_a_160_ = lean_nat_sub(v_abs_158_, v_one_159_);
lean_dec(v_abs_158_);
v___x_161_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_162_ = lean_nat_add(v_a_160_, v_one_159_);
lean_dec(v_a_160_);
v___x_163_ = l_Nat_reprFast(v___x_162_);
v___x_164_ = lean_string_append(v___x_161_, v___x_163_);
lean_dec_ref(v___x_163_);
v___y_134_ = v___x_164_;
goto v___jp_133_;
}
}
v___jp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_135_, 0, v___y_134_);
v___x_136_ = l_Repr_addAppParen(v___x_135_, v___x_132_);
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_131_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_122_, v___x_137_, v_tail_126_);
return v___x_138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(lean_object* v___y_167_){
_start:
{
lean_object* v___x_168_; lean_object* v___y_170_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_174_ = lean_int_dec_lt(v___y_167_, v___x_173_);
if (v___x_174_ == 0)
{
if (v___x_174_ == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_a_175_ = lean_nat_abs(v___y_167_);
v___x_176_ = l_Nat_reprFast(v_a_175_);
v___x_177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
else
{
lean_object* v_abs_178_; lean_object* v_one_179_; lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_abs_178_ = lean_nat_abs(v___y_167_);
v_one_179_ = lean_unsigned_to_nat(1u);
v_a_180_ = lean_nat_sub(v_abs_178_, v_one_179_);
lean_dec(v_abs_178_);
v___x_181_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_182_ = lean_nat_add(v_a_180_, v_one_179_);
lean_dec(v_a_180_);
v___x_183_ = l_Nat_reprFast(v___x_182_);
v___x_184_ = lean_string_append(v___x_181_, v___x_183_);
lean_dec_ref(v___x_183_);
v___x_185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
else
{
if (v___x_174_ == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; 
v_a_186_ = lean_nat_abs(v___y_167_);
v___x_187_ = l_Nat_reprFast(v_a_186_);
v___y_170_ = v___x_187_;
goto v___jp_169_;
}
else
{
lean_object* v_abs_188_; lean_object* v_one_189_; lean_object* v_a_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_abs_188_ = lean_nat_abs(v___y_167_);
v_one_189_ = lean_unsigned_to_nat(1u);
v_a_190_ = lean_nat_sub(v_abs_188_, v_one_189_);
lean_dec(v_abs_188_);
v___x_191_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_192_ = lean_nat_add(v_a_190_, v_one_189_);
lean_dec(v_a_190_);
v___x_193_ = l_Nat_reprFast(v___x_192_);
v___x_194_ = lean_string_append(v___x_191_, v___x_193_);
lean_dec_ref(v___x_193_);
v___y_170_ = v___x_194_;
goto v___jp_169_;
}
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_171_, 0, v___y_170_);
v___x_172_ = l_Repr_addAppParen(v___x_171_, v___x_168_);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0___boxed(lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v___y_195_);
lean_dec(v___y_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v___x_199_; 
lean_dec(v_x_198_);
v___x_199_ = lean_box(0);
return v___x_199_;
}
else
{
lean_object* v_tail_200_; 
v_tail_200_ = lean_ctor_get(v_x_197_, 1);
if (lean_obj_tag(v_tail_200_) == 0)
{
lean_object* v_head_201_; lean_object* v___x_202_; 
lean_dec(v_x_198_);
v_head_201_ = lean_ctor_get(v_x_197_, 0);
lean_inc(v_head_201_);
lean_dec_ref(v_x_197_);
v___x_202_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v_head_201_);
lean_dec(v_head_201_);
return v___x_202_;
}
else
{
lean_object* v_head_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
lean_inc(v_tail_200_);
v_head_203_ = lean_ctor_get(v_x_197_, 0);
lean_inc(v_head_203_);
lean_dec_ref(v_x_197_);
v___x_204_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v_head_203_);
lean_dec(v_head_203_);
v___x_205_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2(v_x_198_, v___x_204_, v_tail_200_);
return v___x_205_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2));
v___x_218_ = lean_string_length(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7);
v___x_220_ = lean_nat_to_int(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(lean_object* v_a_225_){
_start:
{
if (lean_obj_tag(v_a_225_) == 0)
{
lean_object* v___x_226_; 
v___x_226_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__1));
return v___x_226_;
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_227_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__5));
v___x_228_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0(v_a_225_, v___x_227_);
v___x_229_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8);
v___x_230_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__9));
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_228_);
v___x_232_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__10));
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_229_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = l_Std_Format_fill(v___x_234_);
return v___x_235_;
}
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(9u);
v___x_250_ = lean_nat_to_int(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(10u);
v___x_255_ = lean_nat_to_int(v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0));
v___x_258_ = lean_string_length(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12);
v___x_260_ = lean_nat_to_int(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg(lean_object* v_x_265_){
_start:
{
lean_object* v_const_266_; lean_object* v_coeffs_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_328_; 
v_const_266_ = lean_ctor_get(v_x_265_, 0);
v_coeffs_267_ = lean_ctor_get(v_x_265_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_265_);
if (v_isSharedCheck_328_ == 0)
{
v___x_269_ = v_x_265_;
v_isShared_270_ = v_isSharedCheck_328_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_coeffs_267_);
lean_inc(v_const_266_);
lean_dec(v_x_265_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_328_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___y_275_; lean_object* v___x_301_; lean_object* v___y_303_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_271_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5));
v___x_272_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__6));
v___x_273_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7);
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_307_ = lean_int_dec_lt(v_const_266_, v___x_306_);
if (v___x_307_ == 0)
{
if (v___x_307_ == 0)
{
lean_object* v_a_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_a_308_ = lean_nat_abs(v_const_266_);
lean_dec(v_const_266_);
v___x_309_ = l_Nat_reprFast(v_a_308_);
v___x_310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
v___y_275_ = v___x_310_;
goto v___jp_274_;
}
else
{
lean_object* v_abs_311_; lean_object* v_one_312_; lean_object* v_a_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_abs_311_ = lean_nat_abs(v_const_266_);
lean_dec(v_const_266_);
v_one_312_ = lean_unsigned_to_nat(1u);
v_a_313_ = lean_nat_sub(v_abs_311_, v_one_312_);
lean_dec(v_abs_311_);
v___x_314_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_315_ = lean_nat_add(v_a_313_, v_one_312_);
lean_dec(v_a_313_);
v___x_316_ = l_Nat_reprFast(v___x_315_);
v___x_317_ = lean_string_append(v___x_314_, v___x_316_);
lean_dec_ref(v___x_316_);
v___x_318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
v___y_275_ = v___x_318_;
goto v___jp_274_;
}
}
else
{
if (v___x_307_ == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; 
v_a_319_ = lean_nat_abs(v_const_266_);
lean_dec(v_const_266_);
v___x_320_ = l_Nat_reprFast(v_a_319_);
v___y_303_ = v___x_320_;
goto v___jp_302_;
}
else
{
lean_object* v_abs_321_; lean_object* v_one_322_; lean_object* v_a_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_abs_321_ = lean_nat_abs(v_const_266_);
lean_dec(v_const_266_);
v_one_322_ = lean_unsigned_to_nat(1u);
v_a_323_ = lean_nat_sub(v_abs_321_, v_one_322_);
lean_dec(v_abs_321_);
v___x_324_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_325_ = lean_nat_add(v_a_323_, v_one_322_);
lean_dec(v_a_323_);
v___x_326_ = l_Nat_reprFast(v___x_325_);
v___x_327_ = lean_string_append(v___x_324_, v___x_326_);
lean_dec_ref(v___x_326_);
v___y_303_ = v___x_327_;
goto v___jp_302_;
}
}
v___jp_274_:
{
lean_object* v___x_277_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set_tag(v___x_269_, 4);
lean_ctor_set(v___x_269_, 1, v___y_275_);
lean_ctor_set(v___x_269_, 0, v___x_273_);
v___x_277_ = v___x_269_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___y_275_);
v___x_277_ = v_reuseFailAlloc_300_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_278_ = 0;
v___x_279_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*1, v___x_278_);
v___x_280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_272_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4));
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_box(1);
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__9));
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_271_);
v___x_288_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10);
v___x_289_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(v_coeffs_267_);
v___x_290_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set_uint8(v___x_291_, sizeof(void*)*1, v___x_278_);
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_287_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13);
v___x_294_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__14));
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_292_);
v___x_296_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__15));
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_293_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*1, v___x_278_);
return v___x_299_;
}
}
v___jp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_304_, 0, v___y_303_);
v___x_305_ = l_Repr_addAppParen(v___x_304_, v___x_301_);
v___y_275_ = v___x_305_;
goto v___jp_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr(lean_object* v_x_329_, lean_object* v_prec_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Omega_instReprLinearCombo_repr___redArg(v_x_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr___boxed(lean_object* v_x_332_, lean_object* v_prec_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Omega_instReprLinearCombo_repr(v_x_332_, v_prec_333_);
lean_dec(v_prec_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0(lean_object* v_a_335_, lean_object* v_n_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(v_a_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___boxed(lean_object* v_a_338_, lean_object* v_n_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0(v_a_338_, v_n_339_);
lean_dec(v_n_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_344_) == 0)
{
return v_x_343_;
}
else
{
lean_object* v_head_345_; lean_object* v_tail_346_; lean_object* v___x_347_; 
v_head_345_ = lean_ctor_get(v_x_344_, 0);
v_tail_346_ = lean_ctor_get(v_x_344_, 1);
v___x_347_ = lean_string_append(v_x_343_, v_head_345_);
v_x_343_ = v___x_347_;
v_x_344_ = v_tail_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0___boxed(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(v_x_349_, v_x_350_);
lean_dec(v_x_350_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(lean_object* v_l_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___closed__0));
v___x_355_ = l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(v___x_354_, v_l_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___boxed(lean_object* v_l_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v_l_356_);
lean_dec(v_l_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1___lam__0(lean_object* v_x_360_){
_start:
{
lean_object* v_fst_361_; lean_object* v_snd_362_; lean_object* v___x_363_; lean_object* v___y_365_; lean_object* v_intZero_373_; uint8_t v_isNeg_374_; 
v_fst_361_ = lean_ctor_get(v_x_360_, 0);
v_snd_362_ = lean_ctor_get(v_x_360_, 1);
v___x_363_ = ((lean_object*)(l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__0));
v_intZero_373_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_374_ = lean_int_dec_lt(v_fst_361_, v_intZero_373_);
if (v_isNeg_374_ == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_375_ = lean_nat_abs(v_fst_361_);
v___x_376_ = l_Nat_reprFast(v_a_375_);
v___y_365_ = v___x_376_;
goto v___jp_364_;
}
else
{
lean_object* v_abs_377_; lean_object* v_one_378_; lean_object* v_a_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_abs_377_ = lean_nat_abs(v_fst_361_);
v_one_378_ = lean_unsigned_to_nat(1u);
v_a_379_ = lean_nat_sub(v_abs_377_, v_one_378_);
lean_dec(v_abs_377_);
v___x_380_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_381_ = lean_nat_add(v_a_379_, v_one_378_);
lean_dec(v_a_379_);
v___x_382_ = l_Nat_reprFast(v___x_381_);
v___x_383_ = lean_string_append(v___x_380_, v___x_382_);
lean_dec_ref(v___x_382_);
v___y_365_ = v___x_383_;
goto v___jp_364_;
}
v___jp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_366_ = lean_string_append(v___x_363_, v___y_365_);
lean_dec_ref(v___y_365_);
v___x_367_ = ((lean_object*)(l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__1));
v___x_368_ = lean_string_append(v___x_366_, v___x_367_);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_snd_362_, v___x_369_);
v___x_371_ = l_Nat_reprFast(v___x_370_);
v___x_372_ = lean_string_append(v___x_368_, v___x_371_);
lean_dec_ref(v___x_371_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___boxed(lean_object* v_x_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Omega_LinearCombo_instToString___private__1___lam__0(v_x_384_);
lean_dec_ref(v_x_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1(lean_object* v_lc_387_){
_start:
{
lean_object* v_const_388_; lean_object* v_coeffs_389_; lean_object* v___f_390_; lean_object* v___y_392_; lean_object* v_intZero_399_; uint8_t v_isNeg_400_; 
v_const_388_ = lean_ctor_get(v_lc_387_, 0);
lean_inc(v_const_388_);
v_coeffs_389_ = lean_ctor_get(v_lc_387_, 1);
lean_inc(v_coeffs_389_);
lean_dec_ref(v_lc_387_);
v___f_390_ = ((lean_object*)(l_Lean_Omega_LinearCombo_instToString___private__1___closed__0));
v_intZero_399_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_400_ = lean_int_dec_lt(v_const_388_, v_intZero_399_);
if (v_isNeg_400_ == 0)
{
lean_object* v_a_401_; lean_object* v___x_402_; 
v_a_401_ = lean_nat_abs(v_const_388_);
lean_dec(v_const_388_);
v___x_402_ = l_Nat_reprFast(v_a_401_);
v___y_392_ = v___x_402_;
goto v___jp_391_;
}
else
{
lean_object* v_abs_403_; lean_object* v_one_404_; lean_object* v_a_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_abs_403_ = lean_nat_abs(v_const_388_);
lean_dec(v_const_388_);
v_one_404_ = lean_unsigned_to_nat(1u);
v_a_405_ = lean_nat_sub(v_abs_403_, v_one_404_);
lean_dec(v_abs_403_);
v___x_406_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_407_ = lean_nat_add(v_a_405_, v_one_404_);
lean_dec(v_a_405_);
v___x_408_ = l_Nat_reprFast(v___x_407_);
v___x_409_ = lean_string_append(v___x_406_, v___x_408_);
lean_dec_ref(v___x_408_);
v___y_392_ = v___x_409_;
goto v___jp_391_;
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = l_List_zipIdx___redArg(v_coeffs_389_, v___x_393_);
v___x_395_ = lean_box(0);
v___x_396_ = l_List_mapTR_loop___redArg(v___f_390_, v___x_394_, v___x_395_);
v___x_397_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v___x_396_);
lean_dec(v___x_396_);
v___x_398_ = lean_string_append(v___y_392_, v___x_397_);
lean_dec_ref(v___x_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___lam__1(lean_object* v___f_410_, lean_object* v_lc_411_){
_start:
{
lean_object* v_const_412_; lean_object* v_coeffs_413_; lean_object* v___y_415_; lean_object* v_intZero_422_; uint8_t v_isNeg_423_; 
v_const_412_ = lean_ctor_get(v_lc_411_, 0);
lean_inc(v_const_412_);
v_coeffs_413_ = lean_ctor_get(v_lc_411_, 1);
lean_inc(v_coeffs_413_);
lean_dec_ref(v_lc_411_);
v_intZero_422_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_423_ = lean_int_dec_lt(v_const_412_, v_intZero_422_);
if (v_isNeg_423_ == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; 
v_a_424_ = lean_nat_abs(v_const_412_);
lean_dec(v_const_412_);
v___x_425_ = l_Nat_reprFast(v_a_424_);
v___y_415_ = v___x_425_;
goto v___jp_414_;
}
else
{
lean_object* v_abs_426_; lean_object* v_one_427_; lean_object* v_a_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_abs_426_ = lean_nat_abs(v_const_412_);
lean_dec(v_const_412_);
v_one_427_ = lean_unsigned_to_nat(1u);
v_a_428_ = lean_nat_sub(v_abs_426_, v_one_427_);
lean_dec(v_abs_426_);
v___x_429_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_430_ = lean_nat_add(v_a_428_, v_one_427_);
lean_dec(v_a_428_);
v___x_431_ = l_Nat_reprFast(v___x_430_);
v___x_432_ = lean_string_append(v___x_429_, v___x_431_);
lean_dec_ref(v___x_431_);
v___y_415_ = v___x_432_;
goto v___jp_414_;
}
v___jp_414_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = l_List_zipIdx___redArg(v_coeffs_413_, v___x_416_);
v___x_418_ = lean_box(0);
v___x_419_ = l_List_mapTR_loop___redArg(v___f_410_, v___x_417_, v___x_418_);
v___x_420_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v___x_419_);
lean_dec(v___x_419_);
v___x_421_ = lean_string_append(v___y_415_, v___x_420_);
lean_dec_ref(v___x_420_);
return v___x_421_;
}
}
}
static lean_object* _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_nat_to_int(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Omega_LinearCombo_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_box(0);
v___x_439_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Omega_LinearCombo_instInhabited(void){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__1, &l_Lean_Omega_LinearCombo_instInhabited___closed__1_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__1);
return v___x_441_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_LinearCombo_isAtom___lam__0(lean_object* v_c_442_){
_start:
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_444_ = lean_int_dec_eq(v_c_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_446_ = lean_int_dec_eq(v_c_442_, v___x_445_);
return v___x_446_;
}
else
{
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_isAtom___lam__0___boxed(lean_object* v_c_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l_Lean_Omega_LinearCombo_isAtom___lam__0(v_c_447_);
lean_dec(v_c_447_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Omega_LinearCombo_isAtom_spec__0(lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
if (lean_obj_tag(v_a_450_) == 0)
{
lean_object* v___x_452_; 
v___x_452_ = l_List_reverse___redArg(v_a_451_);
return v___x_452_;
}
else
{
lean_object* v_head_453_; lean_object* v_tail_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_465_; 
v_head_453_ = lean_ctor_get(v_a_450_, 0);
v_tail_454_ = lean_ctor_get(v_a_450_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_465_ == 0)
{
v___x_456_ = v_a_450_;
v_isShared_457_ = v_isSharedCheck_465_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_tail_454_);
lean_inc(v_head_453_);
lean_dec(v_a_450_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_465_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_459_ = lean_int_dec_eq(v_head_453_, v___x_458_);
if (v___x_459_ == 0)
{
lean_del_object(v___x_456_);
lean_dec(v_head_453_);
v_a_450_ = v_tail_454_;
goto _start;
}
else
{
lean_object* v___x_462_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 1, v_a_451_);
v___x_462_ = v___x_456_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_head_453_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_a_451_);
v___x_462_ = v_reuseFailAlloc_464_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
v_a_450_ = v_tail_454_;
v_a_451_ = v___x_462_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_LinearCombo_isAtom(lean_object* v_a_467_){
_start:
{
lean_object* v_const_468_; lean_object* v_coeffs_469_; lean_object* v___f_470_; uint8_t v___y_472_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_const_468_ = lean_ctor_get(v_a_467_, 0);
lean_inc(v_const_468_);
v_coeffs_469_ = lean_ctor_get(v_a_467_, 1);
lean_inc(v_coeffs_469_);
lean_dec_ref(v_a_467_);
v___f_470_ = ((lean_object*)(l_Lean_Omega_LinearCombo_isAtom___closed__0));
v___x_474_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_475_ = lean_int_dec_eq(v_const_468_, v___x_474_);
lean_dec(v_const_468_);
if (v___x_475_ == 0)
{
v___y_472_ = v___x_475_;
goto v___jp_471_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_476_ = lean_box(0);
lean_inc(v_coeffs_469_);
v___x_477_ = l_List_filterTR_loop___at___00Lean_Omega_LinearCombo_isAtom_spec__0(v_coeffs_469_, v___x_476_);
v___x_478_ = l_List_lengthTR___redArg(v___x_477_);
lean_dec(v___x_477_);
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_dec_eq(v___x_478_, v___x_479_);
lean_dec(v___x_478_);
v___y_472_ = v___x_480_;
goto v___jp_471_;
}
v___jp_471_:
{
if (v___y_472_ == 0)
{
lean_dec(v_coeffs_469_);
return v___y_472_;
}
else
{
uint8_t v___x_473_; 
v___x_473_ = l_List_all___redArg(v_coeffs_469_, v___f_470_);
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_isAtom___boxed(lean_object* v_a_481_){
_start:
{
uint8_t v_res_482_; lean_object* v_r_483_; 
v_res_482_ = l_Lean_Omega_LinearCombo_isAtom(v_a_481_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_eval(lean_object* v_lc_484_, lean_object* v_values_485_){
_start:
{
lean_object* v_const_486_; lean_object* v_coeffs_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_const_486_ = lean_ctor_get(v_lc_484_, 0);
v_coeffs_487_ = lean_ctor_get(v_lc_484_, 1);
v___x_488_ = l_Lean_Omega_IntList_dot(v_coeffs_487_, v_values_485_);
v___x_489_ = lean_int_add(v_const_486_, v___x_488_);
lean_dec(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_eval___boxed(lean_object* v_lc_490_, lean_object* v_values_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Omega_LinearCombo_eval(v_lc_490_, v_values_491_);
lean_dec_ref(v_lc_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_coordinate(lean_object* v_i_493_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_494_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_495_ = lean_box(0);
v___x_496_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_497_ = l_Lean_Omega_IntList_set(v___x_495_, v_i_493_, v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_494_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_coordinate___boxed(lean_object* v_i_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Omega_LinearCombo_coordinate(v_i_499_);
lean_dec(v_i_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_add(lean_object* v_l_u2081_501_, lean_object* v_l_u2082_502_){
_start:
{
lean_object* v_const_503_; lean_object* v_coeffs_504_; lean_object* v_const_505_; lean_object* v_coeffs_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_515_; 
v_const_503_ = lean_ctor_get(v_l_u2081_501_, 0);
lean_inc(v_const_503_);
v_coeffs_504_ = lean_ctor_get(v_l_u2081_501_, 1);
lean_inc(v_coeffs_504_);
lean_dec_ref(v_l_u2081_501_);
v_const_505_ = lean_ctor_get(v_l_u2082_502_, 0);
v_coeffs_506_ = lean_ctor_get(v_l_u2082_502_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_l_u2082_502_);
if (v_isSharedCheck_515_ == 0)
{
v___x_508_ = v_l_u2082_502_;
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_coeffs_506_);
lean_inc(v_const_505_);
lean_dec(v_l_u2082_502_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = lean_int_add(v_const_503_, v_const_505_);
lean_dec(v_const_505_);
lean_dec(v_const_503_);
v___x_511_ = l_Lean_Omega_IntList_add(v_coeffs_504_, v_coeffs_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_511_);
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_sub(lean_object* v_l_u2081_518_, lean_object* v_l_u2082_519_){
_start:
{
lean_object* v_const_520_; lean_object* v_coeffs_521_; lean_object* v_const_522_; lean_object* v_coeffs_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_532_; 
v_const_520_ = lean_ctor_get(v_l_u2081_518_, 0);
lean_inc(v_const_520_);
v_coeffs_521_ = lean_ctor_get(v_l_u2081_518_, 1);
lean_inc(v_coeffs_521_);
lean_dec_ref(v_l_u2081_518_);
v_const_522_ = lean_ctor_get(v_l_u2082_519_, 0);
v_coeffs_523_ = lean_ctor_get(v_l_u2082_519_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v_l_u2082_519_);
if (v_isSharedCheck_532_ == 0)
{
v___x_525_ = v_l_u2082_519_;
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_coeffs_523_);
lean_inc(v_const_522_);
lean_dec(v_l_u2082_519_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_527_ = lean_int_sub(v_const_520_, v_const_522_);
lean_dec(v_const_522_);
lean_dec(v_const_520_);
v___x_528_ = l_Lean_Omega_IntList_sub(v_coeffs_521_, v_coeffs_523_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v___x_528_);
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_530_ = v___x_525_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_neg(lean_object* v_lc_535_){
_start:
{
lean_object* v_const_536_; lean_object* v_coeffs_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_546_; 
v_const_536_ = lean_ctor_get(v_lc_535_, 0);
v_coeffs_537_ = lean_ctor_get(v_lc_535_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_lc_535_);
if (v_isSharedCheck_546_ == 0)
{
v___x_539_ = v_lc_535_;
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_coeffs_537_);
lean_inc(v_const_536_);
lean_dec(v_lc_535_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_int_neg(v_const_536_);
lean_dec(v_const_536_);
v___x_542_ = l_Lean_Omega_IntList_neg(v_coeffs_537_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_542_);
lean_ctor_set(v___x_539_, 0, v___x_541_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_smul(lean_object* v_lc_549_, lean_object* v_i_550_){
_start:
{
lean_object* v_const_551_; lean_object* v_coeffs_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_561_; 
v_const_551_ = lean_ctor_get(v_lc_549_, 0);
v_coeffs_552_ = lean_ctor_get(v_lc_549_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v_lc_549_);
if (v_isSharedCheck_561_ == 0)
{
v___x_554_ = v_lc_549_;
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_coeffs_552_);
lean_inc(v_const_551_);
lean_dec(v_lc_549_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = lean_int_mul(v_i_550_, v_const_551_);
lean_dec(v_const_551_);
v___x_557_ = l_Lean_Omega_IntList_smul(v_coeffs_552_, v_i_550_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_557_);
lean_ctor_set(v___x_554_, 0, v___x_556_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_smul___boxed(lean_object* v_lc_562_, lean_object* v_i_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Omega_LinearCombo_smul(v_lc_562_, v_i_563_);
lean_dec(v_i_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instHMulInt___lam__0(lean_object* v_i_565_, lean_object* v_lc_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Omega_LinearCombo_smul(v_lc_566_, v_i_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instHMulInt___lam__0___boxed(lean_object* v_i_568_, lean_object* v_lc_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Omega_LinearCombo_instHMulInt___lam__0(v_i_568_, v_lc_569_);
lean_dec(v_i_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_mul(lean_object* v_l_u2081_573_, lean_object* v_l_u2082_574_){
_start:
{
lean_object* v_const_575_; lean_object* v_const_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_const_575_ = lean_ctor_get(v_l_u2082_574_, 0);
lean_inc(v_const_575_);
v_const_576_ = lean_ctor_get(v_l_u2081_573_, 0);
lean_inc(v_const_576_);
v___x_577_ = l_Lean_Omega_LinearCombo_smul(v_l_u2081_573_, v_const_575_);
v___x_578_ = l_Lean_Omega_LinearCombo_smul(v_l_u2082_574_, v_const_576_);
v___x_579_ = l_Lean_Omega_LinearCombo_add(v___x_577_, v___x_578_);
v___x_580_ = lean_int_mul(v_const_576_, v_const_575_);
lean_dec(v_const_575_);
lean_dec(v_const_576_);
v___x_581_ = lean_box(0);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = l_Lean_Omega_LinearCombo_sub(v___x_579_, v___x_582_);
return v___x_583_;
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
