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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(lean_object*, lean_object*);
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
lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Omega_LinearCombo_isAtom_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__1___boxed(lean_object*);
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
uint8_t l_Lean_Omega_instDecidableEqLinearCombo_decEq(lean_object* v_x_55_, lean_object* v_x_56_){
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
LEAN_EXPORT void l_Lean_Omega_instDecidableEqLinearCombo_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_55_ = stack[0].m_obj;
lean_object* v_x_56_ = stack[1].m_obj;
uint8_t v_res_64_;
v_res_64_ = l_Lean_Omega_instDecidableEqLinearCombo_decEq(v_x_55_, v_x_56_);
stack->m_num = v_res_64_;
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
uint8_t l_Lean_Omega_instDecidableEqLinearCombo(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = l_Lean_Omega_instDecidableEqLinearCombo_decEq(v_x_69_, v_x_70_);
return v___x_71_;
}
}
LEAN_EXPORT void l_Lean_Omega_instDecidableEqLinearCombo_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_69_ = stack[0].m_obj;
lean_object* v_x_70_ = stack[1].m_obj;
uint8_t v_res_72_;
v_res_72_ = l_Lean_Omega_instDecidableEqLinearCombo(v_x_69_, v_x_70_);
stack->m_num = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_Omega_instDecidableEqLinearCombo___boxed(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lean_Omega_instDecidableEqLinearCombo(v_x_73_, v_x_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Omega_instReprLinearCombo_repr_spec__1(lean_object* v_a_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_nat_to_int(v_a_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_79_, lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_dec(v_x_79_);
return v_x_80_;
}
else
{
lean_object* v_head_82_; lean_object* v_tail_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_123_; 
v_head_82_ = lean_ctor_get(v_x_81_, 0);
v_tail_83_ = lean_ctor_get(v_x_81_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_81_);
if (v_isSharedCheck_123_ == 0)
{
v___x_85_ = v_x_81_;
v_isShared_86_ = v_isSharedCheck_123_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_tail_83_);
lean_inc(v_head_82_);
lean_dec(v_x_81_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_123_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
lean_inc(v_x_79_);
if (v_isShared_86_ == 0)
{
lean_ctor_set_tag(v___x_85_, 5);
lean_ctor_set(v___x_85_, 1, v_x_79_);
lean_ctor_set(v___x_85_, 0, v_x_80_);
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_x_80_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_x_79_);
v___x_88_ = v_reuseFailAlloc_122_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; lean_object* v___y_91_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_97_ = lean_int_dec_lt(v_head_82_, v___x_96_);
if (v___x_97_ == 0)
{
if (v___x_97_ == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_a_98_ = lean_nat_abs(v_head_82_);
lean_dec(v_head_82_);
v___x_99_ = l_Nat_reprFast(v_a_98_);
v___x_100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
v___x_101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_88_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v_x_80_ = v___x_101_;
v_x_81_ = v_tail_83_;
goto _start;
}
else
{
lean_object* v_abs_103_; lean_object* v_one_104_; lean_object* v_a_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_abs_103_ = lean_nat_abs(v_head_82_);
lean_dec(v_head_82_);
v_one_104_ = lean_unsigned_to_nat(1u);
v_a_105_ = lean_nat_sub(v_abs_103_, v_one_104_);
lean_dec(v_abs_103_);
v___x_106_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_107_ = lean_nat_add(v_a_105_, v_one_104_);
lean_dec(v_a_105_);
v___x_108_ = l_Nat_reprFast(v___x_107_);
v___x_109_ = lean_string_append(v___x_106_, v___x_108_);
lean_dec_ref(v___x_108_);
v___x_110_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
v___x_111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_88_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v_x_80_ = v___x_111_;
v_x_81_ = v_tail_83_;
goto _start;
}
}
else
{
if (v___x_97_ == 0)
{
lean_object* v_a_113_; lean_object* v___x_114_; 
v_a_113_ = lean_nat_abs(v_head_82_);
lean_dec(v_head_82_);
v___x_114_ = l_Nat_reprFast(v_a_113_);
v___y_91_ = v___x_114_;
goto v___jp_90_;
}
else
{
lean_object* v_abs_115_; lean_object* v_one_116_; lean_object* v_a_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_abs_115_ = lean_nat_abs(v_head_82_);
lean_dec(v_head_82_);
v_one_116_ = lean_unsigned_to_nat(1u);
v_a_117_ = lean_nat_sub(v_abs_115_, v_one_116_);
lean_dec(v_abs_115_);
v___x_118_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_119_ = lean_nat_add(v_a_117_, v_one_116_);
lean_dec(v_a_117_);
v___x_120_ = l_Nat_reprFast(v___x_119_);
v___x_121_ = lean_string_append(v___x_118_, v___x_120_);
lean_dec_ref(v___x_120_);
v___y_91_ = v___x_121_;
goto v___jp_90_;
}
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_92_, 0, v___y_91_);
v___x_93_ = l_Repr_addAppParen(v___x_92_, v___x_89_);
v___x_94_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_88_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v_x_80_ = v___x_94_;
v_x_81_ = v_tail_83_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2(lean_object* v_x_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_dec(v_x_124_);
return v_x_125_;
}
else
{
lean_object* v_head_127_; lean_object* v_tail_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_168_; 
v_head_127_ = lean_ctor_get(v_x_126_, 0);
v_tail_128_ = lean_ctor_get(v_x_126_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_x_126_);
if (v_isSharedCheck_168_ == 0)
{
v___x_130_ = v_x_126_;
v_isShared_131_ = v_isSharedCheck_168_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_tail_128_);
lean_inc(v_head_127_);
lean_dec(v_x_126_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_168_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
lean_inc(v_x_124_);
if (v_isShared_131_ == 0)
{
lean_ctor_set_tag(v___x_130_, 5);
lean_ctor_set(v___x_130_, 1, v_x_124_);
lean_ctor_set(v___x_130_, 0, v_x_125_);
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_x_125_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_x_124_);
v___x_133_ = v_reuseFailAlloc_167_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v___y_136_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_142_ = lean_int_dec_lt(v_head_127_, v___x_141_);
if (v___x_142_ == 0)
{
if (v___x_142_ == 0)
{
lean_object* v_a_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_a_143_ = lean_nat_abs(v_head_127_);
lean_dec(v_head_127_);
v___x_144_ = l_Nat_reprFast(v_a_143_);
v___x_145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_133_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_124_, v___x_146_, v_tail_128_);
return v___x_147_;
}
else
{
lean_object* v_abs_148_; lean_object* v_one_149_; lean_object* v_a_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_abs_148_ = lean_nat_abs(v_head_127_);
lean_dec(v_head_127_);
v_one_149_ = lean_unsigned_to_nat(1u);
v_a_150_ = lean_nat_sub(v_abs_148_, v_one_149_);
lean_dec(v_abs_148_);
v___x_151_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_152_ = lean_nat_add(v_a_150_, v_one_149_);
lean_dec(v_a_150_);
v___x_153_ = l_Nat_reprFast(v___x_152_);
v___x_154_ = lean_string_append(v___x_151_, v___x_153_);
lean_dec_ref(v___x_153_);
v___x_155_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
v___x_156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_133_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v___x_157_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_124_, v___x_156_, v_tail_128_);
return v___x_157_;
}
}
else
{
if (v___x_142_ == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; 
v_a_158_ = lean_nat_abs(v_head_127_);
lean_dec(v_head_127_);
v___x_159_ = l_Nat_reprFast(v_a_158_);
v___y_136_ = v___x_159_;
goto v___jp_135_;
}
else
{
lean_object* v_abs_160_; lean_object* v_one_161_; lean_object* v_a_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_abs_160_ = lean_nat_abs(v_head_127_);
lean_dec(v_head_127_);
v_one_161_ = lean_unsigned_to_nat(1u);
v_a_162_ = lean_nat_sub(v_abs_160_, v_one_161_);
lean_dec(v_abs_160_);
v___x_163_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_164_ = lean_nat_add(v_a_162_, v_one_161_);
lean_dec(v_a_162_);
v___x_165_ = l_Nat_reprFast(v___x_164_);
v___x_166_ = lean_string_append(v___x_163_, v___x_165_);
lean_dec_ref(v___x_165_);
v___y_136_ = v___x_166_;
goto v___jp_135_;
}
}
v___jp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_137_, 0, v___y_136_);
v___x_138_ = l_Repr_addAppParen(v___x_137_, v___x_134_);
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_133_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
v___x_140_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_124_, v___x_139_, v_tail_128_);
return v___x_140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(lean_object* v___y_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___y_172_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_176_ = lean_int_dec_lt(v___y_169_, v___x_175_);
if (v___x_176_ == 0)
{
if (v___x_176_ == 0)
{
lean_object* v_a_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_a_177_ = lean_nat_abs(v___y_169_);
v___x_178_ = l_Nat_reprFast(v_a_177_);
v___x_179_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
else
{
lean_object* v_abs_180_; lean_object* v_one_181_; lean_object* v_a_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_abs_180_ = lean_nat_abs(v___y_169_);
v_one_181_ = lean_unsigned_to_nat(1u);
v_a_182_ = lean_nat_sub(v_abs_180_, v_one_181_);
lean_dec(v_abs_180_);
v___x_183_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_184_ = lean_nat_add(v_a_182_, v_one_181_);
lean_dec(v_a_182_);
v___x_185_ = l_Nat_reprFast(v___x_184_);
v___x_186_ = lean_string_append(v___x_183_, v___x_185_);
lean_dec_ref(v___x_185_);
v___x_187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
else
{
if (v___x_176_ == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; 
v_a_188_ = lean_nat_abs(v___y_169_);
v___x_189_ = l_Nat_reprFast(v_a_188_);
v___y_172_ = v___x_189_;
goto v___jp_171_;
}
else
{
lean_object* v_abs_190_; lean_object* v_one_191_; lean_object* v_a_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_abs_190_ = lean_nat_abs(v___y_169_);
v_one_191_ = lean_unsigned_to_nat(1u);
v_a_192_ = lean_nat_sub(v_abs_190_, v_one_191_);
lean_dec(v_abs_190_);
v___x_193_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_194_ = lean_nat_add(v_a_192_, v_one_191_);
lean_dec(v_a_192_);
v___x_195_ = l_Nat_reprFast(v___x_194_);
v___x_196_ = lean_string_append(v___x_193_, v___x_195_);
lean_dec_ref(v___x_195_);
v___y_172_ = v___x_196_;
goto v___jp_171_;
}
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_173_, 0, v___y_172_);
v___x_174_ = l_Repr_addAppParen(v___x_173_, v___x_170_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0___boxed(lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v___y_197_);
lean_dec(v___y_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0(lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v___x_201_; 
lean_dec(v_x_200_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
else
{
lean_object* v_tail_202_; 
v_tail_202_ = lean_ctor_get(v_x_199_, 1);
if (lean_obj_tag(v_tail_202_) == 0)
{
lean_object* v_head_203_; lean_object* v___x_204_; 
lean_dec(v_x_200_);
v_head_203_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_head_203_);
lean_dec_ref_known(v_x_199_, 2);
v___x_204_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v_head_203_);
lean_dec(v_head_203_);
return v___x_204_;
}
else
{
lean_object* v_head_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
lean_inc(v_tail_202_);
v_head_205_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_head_205_);
lean_dec_ref_known(v_x_199_, 2);
v___x_206_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v_head_205_);
lean_dec(v_head_205_);
v___x_207_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2(v_x_200_, v___x_206_, v_tail_202_);
return v___x_207_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2));
v___x_220_ = lean_string_length(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7);
v___x_222_ = lean_nat_to_int(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(lean_object* v_a_227_){
_start:
{
if (lean_obj_tag(v_a_227_) == 0)
{
lean_object* v___x_228_; 
v___x_228_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__1));
return v___x_228_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_229_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__5));
v___x_230_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0(v_a_227_, v___x_229_);
v___x_231_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8);
v___x_232_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__9));
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_230_);
v___x_234_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__10));
v___x_235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_231_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = l_Std_Format_fill(v___x_236_);
return v___x_237_;
}
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(9u);
v___x_252_ = lean_nat_to_int(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_unsigned_to_nat(10u);
v___x_257_ = lean_nat_to_int(v___x_256_);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0));
v___x_260_ = lean_string_length(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12);
v___x_262_ = lean_nat_to_int(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr___redArg(lean_object* v_x_267_){
_start:
{
lean_object* v_const_268_; lean_object* v_coeffs_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_330_; 
v_const_268_ = lean_ctor_get(v_x_267_, 0);
v_coeffs_269_ = lean_ctor_get(v_x_267_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_x_267_);
if (v_isSharedCheck_330_ == 0)
{
v___x_271_ = v_x_267_;
v_isShared_272_ = v_isSharedCheck_330_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_coeffs_269_);
lean_inc(v_const_268_);
lean_dec(v_x_267_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_330_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___y_277_; lean_object* v___x_303_; lean_object* v___y_305_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_273_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5));
v___x_274_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__6));
v___x_275_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7);
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_309_ = lean_int_dec_lt(v_const_268_, v___x_308_);
if (v___x_309_ == 0)
{
if (v___x_309_ == 0)
{
lean_object* v_a_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_a_310_ = lean_nat_abs(v_const_268_);
lean_dec(v_const_268_);
v___x_311_ = l_Nat_reprFast(v_a_310_);
v___x_312_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
v___y_277_ = v___x_312_;
goto v___jp_276_;
}
else
{
lean_object* v_abs_313_; lean_object* v_one_314_; lean_object* v_a_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_abs_313_ = lean_nat_abs(v_const_268_);
lean_dec(v_const_268_);
v_one_314_ = lean_unsigned_to_nat(1u);
v_a_315_ = lean_nat_sub(v_abs_313_, v_one_314_);
lean_dec(v_abs_313_);
v___x_316_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_317_ = lean_nat_add(v_a_315_, v_one_314_);
lean_dec(v_a_315_);
v___x_318_ = l_Nat_reprFast(v___x_317_);
v___x_319_ = lean_string_append(v___x_316_, v___x_318_);
lean_dec_ref(v___x_318_);
v___x_320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
v___y_277_ = v___x_320_;
goto v___jp_276_;
}
}
else
{
if (v___x_309_ == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; 
v_a_321_ = lean_nat_abs(v_const_268_);
lean_dec(v_const_268_);
v___x_322_ = l_Nat_reprFast(v_a_321_);
v___y_305_ = v___x_322_;
goto v___jp_304_;
}
else
{
lean_object* v_abs_323_; lean_object* v_one_324_; lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_abs_323_ = lean_nat_abs(v_const_268_);
lean_dec(v_const_268_);
v_one_324_ = lean_unsigned_to_nat(1u);
v_a_325_ = lean_nat_sub(v_abs_323_, v_one_324_);
lean_dec(v_abs_323_);
v___x_326_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_327_ = lean_nat_add(v_a_325_, v_one_324_);
lean_dec(v_a_325_);
v___x_328_ = l_Nat_reprFast(v___x_327_);
v___x_329_ = lean_string_append(v___x_326_, v___x_328_);
lean_dec_ref(v___x_328_);
v___y_305_ = v___x_329_;
goto v___jp_304_;
}
}
v___jp_276_:
{
lean_object* v___x_279_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 4);
lean_ctor_set(v___x_271_, 1, v___y_277_);
lean_ctor_set(v___x_271_, 0, v___x_275_);
v___x_279_ = v___x_271_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v___y_277_);
v___x_279_ = v_reuseFailAlloc_302_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_280_ = 0;
v___x_281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*1, v___x_280_);
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_274_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4));
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_box(1);
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__9));
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_273_);
v___x_290_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10);
v___x_291_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(v_coeffs_269_);
v___x_292_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*1, v___x_280_);
v___x_294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_289_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_obj_once(&l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13, &l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13_once, _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13);
v___x_296_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__14));
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_294_);
v___x_298_ = ((lean_object*)(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__15));
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_295_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*1, v___x_280_);
return v___x_301_;
}
}
v___jp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_306_, 0, v___y_305_);
v___x_307_ = l_Repr_addAppParen(v___x_306_, v___x_303_);
v___y_277_ = v___x_307_;
goto v___jp_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr(lean_object* v_x_331_, lean_object* v_prec_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Omega_instReprLinearCombo_repr___redArg(v_x_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_instReprLinearCombo_repr___boxed(lean_object* v_x_334_, lean_object* v_prec_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Omega_instReprLinearCombo_repr(v_x_334_, v_prec_335_);
lean_dec(v_prec_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0(lean_object* v_a_337_, lean_object* v_n_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(v_a_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___boxed(lean_object* v_a_340_, lean_object* v_n_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0(v_a_340_, v_n_341_);
lean_dec(v_n_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
if (lean_obj_tag(v_x_346_) == 0)
{
return v_x_345_;
}
else
{
lean_object* v_head_347_; lean_object* v_tail_348_; lean_object* v___x_349_; 
v_head_347_ = lean_ctor_get(v_x_346_, 0);
v_tail_348_ = lean_ctor_get(v_x_346_, 1);
v___x_349_ = lean_string_append(v_x_345_, v_head_347_);
v_x_345_ = v___x_349_;
v_x_346_ = v_tail_348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0___boxed(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(v_x_351_, v_x_352_);
lean_dec(v_x_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(lean_object* v_l_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___closed__0));
v___x_357_ = l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(v___x_356_, v_l_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___boxed(lean_object* v_l_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v_l_358_);
lean_dec(v_l_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1___lam__0(lean_object* v_x_362_){
_start:
{
lean_object* v_fst_363_; lean_object* v_snd_364_; lean_object* v___x_365_; lean_object* v___y_367_; lean_object* v_intZero_375_; uint8_t v_isNeg_376_; 
v_fst_363_ = lean_ctor_get(v_x_362_, 0);
v_snd_364_ = lean_ctor_get(v_x_362_, 1);
v___x_365_ = ((lean_object*)(l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__0));
v_intZero_375_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_376_ = lean_int_dec_lt(v_fst_363_, v_intZero_375_);
if (v_isNeg_376_ == 0)
{
lean_object* v_a_377_; lean_object* v___x_378_; 
v_a_377_ = lean_nat_abs(v_fst_363_);
v___x_378_ = l_Nat_reprFast(v_a_377_);
v___y_367_ = v___x_378_;
goto v___jp_366_;
}
else
{
lean_object* v_abs_379_; lean_object* v_one_380_; lean_object* v_a_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_abs_379_ = lean_nat_abs(v_fst_363_);
v_one_380_ = lean_unsigned_to_nat(1u);
v_a_381_ = lean_nat_sub(v_abs_379_, v_one_380_);
lean_dec(v_abs_379_);
v___x_382_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_383_ = lean_nat_add(v_a_381_, v_one_380_);
lean_dec(v_a_381_);
v___x_384_ = l_Nat_reprFast(v___x_383_);
v___x_385_ = lean_string_append(v___x_382_, v___x_384_);
lean_dec_ref(v___x_384_);
v___y_367_ = v___x_385_;
goto v___jp_366_;
}
v___jp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_368_ = lean_string_append(v___x_365_, v___y_367_);
lean_dec_ref(v___y_367_);
v___x_369_ = ((lean_object*)(l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__1));
v___x_370_ = lean_string_append(v___x_368_, v___x_369_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_snd_364_, v___x_371_);
v___x_373_ = l_Nat_reprFast(v___x_372_);
v___x_374_ = lean_string_append(v___x_370_, v___x_373_);
lean_dec_ref(v___x_373_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___boxed(lean_object* v_x_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Omega_LinearCombo_instToString___private__1___lam__0(v_x_386_);
lean_dec_ref(v_x_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___private__1(lean_object* v_lc_389_){
_start:
{
lean_object* v_const_390_; lean_object* v_coeffs_391_; lean_object* v___f_392_; lean_object* v___y_394_; lean_object* v_intZero_401_; uint8_t v_isNeg_402_; 
v_const_390_ = lean_ctor_get(v_lc_389_, 0);
lean_inc(v_const_390_);
v_coeffs_391_ = lean_ctor_get(v_lc_389_, 1);
lean_inc(v_coeffs_391_);
lean_dec_ref(v_lc_389_);
v___f_392_ = ((lean_object*)(l_Lean_Omega_LinearCombo_instToString___private__1___closed__0));
v_intZero_401_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_402_ = lean_int_dec_lt(v_const_390_, v_intZero_401_);
if (v_isNeg_402_ == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; 
v_a_403_ = lean_nat_abs(v_const_390_);
lean_dec(v_const_390_);
v___x_404_ = l_Nat_reprFast(v_a_403_);
v___y_394_ = v___x_404_;
goto v___jp_393_;
}
else
{
lean_object* v_abs_405_; lean_object* v_one_406_; lean_object* v_a_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_abs_405_ = lean_nat_abs(v_const_390_);
lean_dec(v_const_390_);
v_one_406_ = lean_unsigned_to_nat(1u);
v_a_407_ = lean_nat_sub(v_abs_405_, v_one_406_);
lean_dec(v_abs_405_);
v___x_408_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_409_ = lean_nat_add(v_a_407_, v_one_406_);
lean_dec(v_a_407_);
v___x_410_ = l_Nat_reprFast(v___x_409_);
v___x_411_ = lean_string_append(v___x_408_, v___x_410_);
lean_dec_ref(v___x_410_);
v___y_394_ = v___x_411_;
goto v___jp_393_;
}
v___jp_393_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = l_List_zipIdx___redArg(v_coeffs_391_, v___x_395_);
v___x_397_ = lean_box(0);
v___x_398_ = l_List_mapTR_loop___redArg(v___f_392_, v___x_396_, v___x_397_);
v___x_399_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v___x_398_);
lean_dec(v___x_398_);
v___x_400_ = lean_string_append(v___y_394_, v___x_399_);
lean_dec_ref(v___x_399_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instToString___lam__1(lean_object* v___f_412_, lean_object* v_lc_413_){
_start:
{
lean_object* v_const_414_; lean_object* v_coeffs_415_; lean_object* v___y_417_; lean_object* v_intZero_424_; uint8_t v_isNeg_425_; 
v_const_414_ = lean_ctor_get(v_lc_413_, 0);
lean_inc(v_const_414_);
v_coeffs_415_ = lean_ctor_get(v_lc_413_, 1);
lean_inc(v_coeffs_415_);
lean_dec_ref(v_lc_413_);
v_intZero_424_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v_isNeg_425_ = lean_int_dec_lt(v_const_414_, v_intZero_424_);
if (v_isNeg_425_ == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; 
v_a_426_ = lean_nat_abs(v_const_414_);
lean_dec(v_const_414_);
v___x_427_ = l_Nat_reprFast(v_a_426_);
v___y_417_ = v___x_427_;
goto v___jp_416_;
}
else
{
lean_object* v_abs_428_; lean_object* v_one_429_; lean_object* v_a_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_abs_428_ = lean_nat_abs(v_const_414_);
lean_dec(v_const_414_);
v_one_429_ = lean_unsigned_to_nat(1u);
v_a_430_ = lean_nat_sub(v_abs_428_, v_one_429_);
lean_dec(v_abs_428_);
v___x_431_ = ((lean_object*)(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1));
v___x_432_ = lean_nat_add(v_a_430_, v_one_429_);
lean_dec(v_a_430_);
v___x_433_ = l_Nat_reprFast(v___x_432_);
v___x_434_ = lean_string_append(v___x_431_, v___x_433_);
lean_dec_ref(v___x_433_);
v___y_417_ = v___x_434_;
goto v___jp_416_;
}
v___jp_416_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = l_List_zipIdx___redArg(v_coeffs_415_, v___x_418_);
v___x_420_ = lean_box(0);
v___x_421_ = l_List_mapTR_loop___redArg(v___f_412_, v___x_419_, v___x_420_);
v___x_422_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v___x_421_);
lean_dec(v___x_421_);
v___x_423_ = lean_string_append(v___y_417_, v___x_422_);
lean_dec_ref(v___x_422_);
return v___x_423_;
}
}
}
static lean_object* _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_to_int(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_Omega_LinearCombo_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_box(0);
v___x_441_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_440_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Omega_LinearCombo_instInhabited(void){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__1, &l_Lean_Omega_LinearCombo_instInhabited___closed__1_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__1);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Omega_LinearCombo_isAtom_spec__0(lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
if (lean_obj_tag(v_a_444_) == 0)
{
lean_object* v___x_446_; 
v___x_446_ = l_List_reverse___redArg(v_a_445_);
return v___x_446_;
}
else
{
lean_object* v_head_447_; lean_object* v_tail_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_459_; 
v_head_447_ = lean_ctor_get(v_a_444_, 0);
v_tail_448_ = lean_ctor_get(v_a_444_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_a_444_);
if (v_isSharedCheck_459_ == 0)
{
v___x_450_ = v_a_444_;
v_isShared_451_ = v_isSharedCheck_459_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_tail_448_);
lean_inc(v_head_447_);
lean_dec(v_a_444_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_459_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_453_ = lean_int_dec_eq(v_head_447_, v___x_452_);
if (v___x_453_ == 0)
{
lean_del_object(v___x_450_);
lean_dec(v_head_447_);
v_a_444_ = v_tail_448_;
goto _start;
}
else
{
lean_object* v___x_456_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v_a_445_);
v___x_456_ = v___x_450_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_head_447_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_a_445_);
v___x_456_ = v_reuseFailAlloc_458_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
v_a_444_ = v_tail_448_;
v_a_445_ = v___x_456_;
goto _start;
}
}
}
}
}
}
uint8_t l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__1(lean_object* v_x_460_){
_start:
{
if (lean_obj_tag(v_x_460_) == 0)
{
uint8_t v___x_461_; 
v___x_461_ = 1;
return v___x_461_;
}
else
{
lean_object* v_head_462_; lean_object* v_tail_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_head_462_ = lean_ctor_get(v_x_460_, 0);
v_tail_463_ = lean_ctor_get(v_x_460_, 1);
v___x_464_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_465_ = lean_int_dec_eq(v_head_462_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_467_ = lean_int_dec_eq(v_head_462_, v___x_466_);
if (v___x_467_ == 0)
{
return v___x_467_;
}
else
{
v_x_460_ = v_tail_463_;
goto _start;
}
}
else
{
v_x_460_ = v_tail_463_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_460_ = stack[0].m_obj;
uint8_t v_res_470_;
v_res_470_ = l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__1(v_x_460_);
stack->m_num = v_res_470_;
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__1___boxed(lean_object* v_x_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__1(v_x_471_);
lean_dec(v_x_471_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
uint8_t l_Lean_Omega_LinearCombo_isAtom(lean_object* v_a_474_){
_start:
{
lean_object* v_const_475_; lean_object* v_coeffs_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_const_475_ = lean_ctor_get(v_a_474_, 0);
lean_inc(v_const_475_);
v_coeffs_476_ = lean_ctor_get(v_a_474_, 1);
lean_inc(v_coeffs_476_);
lean_dec_ref(v_a_474_);
v___x_477_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_478_ = lean_int_dec_eq(v_const_475_, v___x_477_);
lean_dec(v_const_475_);
if (v___x_478_ == 0)
{
lean_dec(v_coeffs_476_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_479_ = lean_box(0);
lean_inc(v_coeffs_476_);
v___x_480_ = l_List_filterTR_loop___at___00Lean_Omega_LinearCombo_isAtom_spec__0(v_coeffs_476_, v___x_479_);
v___x_481_ = l_List_lengthTR___redArg(v___x_480_);
lean_dec(v___x_480_);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_dec_eq(v___x_481_, v___x_482_);
lean_dec(v___x_481_);
if (v___x_483_ == 0)
{
lean_dec(v_coeffs_476_);
return v___x_483_;
}
else
{
uint8_t v___x_484_; 
v___x_484_ = l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__1(v_coeffs_476_);
lean_dec(v_coeffs_476_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT void l_Lean_Omega_LinearCombo_isAtom_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_474_ = stack[0].m_obj;
uint8_t v_res_485_;
v_res_485_ = l_Lean_Omega_LinearCombo_isAtom(v_a_474_);
stack->m_num = v_res_485_;
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_isAtom___boxed(lean_object* v_a_486_){
_start:
{
uint8_t v_res_487_; lean_object* v_r_488_; 
v_res_487_ = l_Lean_Omega_LinearCombo_isAtom(v_a_486_);
v_r_488_ = lean_box(v_res_487_);
return v_r_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_eval(lean_object* v_lc_489_, lean_object* v_values_490_){
_start:
{
lean_object* v_const_491_; lean_object* v_coeffs_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_const_491_ = lean_ctor_get(v_lc_489_, 0);
v_coeffs_492_ = lean_ctor_get(v_lc_489_, 1);
v___x_493_ = l_Lean_Omega_IntList_dot(v_coeffs_492_, v_values_490_);
v___x_494_ = lean_int_add(v_const_491_, v___x_493_);
lean_dec(v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_eval___boxed(lean_object* v_lc_495_, lean_object* v_values_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Omega_LinearCombo_eval(v_lc_495_, v_values_496_);
lean_dec_ref(v_lc_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_coordinate(lean_object* v_i_498_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_499_ = lean_obj_once(&l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0, &l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once, _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
v___x_500_ = lean_box(0);
v___x_501_ = lean_obj_once(&l_Lean_Omega_LinearCombo_instInhabited___closed__0, &l_Lean_Omega_LinearCombo_instInhabited___closed__0_once, _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0);
v___x_502_ = l_Lean_Omega_IntList_set(v___x_500_, v_i_498_, v___x_501_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_499_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_coordinate___boxed(lean_object* v_i_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Omega_LinearCombo_coordinate(v_i_504_);
lean_dec(v_i_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_add(lean_object* v_l_u2081_506_, lean_object* v_l_u2082_507_){
_start:
{
lean_object* v_const_508_; lean_object* v_coeffs_509_; lean_object* v_const_510_; lean_object* v_coeffs_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_520_; 
v_const_508_ = lean_ctor_get(v_l_u2081_506_, 0);
lean_inc(v_const_508_);
v_coeffs_509_ = lean_ctor_get(v_l_u2081_506_, 1);
lean_inc(v_coeffs_509_);
lean_dec_ref(v_l_u2081_506_);
v_const_510_ = lean_ctor_get(v_l_u2082_507_, 0);
v_coeffs_511_ = lean_ctor_get(v_l_u2082_507_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_l_u2082_507_);
if (v_isSharedCheck_520_ == 0)
{
v___x_513_ = v_l_u2082_507_;
v_isShared_514_ = v_isSharedCheck_520_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_coeffs_511_);
lean_inc(v_const_510_);
lean_dec(v_l_u2082_507_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_520_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_515_ = lean_int_add(v_const_508_, v_const_510_);
lean_dec(v_const_510_);
lean_dec(v_const_508_);
v___x_516_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_coeffs_509_, v_coeffs_511_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v___x_516_);
lean_ctor_set(v___x_513_, 0, v___x_515_);
v___x_518_ = v___x_513_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_sub(lean_object* v_l_u2081_523_, lean_object* v_l_u2082_524_){
_start:
{
lean_object* v_const_525_; lean_object* v_coeffs_526_; lean_object* v_const_527_; lean_object* v_coeffs_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_537_; 
v_const_525_ = lean_ctor_get(v_l_u2081_523_, 0);
lean_inc(v_const_525_);
v_coeffs_526_ = lean_ctor_get(v_l_u2081_523_, 1);
lean_inc(v_coeffs_526_);
lean_dec_ref(v_l_u2081_523_);
v_const_527_ = lean_ctor_get(v_l_u2082_524_, 0);
v_coeffs_528_ = lean_ctor_get(v_l_u2082_524_, 1);
v_isSharedCheck_537_ = !lean_is_exclusive(v_l_u2082_524_);
if (v_isSharedCheck_537_ == 0)
{
v___x_530_ = v_l_u2082_524_;
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_coeffs_528_);
lean_inc(v_const_527_);
lean_dec(v_l_u2082_524_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_532_ = lean_int_sub(v_const_525_, v_const_527_);
lean_dec(v_const_527_);
lean_dec(v_const_525_);
v___x_533_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_coeffs_526_, v_coeffs_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v___x_533_);
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_535_ = v___x_530_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_neg(lean_object* v_lc_540_){
_start:
{
lean_object* v_const_541_; lean_object* v_coeffs_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_551_; 
v_const_541_ = lean_ctor_get(v_lc_540_, 0);
v_coeffs_542_ = lean_ctor_get(v_lc_540_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_lc_540_);
if (v_isSharedCheck_551_ == 0)
{
v___x_544_ = v_lc_540_;
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_coeffs_542_);
lean_inc(v_const_541_);
lean_dec(v_lc_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_546_ = lean_int_neg(v_const_541_);
lean_dec(v_const_541_);
v___x_547_ = l_Lean_Omega_IntList_neg(v_coeffs_542_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_547_);
lean_ctor_set(v___x_544_, 0, v___x_546_);
v___x_549_ = v___x_544_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_546_);
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
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_smul(lean_object* v_lc_554_, lean_object* v_i_555_){
_start:
{
lean_object* v_const_556_; lean_object* v_coeffs_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_566_; 
v_const_556_ = lean_ctor_get(v_lc_554_, 0);
v_coeffs_557_ = lean_ctor_get(v_lc_554_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_lc_554_);
if (v_isSharedCheck_566_ == 0)
{
v___x_559_ = v_lc_554_;
v_isShared_560_ = v_isSharedCheck_566_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_coeffs_557_);
lean_inc(v_const_556_);
lean_dec(v_lc_554_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_566_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_561_ = lean_int_mul(v_i_555_, v_const_556_);
lean_dec(v_const_556_);
v___x_562_ = l_Lean_Omega_IntList_smul(v_coeffs_557_, v_i_555_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v___x_562_);
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_564_ = v___x_559_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_smul___boxed(lean_object* v_lc_567_, lean_object* v_i_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Omega_LinearCombo_smul(v_lc_567_, v_i_568_);
lean_dec(v_i_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instHMulInt___lam__0(lean_object* v_i_570_, lean_object* v_lc_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Omega_LinearCombo_smul(v_lc_571_, v_i_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_instHMulInt___lam__0___boxed(lean_object* v_i_573_, lean_object* v_lc_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Omega_LinearCombo_instHMulInt___lam__0(v_i_573_, v_lc_574_);
lean_dec(v_i_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_LinearCombo_mul(lean_object* v_l_u2081_578_, lean_object* v_l_u2082_579_){
_start:
{
lean_object* v_const_580_; lean_object* v_const_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_const_580_ = lean_ctor_get(v_l_u2082_579_, 0);
lean_inc(v_const_580_);
v_const_581_ = lean_ctor_get(v_l_u2081_578_, 0);
lean_inc(v_const_581_);
v___x_582_ = l_Lean_Omega_LinearCombo_smul(v_l_u2081_578_, v_const_580_);
v___x_583_ = l_Lean_Omega_LinearCombo_smul(v_l_u2082_579_, v_const_581_);
v___x_584_ = l_Lean_Omega_LinearCombo_add(v___x_582_, v___x_583_);
v___x_585_ = lean_int_mul(v_const_581_, v_const_580_);
lean_dec(v_const_580_);
lean_dec(v_const_581_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l_Lean_Omega_LinearCombo_sub(v___x_584_, v___x_587_);
return v___x_588_;
}
}
lean_object* runtime_initialize_Init_Omega_Coeffs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Omega_LinearCombo(uint8_t builtin) {
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
