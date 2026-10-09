// Lean compiler output
// Module: Init.Data.Nat.Fold
// Imports: public import Init.Data.List.FinRange import Init.Data.Fin.Lemmas import Init.Data.List.Lemmas import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fold___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fold(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_any___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_any___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_allTR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allTR___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4_value;
static const lean_array_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7_value;
static const lean_string_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9_value;
static const lean_string_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13;
static const lean_string_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value_aux_2),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9_value),((lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5_value)}};
static const lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16 = (const lean_object*)&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16_value;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25;
static lean_once_cell_t l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3;
LEAN_EXPORT lean_object* l_Nat_dfold___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_dfold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_dfold(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_dfoldRev___auto__1;
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_dfoldRev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_dfold__zero___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5;
LEAN_EXPORT lean_object* l_Nat_dfold__succ___auto__3;
LEAN_EXPORT lean_object* l_Nat_dfold__congr___auto__1;
LEAN_EXPORT lean_object* l_Nat_dfold__add___auto__5;
LEAN_EXPORT lean_object* l_Nat_dfoldRev__zero___auto__1;
LEAN_EXPORT lean_object* l_Nat_dfoldRev__succ___auto__3;
LEAN_EXPORT lean_object* l_Nat_dfoldRev__congr___auto__1;
LEAN_EXPORT lean_object* l_Nat_dfoldRev__add___auto__5;
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_foldI___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_foldI(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Prod_anyI___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_anyI___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Prod_anyI(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_anyI___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Prod_allI(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_allI___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_fold___redArg___lam__0(lean_object* v_x_1_, lean_object* v_i_2_, lean_object* v_h_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_apply_3(v_x_1_, v_i_2_, lean_box(0), v___y_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Nat_fold___redArg(lean_object* v_x_6_, lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
lean_object* v_zero_9_; uint8_t v_isZero_10_; 
v_zero_9_ = lean_unsigned_to_nat(0u);
v_isZero_10_ = lean_nat_dec_eq(v_x_6_, v_zero_9_);
if (v_isZero_10_ == 1)
{
lean_dec(v_x_7_);
lean_inc(v_x_8_);
return v_x_8_;
}
else
{
lean_object* v___f_11_; lean_object* v_one_12_; lean_object* v_n_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
lean_inc(v_x_7_);
v___f_11_ = lean_alloc_closure((void*)(l_Nat_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_11_, 0, v_x_7_);
v_one_12_ = lean_unsigned_to_nat(1u);
v_n_13_ = lean_nat_sub(v_x_6_, v_one_12_);
v___x_14_ = l_Nat_fold___redArg(v_n_13_, v___f_11_, v_x_8_);
v___x_15_ = lean_apply_3(v_x_7_, v_n_13_, lean_box(0), v___x_14_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_fold___redArg___boxed(lean_object* v_x_16_, lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Nat_fold___redArg(v_x_16_, v_x_17_, v_x_18_);
lean_dec(v_x_18_);
lean_dec(v_x_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Nat_fold(lean_object* v_00_u03b1_20_, lean_object* v_x_21_, lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Nat_fold___redArg(v_x_21_, v_x_22_, v_x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Nat_fold___boxed(lean_object* v_00_u03b1_25_, lean_object* v_x_26_, lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Nat_fold(v_00_u03b1_25_, v_x_26_, v_x_27_, v_x_28_);
lean_dec(v_x_28_);
lean_dec(v_x_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(lean_object* v_n_30_, lean_object* v_f_31_, lean_object* v_j_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_zero_34_; uint8_t v_isZero_35_; 
v_zero_34_ = lean_unsigned_to_nat(0u);
v_isZero_35_ = lean_nat_dec_eq(v_j_32_, v_zero_34_);
if (v_isZero_35_ == 1)
{
lean_dec(v_j_32_);
lean_dec(v_f_31_);
return v_a_33_;
}
else
{
lean_object* v_one_36_; lean_object* v_n_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_one_36_ = lean_unsigned_to_nat(1u);
v_n_37_ = lean_nat_sub(v_j_32_, v_one_36_);
v___x_38_ = lean_nat_sub(v_n_30_, v_j_32_);
lean_dec(v_j_32_);
lean_inc(v_f_31_);
v___x_39_ = lean_apply_3(v_f_31_, v___x_38_, lean_box(0), v_a_33_);
v_j_32_ = v_n_37_;
v_a_33_ = v___x_39_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg___boxed(lean_object* v_n_41_, lean_object* v_f_42_, lean_object* v_j_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v_n_41_, v_f_42_, v_j_43_, v_a_44_);
lean_dec(v_n_41_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_object* v_00_u03b1_46_, lean_object* v_n_47_, lean_object* v_f_48_, lean_object* v_j_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v_n_47_, v_f_48_, v_j_49_, v_a_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___boxed(lean_object* v_00_u03b1_53_, lean_object* v_n_54_, lean_object* v_f_55_, lean_object* v_j_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(v_00_u03b1_53_, v_n_54_, v_f_55_, v_j_56_, v_a_57_, v_a_58_);
lean_dec(v_n_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR___redArg(lean_object* v_n_60_, lean_object* v_f_61_, lean_object* v_init_62_){
_start:
{
lean_object* v___x_63_; 
lean_inc(v_n_60_);
v___x_63_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v_n_60_, v_f_61_, v_n_60_, v_init_62_);
lean_dec(v_n_60_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR(lean_object* v_00_u03b1_64_, lean_object* v_n_65_, lean_object* v_f_66_, lean_object* v_init_67_){
_start:
{
lean_object* v___x_68_; 
lean_inc(v_n_65_);
v___x_68_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v_n_65_, v_f_66_, v_n_65_, v_init_67_);
lean_dec(v_n_65_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___redArg(lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
lean_object* v_zero_72_; uint8_t v_isZero_73_; 
v_zero_72_ = lean_unsigned_to_nat(0u);
v_isZero_73_ = lean_nat_dec_eq(v_x_69_, v_zero_72_);
if (v_isZero_73_ == 1)
{
lean_dec(v_x_70_);
lean_dec(v_x_69_);
return v_x_71_;
}
else
{
lean_object* v___f_74_; lean_object* v_one_75_; lean_object* v_n_76_; lean_object* v___x_77_; 
lean_inc(v_x_70_);
v___f_74_ = lean_alloc_closure((void*)(l_Nat_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_74_, 0, v_x_70_);
v_one_75_ = lean_unsigned_to_nat(1u);
v_n_76_ = lean_nat_sub(v_x_69_, v_one_75_);
lean_dec(v_x_69_);
lean_inc(v_n_76_);
v___x_77_ = lean_apply_3(v_x_70_, v_n_76_, lean_box(0), v_x_71_);
v_x_69_ = v_n_76_;
v_x_70_ = v___f_74_;
v_x_71_ = v___x_77_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev(lean_object* v_00_u03b1_79_, lean_object* v_x_80_, lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Nat_foldRev___redArg(v_x_80_, v_x_81_, v_x_82_);
return v___x_83_;
}
}
uint8_t l_Nat_any___lam__0(lean_object* v_x_84_, lean_object* v_i_85_, lean_object* v_h_86_){
_start:
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = lean_apply_2(v_x_84_, v_i_85_, lean_box(0));
v___x_88_ = lean_unbox(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT void l_Nat_any___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_84_ = stack[0].m_obj;
lean_object* v_i_85_ = stack[1].m_obj;
uint8_t v_res_89_;
v_res_89_ = l_Nat_any___lam__0(v_x_84_, v_i_85_, lean_box(0));
stack->m_num = v_res_89_;
}
LEAN_EXPORT lean_object* l_Nat_any___lam__0___boxed(lean_object* v_x_90_, lean_object* v_i_91_, lean_object* v_h_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Nat_any___lam__0(v_x_90_, v_i_91_, v_h_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
uint8_t l_Nat_any(lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_zero_97_; uint8_t v_isZero_98_; 
v_zero_97_ = lean_unsigned_to_nat(0u);
v_isZero_98_ = lean_nat_dec_eq(v_x_95_, v_zero_97_);
if (v_isZero_98_ == 1)
{
uint8_t v___x_99_; 
lean_dec_ref(v_x_96_);
v___x_99_ = 0;
return v___x_99_;
}
else
{
lean_object* v___f_100_; lean_object* v_one_101_; lean_object* v_n_102_; uint8_t v___x_103_; 
lean_inc_ref(v_x_96_);
v___f_100_ = lean_alloc_closure((void*)(l_Nat_any___lam__0___boxed), 3, 1);
lean_closure_set(v___f_100_, 0, v_x_96_);
v_one_101_ = lean_unsigned_to_nat(1u);
v_n_102_ = lean_nat_sub(v_x_95_, v_one_101_);
v___x_103_ = l_Nat_any(v_n_102_, v___f_100_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_apply_2(v_x_96_, v_n_102_, lean_box(0));
v___x_105_ = lean_unbox(v___x_104_);
return v___x_105_;
}
else
{
lean_dec(v_n_102_);
lean_dec_ref(v_x_96_);
return v___x_103_;
}
}
}
}
LEAN_EXPORT void l_Nat_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_95_ = stack[0].m_obj;
lean_object* v_x_96_ = stack[1].m_obj;
uint8_t v_res_106_;
v_res_106_ = l_Nat_any(v_x_95_, v_x_96_);
stack->m_num = v_res_106_;
}
LEAN_EXPORT lean_object* l_Nat_any___boxed(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Nat_any(v_x_107_, v_x_108_);
lean_dec(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(lean_object* v_n_111_, lean_object* v_f_112_, lean_object* v_i_113_){
_start:
{
lean_object* v_zero_114_; uint8_t v_isZero_115_; 
v_zero_114_ = lean_unsigned_to_nat(0u);
v_isZero_115_ = lean_nat_dec_eq(v_i_113_, v_zero_114_);
if (v_isZero_115_ == 1)
{
uint8_t v___x_116_; 
lean_dec(v_i_113_);
lean_dec_ref(v_f_112_);
v___x_116_ = 0;
return v___x_116_;
}
else
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_nat_sub(v_n_111_, v_i_113_);
lean_inc_ref(v_f_112_);
v___x_118_ = lean_apply_2(v_f_112_, v___x_117_, lean_box(0));
v___x_119_ = lean_unbox(v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v_one_120_; lean_object* v_n_121_; 
v_one_120_ = lean_unsigned_to_nat(1u);
v_n_121_ = lean_nat_sub(v_i_113_, v_one_120_);
lean_dec(v_i_113_);
v_i_113_ = v_n_121_;
goto _start;
}
else
{
uint8_t v___x_123_; 
lean_dec(v_i_113_);
lean_dec_ref(v_f_112_);
v___x_123_ = lean_unbox(v___x_118_);
return v___x_123_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_111_ = stack[0].m_obj;
lean_object* v_f_112_ = stack[1].m_obj;
lean_object* v_i_113_ = stack[2].m_obj;
uint8_t v_res_124_;
v_res_124_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_111_, v_f_112_, v_i_113_);
stack->m_num = v_res_124_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg___boxed(lean_object* v_n_125_, lean_object* v_f_126_, lean_object* v_i_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_125_, v_f_126_, v_i_127_);
lean_dec(v_n_125_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(lean_object* v_n_130_, lean_object* v_f_131_, lean_object* v_i_132_, lean_object* v_a_133_){
_start:
{
uint8_t v___x_134_; 
v___x_134_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_130_, v_f_131_, v_i_132_);
return v___x_134_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_130_ = stack[0].m_obj;
lean_object* v_f_131_ = stack[1].m_obj;
lean_object* v_i_132_ = stack[2].m_obj;
uint8_t v_res_135_;
v_res_135_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(v_n_130_, v_f_131_, v_i_132_, lean_box(0));
stack->m_num = v_res_135_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___boxed(lean_object* v_n_136_, lean_object* v_f_137_, lean_object* v_i_138_, lean_object* v_a_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(v_n_136_, v_f_137_, v_i_138_, v_a_139_);
lean_dec(v_n_136_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
uint8_t l_Nat_anyTR(lean_object* v_n_142_, lean_object* v_f_143_){
_start:
{
uint8_t v___x_144_; 
lean_inc(v_n_142_);
v___x_144_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_142_, v_f_143_, v_n_142_);
lean_dec(v_n_142_);
return v___x_144_;
}
}
LEAN_EXPORT void l_Nat_anyTR_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_142_ = stack[0].m_obj;
lean_object* v_f_143_ = stack[1].m_obj;
uint8_t v_res_145_;
v_res_145_ = l_Nat_anyTR(v_n_142_, v_f_143_);
stack->m_num = v_res_145_;
}
LEAN_EXPORT lean_object* l_Nat_anyTR___boxed(lean_object* v_n_146_, lean_object* v_f_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Nat_anyTR(v_n_146_, v_f_147_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
uint8_t l_Nat_all(lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
lean_object* v_zero_152_; uint8_t v_isZero_153_; 
v_zero_152_ = lean_unsigned_to_nat(0u);
v_isZero_153_ = lean_nat_dec_eq(v_x_150_, v_zero_152_);
if (v_isZero_153_ == 1)
{
lean_dec_ref(v_x_151_);
return v_isZero_153_;
}
else
{
lean_object* v___f_154_; lean_object* v_one_155_; lean_object* v_n_156_; uint8_t v___x_157_; 
lean_inc_ref(v_x_151_);
v___f_154_ = lean_alloc_closure((void*)(l_Nat_any___lam__0___boxed), 3, 1);
lean_closure_set(v___f_154_, 0, v_x_151_);
v_one_155_ = lean_unsigned_to_nat(1u);
v_n_156_ = lean_nat_sub(v_x_150_, v_one_155_);
v___x_157_ = l_Nat_all(v_n_156_, v___f_154_);
if (v___x_157_ == 0)
{
lean_dec(v_n_156_);
lean_dec_ref(v_x_151_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_apply_2(v_x_151_, v_n_156_, lean_box(0));
v___x_159_ = lean_unbox(v___x_158_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT void l_Nat_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_150_ = stack[0].m_obj;
lean_object* v_x_151_ = stack[1].m_obj;
uint8_t v_res_160_;
v_res_160_ = l_Nat_all(v_x_150_, v_x_151_);
stack->m_num = v_res_160_;
}
LEAN_EXPORT lean_object* l_Nat_all___boxed(lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Nat_all(v_x_161_, v_x_162_);
lean_dec(v_x_161_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(lean_object* v_n_165_, lean_object* v_f_166_, lean_object* v_i_167_){
_start:
{
lean_object* v_zero_168_; uint8_t v_isZero_169_; 
v_zero_168_ = lean_unsigned_to_nat(0u);
v_isZero_169_ = lean_nat_dec_eq(v_i_167_, v_zero_168_);
if (v_isZero_169_ == 1)
{
lean_dec(v_i_167_);
lean_dec_ref(v_f_166_);
return v_isZero_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_170_ = lean_nat_sub(v_n_165_, v_i_167_);
lean_inc_ref(v_f_166_);
v___x_171_ = lean_apply_2(v_f_166_, v___x_170_, lean_box(0));
v___x_172_ = lean_unbox(v___x_171_);
if (v___x_172_ == 0)
{
uint8_t v___x_173_; 
lean_dec(v_i_167_);
lean_dec_ref(v_f_166_);
v___x_173_ = lean_unbox(v___x_171_);
return v___x_173_;
}
else
{
lean_object* v_one_174_; lean_object* v_n_175_; 
v_one_174_ = lean_unsigned_to_nat(1u);
v_n_175_ = lean_nat_sub(v_i_167_, v_one_174_);
lean_dec(v_i_167_);
v_i_167_ = v_n_175_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_165_ = stack[0].m_obj;
lean_object* v_f_166_ = stack[1].m_obj;
lean_object* v_i_167_ = stack[2].m_obj;
uint8_t v_res_177_;
v_res_177_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_165_, v_f_166_, v_i_167_);
stack->m_num = v_res_177_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg___boxed(lean_object* v_n_178_, lean_object* v_f_179_, lean_object* v_i_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_178_, v_f_179_, v_i_180_);
lean_dec(v_n_178_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(lean_object* v_n_183_, lean_object* v_f_184_, lean_object* v_i_185_, lean_object* v_a_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_183_, v_f_184_, v_i_185_);
return v___x_187_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_183_ = stack[0].m_obj;
lean_object* v_f_184_ = stack[1].m_obj;
lean_object* v_i_185_ = stack[2].m_obj;
uint8_t v_res_188_;
v_res_188_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(v_n_183_, v_f_184_, v_i_185_, lean_box(0));
stack->m_num = v_res_188_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___boxed(lean_object* v_n_189_, lean_object* v_f_190_, lean_object* v_i_191_, lean_object* v_a_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(v_n_189_, v_f_190_, v_i_191_, v_a_192_);
lean_dec(v_n_189_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
uint8_t l_Nat_allTR(lean_object* v_n_195_, lean_object* v_f_196_){
_start:
{
uint8_t v___x_197_; 
lean_inc(v_n_195_);
v___x_197_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_195_, v_f_196_, v_n_195_);
lean_dec(v_n_195_);
return v___x_197_;
}
}
LEAN_EXPORT void l_Nat_allTR_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_195_ = stack[0].m_obj;
lean_object* v_f_196_ = stack[1].m_obj;
uint8_t v_res_198_;
v_res_198_ = l_Nat_allTR(v_n_195_, v_f_196_);
stack->m_num = v_res_198_;
}
LEAN_EXPORT lean_object* l_Nat_allTR___boxed(lean_object* v_n_199_, lean_object* v_f_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Nat_allTR(v_n_199_, v_f_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10));
v___x_230_ = l_Lean_mkAtom(v___x_229_);
return v___x_230_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12);
v___x_232_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_233_ = lean_array_push(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16));
v___x_245_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_246_ = lean_array_push(v___x_245_, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_247_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17);
v___x_248_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15));
v___x_249_ = lean_box(2);
v___x_250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_248_);
lean_ctor_set(v___x_250_, 2, v___x_247_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18);
v___x_252_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13);
v___x_253_ = lean_array_push(v___x_252_, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19);
v___x_255_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11));
v___x_256_ = lean_box(2);
v___x_257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
lean_ctor_set(v___x_257_, 2, v___x_254_);
return v___x_257_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20);
v___x_259_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_260_ = lean_array_push(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21);
v___x_262_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9));
v___x_263_ = lean_box(2);
v___x_264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_261_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22);
v___x_266_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_267_ = lean_array_push(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23);
v___x_269_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7));
v___x_270_ = lean_box(2);
v___x_271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
lean_ctor_set(v___x_271_, 2, v___x_268_);
return v___x_271_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24);
v___x_273_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_274_ = lean_array_push(v___x_273_, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25);
v___x_276_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4));
v___x_277_ = lean_box(2);
v___x_278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
lean_ctor_set(v___x_278_, 2, v___x_275_);
return v___x_278_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(lean_object* v_x_280_){
_start:
{
lean_inc(v_x_280_);
return v_x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg___boxed(lean_object* v_x_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(v_x_281_);
lean_dec(v_x_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(lean_object* v_n_283_, lean_object* v_00_u03b1_284_, lean_object* v_i_285_, lean_object* v_j_286_, lean_object* v_hi_287_, lean_object* v_w_288_, lean_object* v_x_289_){
_start:
{
lean_inc(v_x_289_);
return v_x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___boxed(lean_object* v_n_290_, lean_object* v_00_u03b1_291_, lean_object* v_i_292_, lean_object* v_j_293_, lean_object* v_hi_294_, lean_object* v_w_295_, lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(v_n_290_, v_00_u03b1_291_, v_i_292_, v_j_293_, v_hi_294_, v_w_295_, v_x_296_);
lean_dec(v_x_296_);
lean_dec(v_j_293_);
lean_dec(v_i_292_);
lean_dec(v_n_290_);
return v_res_297_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9(void){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_298_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3(void){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_299_;
}
}
static lean_object* _init_l_Nat_dfold___auto__1(void){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(lean_object* v_n_301_, lean_object* v_f_302_, lean_object* v_j_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_zero_305_; uint8_t v_isZero_306_; 
v_zero_305_ = lean_unsigned_to_nat(0u);
v_isZero_306_ = lean_nat_dec_eq(v_j_303_, v_zero_305_);
if (v_isZero_306_ == 1)
{
lean_dec(v_j_303_);
lean_dec(v_f_302_);
return v_a_304_;
}
else
{
lean_object* v_one_307_; lean_object* v_n_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_one_307_ = lean_unsigned_to_nat(1u);
v_n_308_ = lean_nat_sub(v_j_303_, v_one_307_);
v___x_309_ = lean_nat_sub(v_n_301_, v_j_303_);
lean_dec(v_j_303_);
lean_inc(v_f_302_);
v___x_310_ = lean_apply_3(v_f_302_, v___x_309_, lean_box(0), v_a_304_);
v_j_303_ = v_n_308_;
v_a_304_ = v___x_310_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg___boxed(lean_object* v_n_312_, lean_object* v_f_313_, lean_object* v_j_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_312_, v_f_313_, v_j_314_, v_a_315_);
lean_dec(v_n_312_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(lean_object* v_n_317_, lean_object* v_00_u03b1_318_, lean_object* v_f_319_, lean_object* v_j_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_317_, v_f_319_, v_j_320_, v_a_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___boxed(lean_object* v_n_324_, lean_object* v_00_u03b1_325_, lean_object* v_f_326_, lean_object* v_j_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(v_n_324_, v_00_u03b1_325_, v_f_326_, v_j_327_, v_a_328_, v_a_329_);
lean_dec(v_n_324_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfold___redArg(lean_object* v_n_331_, lean_object* v_f_332_, lean_object* v_init_333_){
_start:
{
lean_object* v___x_334_; 
lean_inc(v_n_331_);
v___x_334_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_331_, v_f_332_, v_n_331_, v_init_333_);
lean_dec(v_n_331_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfold(lean_object* v_n_335_, lean_object* v_00_u03b1_336_, lean_object* v_f_337_, lean_object* v_init_338_){
_start:
{
lean_object* v___x_339_; 
lean_inc(v_n_335_);
v___x_339_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_335_, v_f_337_, v_n_335_, v_init_338_);
lean_dec(v_n_335_);
return v___x_339_;
}
}
static lean_object* _init_l_Nat_dfoldRev___auto__1(void){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg___lam__0(lean_object* v_f_341_, lean_object* v_i_342_, lean_object* v_h_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_apply_3(v_f_341_, v_i_342_, lean_box(0), v___y_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg(lean_object* v_n_346_, lean_object* v_f_347_, lean_object* v_init_348_){
_start:
{
lean_object* v_zero_349_; uint8_t v_isZero_350_; 
v_zero_349_ = lean_unsigned_to_nat(0u);
v_isZero_350_ = lean_nat_dec_eq(v_n_346_, v_zero_349_);
if (v_isZero_350_ == 1)
{
lean_dec(v_f_347_);
lean_dec(v_n_346_);
return v_init_348_;
}
else
{
lean_object* v___f_351_; lean_object* v_one_352_; lean_object* v_n_353_; lean_object* v___x_354_; 
lean_inc(v_f_347_);
v___f_351_ = lean_alloc_closure((void*)(l_Nat_dfoldRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_351_, 0, v_f_347_);
v_one_352_ = lean_unsigned_to_nat(1u);
v_n_353_ = lean_nat_sub(v_n_346_, v_one_352_);
lean_dec(v_n_346_);
lean_inc(v_n_353_);
v___x_354_ = lean_apply_3(v_f_347_, v_n_353_, lean_box(0), v_init_348_);
v_n_346_ = v_n_353_;
v_f_347_ = v___f_351_;
v_init_348_ = v___x_354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev(lean_object* v_n_356_, lean_object* v_00_u03b1_357_, lean_object* v_f_358_, lean_object* v_init_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Nat_dfoldRev___redArg(v_n_356_, v_f_358_, v_init_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Nat_dfold__zero___auto__1(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_361_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_362_;
}
}
static lean_object* _init_l_Nat_dfold__succ___auto__3(void){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_363_;
}
}
static lean_object* _init_l_Nat_dfold__congr___auto__1(void){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_364_;
}
}
static lean_object* _init_l_Nat_dfold__add___auto__5(void){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_365_;
}
}
static lean_object* _init_l_Nat_dfoldRev__zero___auto__1(void){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_366_;
}
}
static lean_object* _init_l_Nat_dfoldRev__succ___auto__3(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_367_;
}
}
static lean_object* _init_l_Nat_dfoldRev__congr___auto__1(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_368_;
}
}
static lean_object* _init_l_Nat_dfoldRev__add___auto__5(void){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0(lean_object* v_fst_370_, lean_object* v_f_371_, lean_object* v_j_372_, lean_object* v_x_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_nat_add(v_fst_370_, v_j_372_);
v___x_376_ = lean_apply_4(v_f_371_, v___x_375_, lean_box(0), lean_box(0), v___y_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0___boxed(lean_object* v_fst_377_, lean_object* v_f_378_, lean_object* v_j_379_, lean_object* v_x_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Prod_foldI___redArg___lam__0(v_fst_377_, v_f_378_, v_j_379_, v_x_380_, v___y_381_);
lean_dec(v_j_379_);
lean_dec(v_fst_377_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg(lean_object* v_i_383_, lean_object* v_f_384_, lean_object* v_init_385_){
_start:
{
lean_object* v_fst_386_; lean_object* v_snd_387_; lean_object* v___f_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_fst_386_ = lean_ctor_get(v_i_383_, 0);
lean_inc_n(v_fst_386_, 2);
v_snd_387_ = lean_ctor_get(v_i_383_, 1);
lean_inc(v_snd_387_);
lean_dec_ref(v_i_383_);
v___f_388_ = lean_alloc_closure((void*)(l_Prod_foldI___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_388_, 0, v_fst_386_);
lean_closure_set(v___f_388_, 1, v_f_384_);
v___x_389_ = lean_nat_sub(v_snd_387_, v_fst_386_);
lean_dec(v_fst_386_);
lean_dec(v_snd_387_);
lean_inc(v___x_389_);
v___x_390_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v___x_389_, v___f_388_, v___x_389_, v_init_385_);
lean_dec(v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI(lean_object* v_00_u03b1_391_, lean_object* v_i_392_, lean_object* v_f_393_, lean_object* v_init_394_){
_start:
{
lean_object* v_fst_395_; lean_object* v_snd_396_; lean_object* v___f_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_fst_395_ = lean_ctor_get(v_i_392_, 0);
lean_inc_n(v_fst_395_, 2);
v_snd_396_ = lean_ctor_get(v_i_392_, 1);
lean_inc(v_snd_396_);
lean_dec_ref(v_i_392_);
v___f_397_ = lean_alloc_closure((void*)(l_Prod_foldI___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_397_, 0, v_fst_395_);
lean_closure_set(v___f_397_, 1, v_f_393_);
v___x_398_ = lean_nat_sub(v_snd_396_, v_fst_395_);
lean_dec(v_fst_395_);
lean_dec(v_snd_396_);
lean_inc(v___x_398_);
v___x_399_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v___x_398_, v___f_397_, v___x_398_, v_init_394_);
lean_dec(v___x_398_);
return v___x_399_;
}
}
uint8_t l_Prod_anyI___lam__0(lean_object* v_fst_400_, lean_object* v_f_401_, lean_object* v_j_402_, lean_object* v_x_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_nat_add(v_fst_400_, v_j_402_);
v___x_405_ = lean_apply_3(v_f_401_, v___x_404_, lean_box(0), lean_box(0));
v___x_406_ = lean_unbox(v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT void l_Prod_anyI___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_400_ = stack[0].m_obj;
lean_object* v_f_401_ = stack[1].m_obj;
lean_object* v_j_402_ = stack[2].m_obj;
uint8_t v_res_407_;
v_res_407_ = l_Prod_anyI___lam__0(v_fst_400_, v_f_401_, v_j_402_, lean_box(0));
stack->m_num = v_res_407_;
}
LEAN_EXPORT lean_object* l_Prod_anyI___lam__0___boxed(lean_object* v_fst_408_, lean_object* v_f_409_, lean_object* v_j_410_, lean_object* v_x_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Prod_anyI___lam__0(v_fst_408_, v_f_409_, v_j_410_, v_x_411_);
lean_dec(v_j_410_);
lean_dec(v_fst_408_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
uint8_t l_Prod_anyI(lean_object* v_i_414_, lean_object* v_f_415_){
_start:
{
lean_object* v_fst_416_; lean_object* v_snd_417_; lean_object* v___f_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_fst_416_ = lean_ctor_get(v_i_414_, 0);
lean_inc_n(v_fst_416_, 2);
v_snd_417_ = lean_ctor_get(v_i_414_, 1);
lean_inc(v_snd_417_);
lean_dec_ref(v_i_414_);
v___f_418_ = lean_alloc_closure((void*)(l_Prod_anyI___lam__0___boxed), 4, 2);
lean_closure_set(v___f_418_, 0, v_fst_416_);
lean_closure_set(v___f_418_, 1, v_f_415_);
v___x_419_ = lean_nat_sub(v_snd_417_, v_fst_416_);
lean_dec(v_fst_416_);
lean_dec(v_snd_417_);
lean_inc(v___x_419_);
v___x_420_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v___x_419_, v___f_418_, v___x_419_);
lean_dec(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT void l_Prod_anyI_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_414_ = stack[0].m_obj;
lean_object* v_f_415_ = stack[1].m_obj;
uint8_t v_res_421_;
v_res_421_ = l_Prod_anyI(v_i_414_, v_f_415_);
stack->m_num = v_res_421_;
}
LEAN_EXPORT lean_object* l_Prod_anyI___boxed(lean_object* v_i_422_, lean_object* v_f_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Prod_anyI(v_i_422_, v_f_423_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
uint8_t l_Prod_allI(lean_object* v_i_426_, lean_object* v_f_427_){
_start:
{
lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v___f_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_fst_428_ = lean_ctor_get(v_i_426_, 0);
lean_inc_n(v_fst_428_, 2);
v_snd_429_ = lean_ctor_get(v_i_426_, 1);
lean_inc(v_snd_429_);
lean_dec_ref(v_i_426_);
v___f_430_ = lean_alloc_closure((void*)(l_Prod_anyI___lam__0___boxed), 4, 2);
lean_closure_set(v___f_430_, 0, v_fst_428_);
lean_closure_set(v___f_430_, 1, v_f_427_);
v___x_431_ = lean_nat_sub(v_snd_429_, v_fst_428_);
lean_dec(v_fst_428_);
lean_dec(v_snd_429_);
lean_inc(v___x_431_);
v___x_432_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v___x_431_, v___f_430_, v___x_431_);
lean_dec(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT void l_Prod_allI_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_426_ = stack[0].m_obj;
lean_object* v_f_427_ = stack[1].m_obj;
uint8_t v_res_433_;
v_res_433_ = l_Prod_allI(v_i_426_, v_f_427_);
stack->m_num = v_res_433_;
}
LEAN_EXPORT lean_object* l_Prod_allI___boxed(lean_object* v_i_434_, lean_object* v_f_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_Prod_allI(v_i_434_, v_f_435_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
lean_object* runtime_initialize_Init_Data_List_FinRange(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_FinRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Fold(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1 = _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1();
lean_mark_persistent(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1);
l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9 = _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9();
lean_mark_persistent(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9);
l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3 = _init_l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3();
lean_mark_persistent(l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3);
l_Nat_dfold___auto__1 = _init_l_Nat_dfold___auto__1();
lean_mark_persistent(l_Nat_dfold___auto__1);
l_Nat_dfoldRev___auto__1 = _init_l_Nat_dfoldRev___auto__1();
lean_mark_persistent(l_Nat_dfoldRev___auto__1);
l_Nat_dfold__zero___auto__1 = _init_l_Nat_dfold__zero___auto__1();
lean_mark_persistent(l_Nat_dfold__zero___auto__1);
l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5 = _init_l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5();
lean_mark_persistent(l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5);
l_Nat_dfold__succ___auto__3 = _init_l_Nat_dfold__succ___auto__3();
lean_mark_persistent(l_Nat_dfold__succ___auto__3);
l_Nat_dfold__congr___auto__1 = _init_l_Nat_dfold__congr___auto__1();
lean_mark_persistent(l_Nat_dfold__congr___auto__1);
l_Nat_dfold__add___auto__5 = _init_l_Nat_dfold__add___auto__5();
lean_mark_persistent(l_Nat_dfold__add___auto__5);
l_Nat_dfoldRev__zero___auto__1 = _init_l_Nat_dfoldRev__zero___auto__1();
lean_mark_persistent(l_Nat_dfoldRev__zero___auto__1);
l_Nat_dfoldRev__succ___auto__3 = _init_l_Nat_dfoldRev__succ___auto__3();
lean_mark_persistent(l_Nat_dfoldRev__succ___auto__3);
l_Nat_dfoldRev__congr___auto__1 = _init_l_Nat_dfoldRev__congr___auto__1();
lean_mark_persistent(l_Nat_dfoldRev__congr___auto__1);
l_Nat_dfoldRev__add___auto__5 = _init_l_Nat_dfoldRev__add___auto__5();
lean_mark_persistent(l_Nat_dfoldRev__add___auto__5);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_FinRange(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Fold(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_FinRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Fold(builtin);
}
#ifdef __cplusplus
}
#endif
