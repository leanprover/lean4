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
LEAN_EXPORT uint8_t l_Nat_any___lam__0(lean_object* v_x_84_, lean_object* v_i_85_, lean_object* v_h_86_){
_start:
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = lean_apply_2(v_x_84_, v_i_85_, lean_box(0));
v___x_88_ = lean_unbox(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Nat_any___lam__0___boxed(lean_object* v_x_89_, lean_object* v_i_90_, lean_object* v_h_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Nat_any___lam__0(v_x_89_, v_i_90_, v_h_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Nat_any(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_zero_96_; uint8_t v_isZero_97_; 
v_zero_96_ = lean_unsigned_to_nat(0u);
v_isZero_97_ = lean_nat_dec_eq(v_x_94_, v_zero_96_);
if (v_isZero_97_ == 1)
{
uint8_t v___x_98_; 
lean_dec_ref(v_x_95_);
v___x_98_ = 0;
return v___x_98_;
}
else
{
lean_object* v___f_99_; lean_object* v_one_100_; lean_object* v_n_101_; uint8_t v___x_102_; 
lean_inc_ref(v_x_95_);
v___f_99_ = lean_alloc_closure((void*)(l_Nat_any___lam__0___boxed), 3, 1);
lean_closure_set(v___f_99_, 0, v_x_95_);
v_one_100_ = lean_unsigned_to_nat(1u);
v_n_101_ = lean_nat_sub(v_x_94_, v_one_100_);
v___x_102_ = l_Nat_any(v_n_101_, v___f_99_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_apply_2(v_x_95_, v_n_101_, lean_box(0));
v___x_104_ = lean_unbox(v___x_103_);
return v___x_104_;
}
else
{
lean_dec(v_n_101_);
lean_dec_ref(v_x_95_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_any___boxed(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Nat_any(v_x_105_, v_x_106_);
lean_dec(v_x_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(lean_object* v_n_109_, lean_object* v_f_110_, lean_object* v_i_111_){
_start:
{
lean_object* v_zero_112_; uint8_t v_isZero_113_; 
v_zero_112_ = lean_unsigned_to_nat(0u);
v_isZero_113_ = lean_nat_dec_eq(v_i_111_, v_zero_112_);
if (v_isZero_113_ == 1)
{
uint8_t v___x_114_; 
lean_dec(v_i_111_);
lean_dec_ref(v_f_110_);
v___x_114_ = 0;
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_nat_sub(v_n_109_, v_i_111_);
lean_inc_ref(v_f_110_);
v___x_116_ = lean_apply_2(v_f_110_, v___x_115_, lean_box(0));
v___x_117_ = lean_unbox(v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v_one_118_; lean_object* v_n_119_; 
v_one_118_ = lean_unsigned_to_nat(1u);
v_n_119_ = lean_nat_sub(v_i_111_, v_one_118_);
lean_dec(v_i_111_);
v_i_111_ = v_n_119_;
goto _start;
}
else
{
uint8_t v___x_121_; 
lean_dec(v_i_111_);
lean_dec_ref(v_f_110_);
v___x_121_ = lean_unbox(v___x_116_);
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg___boxed(lean_object* v_n_122_, lean_object* v_f_123_, lean_object* v_i_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_122_, v_f_123_, v_i_124_);
lean_dec(v_n_122_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(lean_object* v_n_127_, lean_object* v_f_128_, lean_object* v_i_129_, lean_object* v_a_130_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_127_, v_f_128_, v_i_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___boxed(lean_object* v_n_132_, lean_object* v_f_133_, lean_object* v_i_134_, lean_object* v_a_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(v_n_132_, v_f_133_, v_i_134_, v_a_135_);
lean_dec(v_n_132_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR(lean_object* v_n_138_, lean_object* v_f_139_){
_start:
{
uint8_t v___x_140_; 
lean_inc(v_n_138_);
v___x_140_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_138_, v_f_139_, v_n_138_);
lean_dec(v_n_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR___boxed(lean_object* v_n_141_, lean_object* v_f_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Nat_anyTR(v_n_141_, v_f_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT uint8_t l_Nat_all(lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
lean_object* v_zero_147_; uint8_t v_isZero_148_; 
v_zero_147_ = lean_unsigned_to_nat(0u);
v_isZero_148_ = lean_nat_dec_eq(v_x_145_, v_zero_147_);
if (v_isZero_148_ == 1)
{
lean_dec_ref(v_x_146_);
return v_isZero_148_;
}
else
{
lean_object* v___f_149_; lean_object* v_one_150_; lean_object* v_n_151_; uint8_t v___x_152_; 
lean_inc_ref(v_x_146_);
v___f_149_ = lean_alloc_closure((void*)(l_Nat_any___lam__0___boxed), 3, 1);
lean_closure_set(v___f_149_, 0, v_x_146_);
v_one_150_ = lean_unsigned_to_nat(1u);
v_n_151_ = lean_nat_sub(v_x_145_, v_one_150_);
v___x_152_ = l_Nat_all(v_n_151_, v___f_149_);
if (v___x_152_ == 0)
{
lean_dec(v_n_151_);
lean_dec_ref(v_x_146_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_apply_2(v_x_146_, v_n_151_, lean_box(0));
v___x_154_ = lean_unbox(v___x_153_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_all___boxed(lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Nat_all(v_x_155_, v_x_156_);
lean_dec(v_x_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(lean_object* v_n_159_, lean_object* v_f_160_, lean_object* v_i_161_){
_start:
{
lean_object* v_zero_162_; uint8_t v_isZero_163_; 
v_zero_162_ = lean_unsigned_to_nat(0u);
v_isZero_163_ = lean_nat_dec_eq(v_i_161_, v_zero_162_);
if (v_isZero_163_ == 1)
{
lean_dec(v_i_161_);
lean_dec_ref(v_f_160_);
return v_isZero_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_164_ = lean_nat_sub(v_n_159_, v_i_161_);
lean_inc_ref(v_f_160_);
v___x_165_ = lean_apply_2(v_f_160_, v___x_164_, lean_box(0));
v___x_166_ = lean_unbox(v___x_165_);
if (v___x_166_ == 0)
{
uint8_t v___x_167_; 
lean_dec(v_i_161_);
lean_dec_ref(v_f_160_);
v___x_167_ = lean_unbox(v___x_165_);
return v___x_167_;
}
else
{
lean_object* v_one_168_; lean_object* v_n_169_; 
v_one_168_ = lean_unsigned_to_nat(1u);
v_n_169_ = lean_nat_sub(v_i_161_, v_one_168_);
lean_dec(v_i_161_);
v_i_161_ = v_n_169_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg___boxed(lean_object* v_n_171_, lean_object* v_f_172_, lean_object* v_i_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_171_, v_f_172_, v_i_173_);
lean_dec(v_n_171_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(lean_object* v_n_176_, lean_object* v_f_177_, lean_object* v_i_178_, lean_object* v_a_179_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_176_, v_f_177_, v_i_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___boxed(lean_object* v_n_181_, lean_object* v_f_182_, lean_object* v_i_183_, lean_object* v_a_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(v_n_181_, v_f_182_, v_i_183_, v_a_184_);
lean_dec(v_n_181_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t l_Nat_allTR(lean_object* v_n_187_, lean_object* v_f_188_){
_start:
{
uint8_t v___x_189_; 
lean_inc(v_n_187_);
v___x_189_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_187_, v_f_188_, v_n_187_);
lean_dec(v_n_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Nat_allTR___boxed(lean_object* v_n_190_, lean_object* v_f_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_Nat_allTR(v_n_190_, v_f_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10));
v___x_221_ = l_Lean_mkAtom(v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12);
v___x_223_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_224_ = lean_array_push(v___x_223_, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16));
v___x_236_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_237_ = lean_array_push(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_238_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17);
v___x_239_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15));
v___x_240_ = lean_box(2);
v___x_241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_238_);
return v___x_241_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18);
v___x_243_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13);
v___x_244_ = lean_array_push(v___x_243_, v___x_242_);
return v___x_244_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_245_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19);
v___x_246_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11));
v___x_247_ = lean_box(2);
v___x_248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_246_);
lean_ctor_set(v___x_248_, 2, v___x_245_);
return v___x_248_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20);
v___x_250_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_251_ = lean_array_push(v___x_250_, v___x_249_);
return v___x_251_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_252_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21);
v___x_253_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9));
v___x_254_ = lean_box(2);
v___x_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
lean_ctor_set(v___x_255_, 2, v___x_252_);
return v___x_255_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22);
v___x_257_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_258_ = lean_array_push(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_259_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23);
v___x_260_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7));
v___x_261_ = lean_box(2);
v___x_262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
lean_ctor_set(v___x_262_, 2, v___x_259_);
return v___x_262_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24);
v___x_264_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_265_ = lean_array_push(v___x_264_, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_266_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25);
v___x_267_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4));
v___x_268_ = lean_box(2);
v___x_269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
lean_ctor_set(v___x_269_, 2, v___x_266_);
return v___x_269_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1(void){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(lean_object* v_x_271_){
_start:
{
lean_inc(v_x_271_);
return v_x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg___boxed(lean_object* v_x_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(v_x_272_);
lean_dec(v_x_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(lean_object* v_n_274_, lean_object* v_00_u03b1_275_, lean_object* v_i_276_, lean_object* v_j_277_, lean_object* v_hi_278_, lean_object* v_w_279_, lean_object* v_x_280_){
_start:
{
lean_inc(v_x_280_);
return v_x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___boxed(lean_object* v_n_281_, lean_object* v_00_u03b1_282_, lean_object* v_i_283_, lean_object* v_j_284_, lean_object* v_hi_285_, lean_object* v_w_286_, lean_object* v_x_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(v_n_281_, v_00_u03b1_282_, v_i_283_, v_j_284_, v_hi_285_, v_w_286_, v_x_287_);
lean_dec(v_x_287_);
lean_dec(v_j_284_);
lean_dec(v_i_283_);
lean_dec(v_n_281_);
return v_res_288_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9(void){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_289_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_290_;
}
}
static lean_object* _init_l_Nat_dfold___auto__1(void){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(lean_object* v_n_292_, lean_object* v_f_293_, lean_object* v_j_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_zero_296_; uint8_t v_isZero_297_; 
v_zero_296_ = lean_unsigned_to_nat(0u);
v_isZero_297_ = lean_nat_dec_eq(v_j_294_, v_zero_296_);
if (v_isZero_297_ == 1)
{
lean_dec(v_j_294_);
lean_dec(v_f_293_);
return v_a_295_;
}
else
{
lean_object* v_one_298_; lean_object* v_n_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_one_298_ = lean_unsigned_to_nat(1u);
v_n_299_ = lean_nat_sub(v_j_294_, v_one_298_);
v___x_300_ = lean_nat_sub(v_n_292_, v_j_294_);
lean_dec(v_j_294_);
lean_inc(v_f_293_);
v___x_301_ = lean_apply_3(v_f_293_, v___x_300_, lean_box(0), v_a_295_);
v_j_294_ = v_n_299_;
v_a_295_ = v___x_301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg___boxed(lean_object* v_n_303_, lean_object* v_f_304_, lean_object* v_j_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_303_, v_f_304_, v_j_305_, v_a_306_);
lean_dec(v_n_303_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(lean_object* v_n_308_, lean_object* v_00_u03b1_309_, lean_object* v_f_310_, lean_object* v_j_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_308_, v_f_310_, v_j_311_, v_a_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___boxed(lean_object* v_n_315_, lean_object* v_00_u03b1_316_, lean_object* v_f_317_, lean_object* v_j_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(v_n_315_, v_00_u03b1_316_, v_f_317_, v_j_318_, v_a_319_, v_a_320_);
lean_dec(v_n_315_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfold___redArg(lean_object* v_n_322_, lean_object* v_f_323_, lean_object* v_init_324_){
_start:
{
lean_object* v___x_325_; 
lean_inc(v_n_322_);
v___x_325_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_322_, v_f_323_, v_n_322_, v_init_324_);
lean_dec(v_n_322_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfold(lean_object* v_n_326_, lean_object* v_00_u03b1_327_, lean_object* v_f_328_, lean_object* v_init_329_){
_start:
{
lean_object* v___x_330_; 
lean_inc(v_n_326_);
v___x_330_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_326_, v_f_328_, v_n_326_, v_init_329_);
lean_dec(v_n_326_);
return v___x_330_;
}
}
static lean_object* _init_l_Nat_dfoldRev___auto__1(void){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg___lam__0(lean_object* v_f_332_, lean_object* v_i_333_, lean_object* v_h_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lean_apply_3(v_f_332_, v_i_333_, lean_box(0), v___y_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg(lean_object* v_n_337_, lean_object* v_f_338_, lean_object* v_init_339_){
_start:
{
lean_object* v_zero_340_; uint8_t v_isZero_341_; 
v_zero_340_ = lean_unsigned_to_nat(0u);
v_isZero_341_ = lean_nat_dec_eq(v_n_337_, v_zero_340_);
if (v_isZero_341_ == 1)
{
lean_dec(v_f_338_);
lean_dec(v_n_337_);
return v_init_339_;
}
else
{
lean_object* v___f_342_; lean_object* v_one_343_; lean_object* v_n_344_; lean_object* v___x_345_; 
lean_inc(v_f_338_);
v___f_342_ = lean_alloc_closure((void*)(l_Nat_dfoldRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_342_, 0, v_f_338_);
v_one_343_ = lean_unsigned_to_nat(1u);
v_n_344_ = lean_nat_sub(v_n_337_, v_one_343_);
lean_dec(v_n_337_);
lean_inc(v_n_344_);
v___x_345_ = lean_apply_3(v_f_338_, v_n_344_, lean_box(0), v_init_339_);
v_n_337_ = v_n_344_;
v_f_338_ = v___f_342_;
v_init_339_ = v___x_345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev(lean_object* v_n_347_, lean_object* v_00_u03b1_348_, lean_object* v_f_349_, lean_object* v_init_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Nat_dfoldRev___redArg(v_n_347_, v_f_349_, v_init_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Nat_dfold__zero___auto__1(void){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_352_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5(void){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_353_;
}
}
static lean_object* _init_l_Nat_dfold__succ___auto__3(void){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_354_;
}
}
static lean_object* _init_l_Nat_dfold__congr___auto__1(void){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_355_;
}
}
static lean_object* _init_l_Nat_dfold__add___auto__5(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_356_;
}
}
static lean_object* _init_l_Nat_dfoldRev__zero___auto__1(void){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_357_;
}
}
static lean_object* _init_l_Nat_dfoldRev__succ___auto__3(void){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_358_;
}
}
static lean_object* _init_l_Nat_dfoldRev__congr___auto__1(void){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_359_;
}
}
static lean_object* _init_l_Nat_dfoldRev__add___auto__5(void){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0(lean_object* v_fst_361_, lean_object* v_f_362_, lean_object* v_j_363_, lean_object* v_x_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_nat_add(v_fst_361_, v_j_363_);
v___x_367_ = lean_apply_4(v_f_362_, v___x_366_, lean_box(0), lean_box(0), v___y_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0___boxed(lean_object* v_fst_368_, lean_object* v_f_369_, lean_object* v_j_370_, lean_object* v_x_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Prod_foldI___redArg___lam__0(v_fst_368_, v_f_369_, v_j_370_, v_x_371_, v___y_372_);
lean_dec(v_j_370_);
lean_dec(v_fst_368_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg(lean_object* v_i_374_, lean_object* v_f_375_, lean_object* v_init_376_){
_start:
{
lean_object* v_fst_377_; lean_object* v_snd_378_; lean_object* v___f_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_fst_377_ = lean_ctor_get(v_i_374_, 0);
lean_inc_n(v_fst_377_, 2);
v_snd_378_ = lean_ctor_get(v_i_374_, 1);
lean_inc(v_snd_378_);
lean_dec_ref(v_i_374_);
v___f_379_ = lean_alloc_closure((void*)(l_Prod_foldI___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_379_, 0, v_fst_377_);
lean_closure_set(v___f_379_, 1, v_f_375_);
v___x_380_ = lean_nat_sub(v_snd_378_, v_fst_377_);
lean_dec(v_fst_377_);
lean_dec(v_snd_378_);
lean_inc(v___x_380_);
v___x_381_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v___x_380_, v___f_379_, v___x_380_, v_init_376_);
lean_dec(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI(lean_object* v_00_u03b1_382_, lean_object* v_i_383_, lean_object* v_f_384_, lean_object* v_init_385_){
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
LEAN_EXPORT uint8_t l_Prod_anyI___lam__0(lean_object* v_fst_391_, lean_object* v_f_392_, lean_object* v_j_393_, lean_object* v_x_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_395_ = lean_nat_add(v_fst_391_, v_j_393_);
v___x_396_ = lean_apply_3(v_f_392_, v___x_395_, lean_box(0), lean_box(0));
v___x_397_ = lean_unbox(v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Prod_anyI___lam__0___boxed(lean_object* v_fst_398_, lean_object* v_f_399_, lean_object* v_j_400_, lean_object* v_x_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Prod_anyI___lam__0(v_fst_398_, v_f_399_, v_j_400_, v_x_401_);
lean_dec(v_j_400_);
lean_dec(v_fst_398_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_Prod_anyI(lean_object* v_i_404_, lean_object* v_f_405_){
_start:
{
lean_object* v_fst_406_; lean_object* v_snd_407_; lean_object* v___f_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_fst_406_ = lean_ctor_get(v_i_404_, 0);
lean_inc_n(v_fst_406_, 2);
v_snd_407_ = lean_ctor_get(v_i_404_, 1);
lean_inc(v_snd_407_);
lean_dec_ref(v_i_404_);
v___f_408_ = lean_alloc_closure((void*)(l_Prod_anyI___lam__0___boxed), 4, 2);
lean_closure_set(v___f_408_, 0, v_fst_406_);
lean_closure_set(v___f_408_, 1, v_f_405_);
v___x_409_ = lean_nat_sub(v_snd_407_, v_fst_406_);
lean_dec(v_fst_406_);
lean_dec(v_snd_407_);
lean_inc(v___x_409_);
v___x_410_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v___x_409_, v___f_408_, v___x_409_);
lean_dec(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Prod_anyI___boxed(lean_object* v_i_411_, lean_object* v_f_412_){
_start:
{
uint8_t v_res_413_; lean_object* v_r_414_; 
v_res_413_ = l_Prod_anyI(v_i_411_, v_f_412_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT uint8_t l_Prod_allI(lean_object* v_i_415_, lean_object* v_f_416_){
_start:
{
lean_object* v_fst_417_; lean_object* v_snd_418_; lean_object* v___f_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_fst_417_ = lean_ctor_get(v_i_415_, 0);
lean_inc_n(v_fst_417_, 2);
v_snd_418_ = lean_ctor_get(v_i_415_, 1);
lean_inc(v_snd_418_);
lean_dec_ref(v_i_415_);
v___f_419_ = lean_alloc_closure((void*)(l_Prod_anyI___lam__0___boxed), 4, 2);
lean_closure_set(v___f_419_, 0, v_fst_417_);
lean_closure_set(v___f_419_, 1, v_f_416_);
v___x_420_ = lean_nat_sub(v_snd_418_, v_fst_417_);
lean_dec(v_fst_417_);
lean_dec(v_snd_418_);
lean_inc(v___x_420_);
v___x_421_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v___x_420_, v___f_419_, v___x_420_);
lean_dec(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Prod_allI___boxed(lean_object* v_i_422_, lean_object* v_f_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Prod_allI(v_i_422_, v_f_423_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
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
