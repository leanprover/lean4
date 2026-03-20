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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5;
LEAN_EXPORT lean_object* l_Nat_dfold__succ___auto__3;
LEAN_EXPORT lean_object* l_Nat_dfold__congr___auto__1;
LEAN_EXPORT lean_object* l_Nat_dfold__add___auto__5;
LEAN_EXPORT lean_object* l_Nat_dfoldRev__zero___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg(lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_h__1_196_, lean_object* v_h__2_197_){
_start:
{
lean_object* v_zero_198_; uint8_t v_isZero_199_; 
v_zero_198_ = lean_unsigned_to_nat(0u);
v_isZero_199_ = lean_nat_dec_eq(v_x_194_, v_zero_198_);
if (v_isZero_199_ == 1)
{
lean_object* v___x_200_; 
lean_dec(v_h__2_197_);
v___x_200_ = lean_apply_2(v_h__1_196_, lean_box(0), v_x_195_);
return v___x_200_;
}
else
{
lean_object* v_one_201_; lean_object* v_n_202_; lean_object* v___x_203_; 
lean_dec(v_h__1_196_);
v_one_201_ = lean_unsigned_to_nat(1u);
v_n_202_ = lean_nat_sub(v_x_194_, v_one_201_);
v___x_203_ = lean_apply_3(v_h__2_197_, v_n_202_, lean_box(0), v_x_195_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_h__1_206_, lean_object* v_h__2_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg(v_x_204_, v_x_205_, v_h__1_206_, v_h__2_207_);
lean_dec(v_x_204_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter(lean_object* v_00_u03b1_209_, lean_object* v_n_210_, lean_object* v_motive_211_, lean_object* v_x_212_, lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_h__1_215_, lean_object* v_h__2_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg(v_x_212_, v_x_214_, v_h__1_215_, v_h__2_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_218_, lean_object* v_n_219_, lean_object* v_motive_220_, lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_h__1_224_, lean_object* v_h__2_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter(v_00_u03b1_218_, v_n_219_, v_motive_220_, v_x_221_, v_x_222_, v_x_223_, v_h__1_224_, v_h__2_225_);
lean_dec(v_x_221_);
lean_dec(v_n_219_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_h__1_230_, lean_object* v_h__2_231_){
_start:
{
lean_object* v_zero_232_; uint8_t v_isZero_233_; 
v_zero_232_ = lean_unsigned_to_nat(0u);
v_isZero_233_ = lean_nat_dec_eq(v_x_227_, v_zero_232_);
if (v_isZero_233_ == 1)
{
lean_object* v___x_234_; 
lean_dec(v_h__2_231_);
v___x_234_ = lean_apply_2(v_h__1_230_, v_x_228_, v_x_229_);
return v___x_234_;
}
else
{
lean_object* v_one_235_; lean_object* v_n_236_; lean_object* v___x_237_; 
lean_dec(v_h__1_230_);
v_one_235_ = lean_unsigned_to_nat(1u);
v_n_236_ = lean_nat_sub(v_x_227_, v_one_235_);
v___x_237_ = lean_apply_3(v_h__2_231_, v_n_236_, v_x_228_, v_x_229_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg___boxed(lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_h__1_241_, lean_object* v_h__2_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(v_x_238_, v_x_239_, v_x_240_, v_h__1_241_, v_h__2_242_);
lean_dec(v_x_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter(lean_object* v_00_u03b1_244_, lean_object* v_motive_245_, lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_h__1_249_, lean_object* v_h__2_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(v_x_246_, v_x_247_, v_x_248_, v_h__1_249_, v_h__2_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___boxed(lean_object* v_00_u03b1_252_, lean_object* v_motive_253_, lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_h__1_257_, lean_object* v_h__2_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter(v_00_u03b1_252_, v_motive_253_, v_x_254_, v_x_255_, v_x_256_, v_h__1_257_, v_h__2_258_);
lean_dec(v_x_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(lean_object* v_x_260_, lean_object* v_h__1_261_, lean_object* v_h__2_262_){
_start:
{
lean_object* v_zero_263_; uint8_t v_isZero_264_; 
v_zero_263_ = lean_unsigned_to_nat(0u);
v_isZero_264_ = lean_nat_dec_eq(v_x_260_, v_zero_263_);
if (v_isZero_264_ == 1)
{
lean_object* v___x_265_; 
lean_dec(v_h__2_262_);
v___x_265_ = lean_apply_1(v_h__1_261_, lean_box(0));
return v___x_265_;
}
else
{
lean_object* v_one_266_; lean_object* v_n_267_; lean_object* v___x_268_; 
lean_dec(v_h__1_261_);
v_one_266_ = lean_unsigned_to_nat(1u);
v_n_267_ = lean_nat_sub(v_x_260_, v_one_266_);
v___x_268_ = lean_apply_2(v_h__2_262_, v_n_267_, lean_box(0));
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_269_, lean_object* v_h__1_270_, lean_object* v_h__2_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(v_x_269_, v_h__1_270_, v_h__2_271_);
lean_dec(v_x_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter(lean_object* v_n_273_, lean_object* v_motive_274_, lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_h__1_277_, lean_object* v_h__2_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(v_x_275_, v_h__1_277_, v_h__2_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___boxed(lean_object* v_n_280_, lean_object* v_motive_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_h__1_284_, lean_object* v_h__2_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter(v_n_280_, v_motive_281_, v_x_282_, v_x_283_, v_h__1_284_, v_h__2_285_);
lean_dec(v_x_282_);
lean_dec(v_n_280_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v_h__1_289_, lean_object* v_h__2_290_){
_start:
{
lean_object* v_zero_291_; uint8_t v_isZero_292_; 
v_zero_291_ = lean_unsigned_to_nat(0u);
v_isZero_292_ = lean_nat_dec_eq(v_x_287_, v_zero_291_);
if (v_isZero_292_ == 1)
{
lean_object* v___x_293_; 
lean_dec(v_h__2_290_);
v___x_293_ = lean_apply_1(v_h__1_289_, v_x_288_);
return v___x_293_;
}
else
{
lean_object* v_one_294_; lean_object* v_n_295_; lean_object* v___x_296_; 
lean_dec(v_h__1_289_);
v_one_294_ = lean_unsigned_to_nat(1u);
v_n_295_ = lean_nat_sub(v_x_287_, v_one_294_);
v___x_296_ = lean_apply_2(v_h__2_290_, v_n_295_, v_x_288_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg___boxed(lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_h__1_299_, lean_object* v_h__2_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(v_x_297_, v_x_298_, v_h__1_299_, v_h__2_300_);
lean_dec(v_x_297_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter(lean_object* v_motive_302_, lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(v_x_303_, v_x_304_, v_h__1_305_, v_h__2_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___boxed(lean_object* v_motive_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_h__1_311_, lean_object* v_h__2_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter(v_motive_308_, v_x_309_, v_x_310_, v_h__1_311_, v_h__2_312_);
lean_dec(v_x_309_);
return v_res_313_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10));
v___x_341_ = l_Lean_mkAtom(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12);
v___x_343_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_344_ = lean_array_push(v___x_343_, v___x_342_);
return v___x_344_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16));
v___x_356_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_357_ = lean_array_push(v___x_356_, v___x_355_);
return v___x_357_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17);
v___x_359_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15));
v___x_360_ = lean_box(2);
v___x_361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_359_);
lean_ctor_set(v___x_361_, 2, v___x_358_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18);
v___x_363_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13);
v___x_364_ = lean_array_push(v___x_363_, v___x_362_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_365_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19);
v___x_366_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11));
v___x_367_ = lean_box(2);
v___x_368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___x_366_);
lean_ctor_set(v___x_368_, 2, v___x_365_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20);
v___x_370_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_371_ = lean_array_push(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_372_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21);
v___x_373_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9));
v___x_374_ = lean_box(2);
v___x_375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
lean_ctor_set(v___x_375_, 2, v___x_372_);
return v___x_375_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22);
v___x_377_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_378_ = lean_array_push(v___x_377_, v___x_376_);
return v___x_378_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_379_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23);
v___x_380_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7));
v___x_381_ = lean_box(2);
v___x_382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_380_);
lean_ctor_set(v___x_382_, 2, v___x_379_);
return v___x_382_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24);
v___x_384_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_385_ = lean_array_push(v___x_384_, v___x_383_);
return v___x_385_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_386_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25);
v___x_387_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4));
v___x_388_ = lean_box(2);
v___x_389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
lean_ctor_set(v___x_389_, 2, v___x_386_);
return v___x_389_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1(void){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(lean_object* v_x_391_){
_start:
{
lean_inc(v_x_391_);
return v_x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg___boxed(lean_object* v_x_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(v_x_392_);
lean_dec(v_x_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(lean_object* v_n_394_, lean_object* v_00_u03b1_395_, lean_object* v_i_396_, lean_object* v_j_397_, lean_object* v_hi_398_, lean_object* v_w_399_, lean_object* v_x_400_){
_start:
{
lean_inc(v_x_400_);
return v_x_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___boxed(lean_object* v_n_401_, lean_object* v_00_u03b1_402_, lean_object* v_i_403_, lean_object* v_j_404_, lean_object* v_hi_405_, lean_object* v_w_406_, lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(v_n_401_, v_00_u03b1_402_, v_i_403_, v_j_404_, v_hi_405_, v_w_406_, v_x_407_);
lean_dec(v_x_407_);
lean_dec(v_j_404_);
lean_dec(v_i_403_);
lean_dec(v_n_401_);
return v_res_408_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9(void){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_409_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3(void){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_410_;
}
}
static lean_object* _init_l_Nat_dfold___auto__1(void){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(lean_object* v_n_412_, lean_object* v_f_413_, lean_object* v_j_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_zero_416_; uint8_t v_isZero_417_; 
v_zero_416_ = lean_unsigned_to_nat(0u);
v_isZero_417_ = lean_nat_dec_eq(v_j_414_, v_zero_416_);
if (v_isZero_417_ == 1)
{
lean_dec(v_j_414_);
lean_dec(v_f_413_);
return v_a_415_;
}
else
{
lean_object* v_one_418_; lean_object* v_n_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_one_418_ = lean_unsigned_to_nat(1u);
v_n_419_ = lean_nat_sub(v_j_414_, v_one_418_);
v___x_420_ = lean_nat_sub(v_n_412_, v_j_414_);
lean_dec(v_j_414_);
lean_inc(v_f_413_);
v___x_421_ = lean_apply_3(v_f_413_, v___x_420_, lean_box(0), v_a_415_);
v_j_414_ = v_n_419_;
v_a_415_ = v___x_421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg___boxed(lean_object* v_n_423_, lean_object* v_f_424_, lean_object* v_j_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_423_, v_f_424_, v_j_425_, v_a_426_);
lean_dec(v_n_423_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(lean_object* v_n_428_, lean_object* v_00_u03b1_429_, lean_object* v_f_430_, lean_object* v_j_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_428_, v_f_430_, v_j_431_, v_a_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___boxed(lean_object* v_n_435_, lean_object* v_00_u03b1_436_, lean_object* v_f_437_, lean_object* v_j_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(v_n_435_, v_00_u03b1_436_, v_f_437_, v_j_438_, v_a_439_, v_a_440_);
lean_dec(v_n_435_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfold___redArg(lean_object* v_n_442_, lean_object* v_f_443_, lean_object* v_init_444_){
_start:
{
lean_object* v___x_445_; 
lean_inc(v_n_442_);
v___x_445_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_442_, v_f_443_, v_n_442_, v_init_444_);
lean_dec(v_n_442_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfold(lean_object* v_n_446_, lean_object* v_00_u03b1_447_, lean_object* v_f_448_, lean_object* v_init_449_){
_start:
{
lean_object* v___x_450_; 
lean_inc(v_n_446_);
v___x_450_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_446_, v_f_448_, v_n_446_, v_init_449_);
lean_dec(v_n_446_);
return v___x_450_;
}
}
static lean_object* _init_l_Nat_dfoldRev___auto__1(void){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg___lam__0(lean_object* v_f_452_, lean_object* v_i_453_, lean_object* v_h_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = lean_apply_3(v_f_452_, v_i_453_, lean_box(0), v___y_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg(lean_object* v_n_457_, lean_object* v_f_458_, lean_object* v_init_459_){
_start:
{
lean_object* v_zero_460_; uint8_t v_isZero_461_; 
v_zero_460_ = lean_unsigned_to_nat(0u);
v_isZero_461_ = lean_nat_dec_eq(v_n_457_, v_zero_460_);
if (v_isZero_461_ == 1)
{
lean_dec(v_f_458_);
lean_dec(v_n_457_);
return v_init_459_;
}
else
{
lean_object* v___f_462_; lean_object* v_one_463_; lean_object* v_n_464_; lean_object* v___x_465_; 
lean_inc(v_f_458_);
v___f_462_ = lean_alloc_closure((void*)(l_Nat_dfoldRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_462_, 0, v_f_458_);
v_one_463_ = lean_unsigned_to_nat(1u);
v_n_464_ = lean_nat_sub(v_n_457_, v_one_463_);
lean_dec(v_n_457_);
lean_inc(v_n_464_);
v___x_465_ = lean_apply_3(v_f_458_, v_n_464_, lean_box(0), v_init_459_);
v_n_457_ = v_n_464_;
v_f_458_ = v___f_462_;
v_init_459_ = v___x_465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev(lean_object* v_n_467_, lean_object* v_00_u03b1_468_, lean_object* v_f_469_, lean_object* v_init_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Nat_dfoldRev___redArg(v_n_467_, v_f_469_, v_init_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Nat_dfold__zero___auto__1(void){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg(lean_object* v_x_473_, lean_object* v_x_474_, lean_object* v_h__1_475_, lean_object* v_h__2_476_){
_start:
{
lean_object* v_zero_477_; uint8_t v_isZero_478_; 
v_zero_477_ = lean_unsigned_to_nat(0u);
v_isZero_478_ = lean_nat_dec_eq(v_x_473_, v_zero_477_);
if (v_isZero_478_ == 1)
{
lean_object* v___x_479_; 
lean_dec(v_h__2_476_);
v___x_479_ = lean_apply_2(v_h__1_475_, lean_box(0), v_x_474_);
return v___x_479_;
}
else
{
lean_object* v_one_480_; lean_object* v_n_481_; lean_object* v___x_482_; 
lean_dec(v_h__1_475_);
v_one_480_ = lean_unsigned_to_nat(1u);
v_n_481_ = lean_nat_sub(v_x_473_, v_one_480_);
v___x_482_ = lean_apply_3(v_h__2_476_, v_n_481_, lean_box(0), v_x_474_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg___boxed(lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg(v_x_483_, v_x_484_, v_h__1_485_, v_h__2_486_);
lean_dec(v_x_483_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter(lean_object* v_n_488_, lean_object* v_00_u03b1_489_, lean_object* v_motive_490_, lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_h__1_494_, lean_object* v_h__2_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg(v_x_491_, v_x_493_, v_h__1_494_, v_h__2_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___boxed(lean_object* v_n_497_, lean_object* v_00_u03b1_498_, lean_object* v_motive_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_h__1_503_, lean_object* v_h__2_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter(v_n_497_, v_00_u03b1_498_, v_motive_499_, v_x_500_, v_x_501_, v_x_502_, v_h__1_503_, v_h__2_504_);
lean_dec(v_x_500_);
lean_dec(v_n_497_);
return v_res_505_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5(void){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_506_;
}
}
static lean_object* _init_l_Nat_dfold__succ___auto__3(void){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_507_;
}
}
static lean_object* _init_l_Nat_dfold__congr___auto__1(void){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_508_;
}
}
static lean_object* _init_l_Nat_dfold__add___auto__5(void){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_509_;
}
}
static lean_object* _init_l_Nat_dfoldRev__zero___auto__1(void){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg(lean_object* v_n_511_, lean_object* v_f_512_, lean_object* v_init_513_, lean_object* v_h__1_514_, lean_object* v_h__2_515_){
_start:
{
lean_object* v_zero_516_; uint8_t v_isZero_517_; 
v_zero_516_ = lean_unsigned_to_nat(0u);
v_isZero_517_ = lean_nat_dec_eq(v_n_511_, v_zero_516_);
if (v_isZero_517_ == 1)
{
lean_object* v___x_518_; 
lean_dec(v_h__2_515_);
v___x_518_ = lean_apply_3(v_h__1_514_, lean_box(0), v_f_512_, v_init_513_);
return v___x_518_;
}
else
{
lean_object* v_one_519_; lean_object* v_n_520_; lean_object* v___x_521_; 
lean_dec(v_h__1_514_);
v_one_519_ = lean_unsigned_to_nat(1u);
v_n_520_ = lean_nat_sub(v_n_511_, v_one_519_);
v___x_521_ = lean_apply_4(v_h__2_515_, v_n_520_, lean_box(0), v_f_512_, v_init_513_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg___boxed(lean_object* v_n_522_, lean_object* v_f_523_, lean_object* v_init_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg(v_n_522_, v_f_523_, v_init_524_, v_h__1_525_, v_h__2_526_);
lean_dec(v_n_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter(lean_object* v_motive_528_, lean_object* v_n_529_, lean_object* v_00_u03b1_530_, lean_object* v_f_531_, lean_object* v_init_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg(v_n_529_, v_f_531_, v_init_532_, v_h__1_533_, v_h__2_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___boxed(lean_object* v_motive_536_, lean_object* v_n_537_, lean_object* v_00_u03b1_538_, lean_object* v_f_539_, lean_object* v_init_540_, lean_object* v_h__1_541_, lean_object* v_h__2_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter(v_motive_536_, v_n_537_, v_00_u03b1_538_, v_f_539_, v_init_540_, v_h__1_541_, v_h__2_542_);
lean_dec(v_n_537_);
return v_res_543_;
}
}
static lean_object* _init_l_Nat_dfoldRev__succ___auto__3(void){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_544_;
}
}
static lean_object* _init_l_Nat_dfoldRev__congr___auto__1(void){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_545_;
}
}
static lean_object* _init_l_Nat_dfoldRev__add___auto__5(void){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0(lean_object* v_fst_547_, lean_object* v_f_548_, lean_object* v_j_549_, lean_object* v_x_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_nat_add(v_fst_547_, v_j_549_);
v___x_553_ = lean_apply_4(v_f_548_, v___x_552_, lean_box(0), lean_box(0), v___y_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0___boxed(lean_object* v_fst_554_, lean_object* v_f_555_, lean_object* v_j_556_, lean_object* v_x_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Prod_foldI___redArg___lam__0(v_fst_554_, v_f_555_, v_j_556_, v_x_557_, v___y_558_);
lean_dec(v_j_556_);
lean_dec(v_fst_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg(lean_object* v_i_560_, lean_object* v_f_561_, lean_object* v_init_562_){
_start:
{
lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___f_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_fst_563_ = lean_ctor_get(v_i_560_, 0);
lean_inc(v_fst_563_);
v_snd_564_ = lean_ctor_get(v_i_560_, 1);
lean_inc(v_snd_564_);
lean_dec_ref(v_i_560_);
lean_inc(v_fst_563_);
v___f_565_ = lean_alloc_closure((void*)(l_Prod_foldI___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_565_, 0, v_fst_563_);
lean_closure_set(v___f_565_, 1, v_f_561_);
v___x_566_ = lean_nat_sub(v_snd_564_, v_fst_563_);
lean_dec(v_fst_563_);
lean_dec(v_snd_564_);
lean_inc(v___x_566_);
v___x_567_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v___x_566_, v___f_565_, v___x_566_, v_init_562_);
lean_dec(v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI(lean_object* v_00_u03b1_568_, lean_object* v_i_569_, lean_object* v_f_570_, lean_object* v_init_571_){
_start:
{
lean_object* v_fst_572_; lean_object* v_snd_573_; lean_object* v___f_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_fst_572_ = lean_ctor_get(v_i_569_, 0);
lean_inc(v_fst_572_);
v_snd_573_ = lean_ctor_get(v_i_569_, 1);
lean_inc(v_snd_573_);
lean_dec_ref(v_i_569_);
lean_inc(v_fst_572_);
v___f_574_ = lean_alloc_closure((void*)(l_Prod_foldI___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_574_, 0, v_fst_572_);
lean_closure_set(v___f_574_, 1, v_f_570_);
v___x_575_ = lean_nat_sub(v_snd_573_, v_fst_572_);
lean_dec(v_fst_572_);
lean_dec(v_snd_573_);
lean_inc(v___x_575_);
v___x_576_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v___x_575_, v___f_574_, v___x_575_, v_init_571_);
lean_dec(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT uint8_t l_Prod_anyI___lam__0(lean_object* v_fst_577_, lean_object* v_f_578_, lean_object* v_j_579_, lean_object* v_x_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_581_ = lean_nat_add(v_fst_577_, v_j_579_);
v___x_582_ = lean_apply_3(v_f_578_, v___x_581_, lean_box(0), lean_box(0));
v___x_583_ = lean_unbox(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Prod_anyI___lam__0___boxed(lean_object* v_fst_584_, lean_object* v_f_585_, lean_object* v_j_586_, lean_object* v_x_587_){
_start:
{
uint8_t v_res_588_; lean_object* v_r_589_; 
v_res_588_ = l_Prod_anyI___lam__0(v_fst_584_, v_f_585_, v_j_586_, v_x_587_);
lean_dec(v_j_586_);
lean_dec(v_fst_584_);
v_r_589_ = lean_box(v_res_588_);
return v_r_589_;
}
}
LEAN_EXPORT uint8_t l_Prod_anyI(lean_object* v_i_590_, lean_object* v_f_591_){
_start:
{
lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___f_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_fst_592_ = lean_ctor_get(v_i_590_, 0);
lean_inc(v_fst_592_);
v_snd_593_ = lean_ctor_get(v_i_590_, 1);
lean_inc(v_snd_593_);
lean_dec_ref(v_i_590_);
lean_inc(v_fst_592_);
v___f_594_ = lean_alloc_closure((void*)(l_Prod_anyI___lam__0___boxed), 4, 2);
lean_closure_set(v___f_594_, 0, v_fst_592_);
lean_closure_set(v___f_594_, 1, v_f_591_);
v___x_595_ = lean_nat_sub(v_snd_593_, v_fst_592_);
lean_dec(v_fst_592_);
lean_dec(v_snd_593_);
lean_inc(v___x_595_);
v___x_596_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v___x_595_, v___f_594_, v___x_595_);
lean_dec(v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Prod_anyI___boxed(lean_object* v_i_597_, lean_object* v_f_598_){
_start:
{
uint8_t v_res_599_; lean_object* v_r_600_; 
v_res_599_ = l_Prod_anyI(v_i_597_, v_f_598_);
v_r_600_ = lean_box(v_res_599_);
return v_r_600_;
}
}
LEAN_EXPORT uint8_t l_Prod_allI(lean_object* v_i_601_, lean_object* v_f_602_){
_start:
{
lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___f_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_fst_603_ = lean_ctor_get(v_i_601_, 0);
lean_inc(v_fst_603_);
v_snd_604_ = lean_ctor_get(v_i_601_, 1);
lean_inc(v_snd_604_);
lean_dec_ref(v_i_601_);
lean_inc(v_fst_603_);
v___f_605_ = lean_alloc_closure((void*)(l_Prod_anyI___lam__0___boxed), 4, 2);
lean_closure_set(v___f_605_, 0, v_fst_603_);
lean_closure_set(v___f_605_, 1, v_f_602_);
v___x_606_ = lean_nat_sub(v_snd_604_, v_fst_603_);
lean_dec(v_fst_603_);
lean_dec(v_snd_604_);
lean_inc(v___x_606_);
v___x_607_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v___x_606_, v___f_605_, v___x_606_);
lean_dec(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Prod_allI___boxed(lean_object* v_i_608_, lean_object* v_f_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Prod_allI(v_i_608_, v_f_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
lean_object* runtime_initialize_Init_Data_List_FinRange(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
