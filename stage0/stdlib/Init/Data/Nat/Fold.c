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
lean_object* v_zero_217_; uint8_t v_isZero_218_; 
v_zero_217_ = lean_unsigned_to_nat(0u);
v_isZero_218_ = lean_nat_dec_eq(v_x_212_, v_zero_217_);
if (v_isZero_218_ == 1)
{
lean_object* v___x_219_; 
lean_dec(v_h__2_216_);
v___x_219_ = lean_apply_2(v_h__1_215_, lean_box(0), v_x_214_);
return v___x_219_;
}
else
{
lean_object* v_one_220_; lean_object* v_n_221_; lean_object* v___x_222_; 
lean_dec(v_h__1_215_);
v_one_220_ = lean_unsigned_to_nat(1u);
v_n_221_ = lean_nat_sub(v_x_212_, v_one_220_);
v___x_222_ = lean_apply_3(v_h__2_216_, v_n_221_, lean_box(0), v_x_214_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_223_, lean_object* v_n_224_, lean_object* v_motive_225_, lean_object* v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_h__1_229_, lean_object* v_h__2_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter(v_00_u03b1_223_, v_n_224_, v_motive_225_, v_x_226_, v_x_227_, v_x_228_, v_h__1_229_, v_h__2_230_);
lean_dec(v_x_226_);
lean_dec(v_n_224_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v_h__1_235_, lean_object* v_h__2_236_){
_start:
{
lean_object* v_zero_237_; uint8_t v_isZero_238_; 
v_zero_237_ = lean_unsigned_to_nat(0u);
v_isZero_238_ = lean_nat_dec_eq(v_x_232_, v_zero_237_);
if (v_isZero_238_ == 1)
{
lean_object* v___x_239_; 
lean_dec(v_h__2_236_);
v___x_239_ = lean_apply_2(v_h__1_235_, v_x_233_, v_x_234_);
return v___x_239_;
}
else
{
lean_object* v_one_240_; lean_object* v_n_241_; lean_object* v___x_242_; 
lean_dec(v_h__1_235_);
v_one_240_ = lean_unsigned_to_nat(1u);
v_n_241_ = lean_nat_sub(v_x_232_, v_one_240_);
v___x_242_ = lean_apply_3(v_h__2_236_, v_n_241_, v_x_233_, v_x_234_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg___boxed(lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_h__1_246_, lean_object* v_h__2_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(v_x_243_, v_x_244_, v_x_245_, v_h__1_246_, v_h__2_247_);
lean_dec(v_x_243_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter(lean_object* v_00_u03b1_249_, lean_object* v_motive_250_, lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_, lean_object* v_h__1_254_, lean_object* v_h__2_255_){
_start:
{
lean_object* v_zero_256_; uint8_t v_isZero_257_; 
v_zero_256_ = lean_unsigned_to_nat(0u);
v_isZero_257_ = lean_nat_dec_eq(v_x_251_, v_zero_256_);
if (v_isZero_257_ == 1)
{
lean_object* v___x_258_; 
lean_dec(v_h__2_255_);
v___x_258_ = lean_apply_2(v_h__1_254_, v_x_252_, v_x_253_);
return v___x_258_;
}
else
{
lean_object* v_one_259_; lean_object* v_n_260_; lean_object* v___x_261_; 
lean_dec(v_h__1_254_);
v_one_259_ = lean_unsigned_to_nat(1u);
v_n_260_ = lean_nat_sub(v_x_251_, v_one_259_);
v___x_261_ = lean_apply_3(v_h__2_255_, v_n_260_, v_x_252_, v_x_253_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___boxed(lean_object* v_00_u03b1_262_, lean_object* v_motive_263_, lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_h__1_267_, lean_object* v_h__2_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter(v_00_u03b1_262_, v_motive_263_, v_x_264_, v_x_265_, v_x_266_, v_h__1_267_, v_h__2_268_);
lean_dec(v_x_264_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(lean_object* v_x_270_, lean_object* v_h__1_271_, lean_object* v_h__2_272_){
_start:
{
lean_object* v_zero_273_; uint8_t v_isZero_274_; 
v_zero_273_ = lean_unsigned_to_nat(0u);
v_isZero_274_ = lean_nat_dec_eq(v_x_270_, v_zero_273_);
if (v_isZero_274_ == 1)
{
lean_object* v___x_275_; 
lean_dec(v_h__2_272_);
v___x_275_ = lean_apply_1(v_h__1_271_, lean_box(0));
return v___x_275_;
}
else
{
lean_object* v_one_276_; lean_object* v_n_277_; lean_object* v___x_278_; 
lean_dec(v_h__1_271_);
v_one_276_ = lean_unsigned_to_nat(1u);
v_n_277_ = lean_nat_sub(v_x_270_, v_one_276_);
v___x_278_ = lean_apply_2(v_h__2_272_, v_n_277_, lean_box(0));
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_279_, lean_object* v_h__1_280_, lean_object* v_h__2_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(v_x_279_, v_h__1_280_, v_h__2_281_);
lean_dec(v_x_279_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter(lean_object* v_n_283_, lean_object* v_motive_284_, lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_h__1_287_, lean_object* v_h__2_288_){
_start:
{
lean_object* v_zero_289_; uint8_t v_isZero_290_; 
v_zero_289_ = lean_unsigned_to_nat(0u);
v_isZero_290_ = lean_nat_dec_eq(v_x_285_, v_zero_289_);
if (v_isZero_290_ == 1)
{
lean_object* v___x_291_; 
lean_dec(v_h__2_288_);
v___x_291_ = lean_apply_1(v_h__1_287_, lean_box(0));
return v___x_291_;
}
else
{
lean_object* v_one_292_; lean_object* v_n_293_; lean_object* v___x_294_; 
lean_dec(v_h__1_287_);
v_one_292_ = lean_unsigned_to_nat(1u);
v_n_293_ = lean_nat_sub(v_x_285_, v_one_292_);
v___x_294_ = lean_apply_2(v_h__2_288_, v_n_293_, lean_box(0));
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___boxed(lean_object* v_n_295_, lean_object* v_motive_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_h__1_299_, lean_object* v_h__2_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter(v_n_295_, v_motive_296_, v_x_297_, v_x_298_, v_h__1_299_, v_h__2_300_);
lean_dec(v_x_297_);
lean_dec(v_n_295_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_h__1_304_, lean_object* v_h__2_305_){
_start:
{
lean_object* v_zero_306_; uint8_t v_isZero_307_; 
v_zero_306_ = lean_unsigned_to_nat(0u);
v_isZero_307_ = lean_nat_dec_eq(v_x_302_, v_zero_306_);
if (v_isZero_307_ == 1)
{
lean_object* v___x_308_; 
lean_dec(v_h__2_305_);
v___x_308_ = lean_apply_1(v_h__1_304_, v_x_303_);
return v___x_308_;
}
else
{
lean_object* v_one_309_; lean_object* v_n_310_; lean_object* v___x_311_; 
lean_dec(v_h__1_304_);
v_one_309_ = lean_unsigned_to_nat(1u);
v_n_310_ = lean_nat_sub(v_x_302_, v_one_309_);
v___x_311_ = lean_apply_2(v_h__2_305_, v_n_310_, v_x_303_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg___boxed(lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_h__1_314_, lean_object* v_h__2_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(v_x_312_, v_x_313_, v_h__1_314_, v_h__2_315_);
lean_dec(v_x_312_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter(lean_object* v_motive_317_, lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v_h__1_320_, lean_object* v_h__2_321_){
_start:
{
lean_object* v_zero_322_; uint8_t v_isZero_323_; 
v_zero_322_ = lean_unsigned_to_nat(0u);
v_isZero_323_ = lean_nat_dec_eq(v_x_318_, v_zero_322_);
if (v_isZero_323_ == 1)
{
lean_object* v___x_324_; 
lean_dec(v_h__2_321_);
v___x_324_ = lean_apply_1(v_h__1_320_, v_x_319_);
return v___x_324_;
}
else
{
lean_object* v_one_325_; lean_object* v_n_326_; lean_object* v___x_327_; 
lean_dec(v_h__1_320_);
v_one_325_ = lean_unsigned_to_nat(1u);
v_n_326_ = lean_nat_sub(v_x_318_, v_one_325_);
v___x_327_ = lean_apply_2(v_h__2_321_, v_n_326_, v_x_319_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___boxed(lean_object* v_motive_328_, lean_object* v_x_329_, lean_object* v_x_330_, lean_object* v_h__1_331_, lean_object* v_h__2_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter(v_motive_328_, v_x_329_, v_x_330_, v_h__1_331_, v_h__2_332_);
lean_dec(v_x_329_);
return v_res_333_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10));
v___x_361_ = l_Lean_mkAtom(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12);
v___x_363_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_364_ = lean_array_push(v___x_363_, v___x_362_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16));
v___x_376_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_377_ = lean_array_push(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_378_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17);
v___x_379_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15));
v___x_380_ = lean_box(2);
v___x_381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
lean_ctor_set(v___x_381_, 2, v___x_378_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18);
v___x_383_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13);
v___x_384_ = lean_array_push(v___x_383_, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19);
v___x_386_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11));
v___x_387_ = lean_box(2);
v___x_388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
lean_ctor_set(v___x_388_, 2, v___x_385_);
return v___x_388_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20);
v___x_390_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_391_ = lean_array_push(v___x_390_, v___x_389_);
return v___x_391_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21);
v___x_393_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9));
v___x_394_ = lean_box(2);
v___x_395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_393_);
lean_ctor_set(v___x_395_, 2, v___x_392_);
return v___x_395_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22);
v___x_397_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_398_ = lean_array_push(v___x_397_, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23);
v___x_400_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7));
v___x_401_ = lean_box(2);
v___x_402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
lean_ctor_set(v___x_402_, 2, v___x_399_);
return v___x_402_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24);
v___x_404_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_405_ = lean_array_push(v___x_404_, v___x_403_);
return v___x_405_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25);
v___x_407_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4));
v___x_408_ = lean_box(2);
v___x_409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_407_);
lean_ctor_set(v___x_409_, 2, v___x_406_);
return v___x_409_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1(void){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(lean_object* v_x_411_){
_start:
{
lean_inc(v_x_411_);
return v_x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg___boxed(lean_object* v_x_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(v_x_412_);
lean_dec(v_x_412_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(lean_object* v_n_414_, lean_object* v_00_u03b1_415_, lean_object* v_i_416_, lean_object* v_j_417_, lean_object* v_hi_418_, lean_object* v_w_419_, lean_object* v_x_420_){
_start:
{
lean_inc(v_x_420_);
return v_x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___boxed(lean_object* v_n_421_, lean_object* v_00_u03b1_422_, lean_object* v_i_423_, lean_object* v_j_424_, lean_object* v_hi_425_, lean_object* v_w_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(v_n_421_, v_00_u03b1_422_, v_i_423_, v_j_424_, v_hi_425_, v_w_426_, v_x_427_);
lean_dec(v_x_427_);
lean_dec(v_j_424_);
lean_dec(v_i_423_);
lean_dec(v_n_421_);
return v_res_428_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9(void){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_429_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3(void){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_430_;
}
}
static lean_object* _init_l_Nat_dfold___auto__1(void){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(lean_object* v_n_432_, lean_object* v_f_433_, lean_object* v_j_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_zero_436_; uint8_t v_isZero_437_; 
v_zero_436_ = lean_unsigned_to_nat(0u);
v_isZero_437_ = lean_nat_dec_eq(v_j_434_, v_zero_436_);
if (v_isZero_437_ == 1)
{
lean_dec(v_j_434_);
lean_dec(v_f_433_);
return v_a_435_;
}
else
{
lean_object* v_one_438_; lean_object* v_n_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_one_438_ = lean_unsigned_to_nat(1u);
v_n_439_ = lean_nat_sub(v_j_434_, v_one_438_);
v___x_440_ = lean_nat_sub(v_n_432_, v_j_434_);
lean_dec(v_j_434_);
lean_inc(v_f_433_);
v___x_441_ = lean_apply_3(v_f_433_, v___x_440_, lean_box(0), v_a_435_);
v_j_434_ = v_n_439_;
v_a_435_ = v___x_441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg___boxed(lean_object* v_n_443_, lean_object* v_f_444_, lean_object* v_j_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_443_, v_f_444_, v_j_445_, v_a_446_);
lean_dec(v_n_443_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(lean_object* v_n_448_, lean_object* v_00_u03b1_449_, lean_object* v_f_450_, lean_object* v_j_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_448_, v_f_450_, v_j_451_, v_a_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___boxed(lean_object* v_n_455_, lean_object* v_00_u03b1_456_, lean_object* v_f_457_, lean_object* v_j_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(v_n_455_, v_00_u03b1_456_, v_f_457_, v_j_458_, v_a_459_, v_a_460_);
lean_dec(v_n_455_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfold___redArg(lean_object* v_n_462_, lean_object* v_f_463_, lean_object* v_init_464_){
_start:
{
lean_object* v___x_465_; 
lean_inc(v_n_462_);
v___x_465_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_462_, v_f_463_, v_n_462_, v_init_464_);
lean_dec(v_n_462_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfold(lean_object* v_n_466_, lean_object* v_00_u03b1_467_, lean_object* v_f_468_, lean_object* v_init_469_){
_start:
{
lean_object* v___x_470_; 
lean_inc(v_n_466_);
v___x_470_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_466_, v_f_468_, v_n_466_, v_init_469_);
lean_dec(v_n_466_);
return v___x_470_;
}
}
static lean_object* _init_l_Nat_dfoldRev___auto__1(void){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg___lam__0(lean_object* v_f_472_, lean_object* v_i_473_, lean_object* v_h_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_apply_3(v_f_472_, v_i_473_, lean_box(0), v___y_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg(lean_object* v_n_477_, lean_object* v_f_478_, lean_object* v_init_479_){
_start:
{
lean_object* v_zero_480_; uint8_t v_isZero_481_; 
v_zero_480_ = lean_unsigned_to_nat(0u);
v_isZero_481_ = lean_nat_dec_eq(v_n_477_, v_zero_480_);
if (v_isZero_481_ == 1)
{
lean_dec(v_f_478_);
lean_dec(v_n_477_);
return v_init_479_;
}
else
{
lean_object* v___f_482_; lean_object* v_one_483_; lean_object* v_n_484_; lean_object* v___x_485_; 
lean_inc(v_f_478_);
v___f_482_ = lean_alloc_closure((void*)(l_Nat_dfoldRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_482_, 0, v_f_478_);
v_one_483_ = lean_unsigned_to_nat(1u);
v_n_484_ = lean_nat_sub(v_n_477_, v_one_483_);
lean_dec(v_n_477_);
lean_inc(v_n_484_);
v___x_485_ = lean_apply_3(v_f_478_, v_n_484_, lean_box(0), v_init_479_);
v_n_477_ = v_n_484_;
v_f_478_ = v___f_482_;
v_init_479_ = v___x_485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev(lean_object* v_n_487_, lean_object* v_00_u03b1_488_, lean_object* v_f_489_, lean_object* v_init_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Nat_dfoldRev___redArg(v_n_487_, v_f_489_, v_init_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Nat_dfold__zero___auto__1(void){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg(lean_object* v_x_493_, lean_object* v_x_494_, lean_object* v_h__1_495_, lean_object* v_h__2_496_){
_start:
{
lean_object* v_zero_497_; uint8_t v_isZero_498_; 
v_zero_497_ = lean_unsigned_to_nat(0u);
v_isZero_498_ = lean_nat_dec_eq(v_x_493_, v_zero_497_);
if (v_isZero_498_ == 1)
{
lean_object* v___x_499_; 
lean_dec(v_h__2_496_);
v___x_499_ = lean_apply_2(v_h__1_495_, lean_box(0), v_x_494_);
return v___x_499_;
}
else
{
lean_object* v_one_500_; lean_object* v_n_501_; lean_object* v___x_502_; 
lean_dec(v_h__1_495_);
v_one_500_ = lean_unsigned_to_nat(1u);
v_n_501_ = lean_nat_sub(v_x_493_, v_one_500_);
v___x_502_ = lean_apply_3(v_h__2_496_, v_n_501_, lean_box(0), v_x_494_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg___boxed(lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_h__1_505_, lean_object* v_h__2_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg(v_x_503_, v_x_504_, v_h__1_505_, v_h__2_506_);
lean_dec(v_x_503_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter(lean_object* v_n_508_, lean_object* v_00_u03b1_509_, lean_object* v_motive_510_, lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_, lean_object* v_h__1_514_, lean_object* v_h__2_515_){
_start:
{
lean_object* v_zero_516_; uint8_t v_isZero_517_; 
v_zero_516_ = lean_unsigned_to_nat(0u);
v_isZero_517_ = lean_nat_dec_eq(v_x_511_, v_zero_516_);
if (v_isZero_517_ == 1)
{
lean_object* v___x_518_; 
lean_dec(v_h__2_515_);
v___x_518_ = lean_apply_2(v_h__1_514_, lean_box(0), v_x_513_);
return v___x_518_;
}
else
{
lean_object* v_one_519_; lean_object* v_n_520_; lean_object* v___x_521_; 
lean_dec(v_h__1_514_);
v_one_519_ = lean_unsigned_to_nat(1u);
v_n_520_ = lean_nat_sub(v_x_511_, v_one_519_);
v___x_521_ = lean_apply_3(v_h__2_515_, v_n_520_, lean_box(0), v_x_513_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___boxed(lean_object* v_n_522_, lean_object* v_00_u03b1_523_, lean_object* v_motive_524_, lean_object* v_x_525_, lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_h__1_528_, lean_object* v_h__2_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter(v_n_522_, v_00_u03b1_523_, v_motive_524_, v_x_525_, v_x_526_, v_x_527_, v_h__1_528_, v_h__2_529_);
lean_dec(v_x_525_);
lean_dec(v_n_522_);
return v_res_530_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_531_;
}
}
static lean_object* _init_l_Nat_dfold__succ___auto__3(void){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_532_;
}
}
static lean_object* _init_l_Nat_dfold__congr___auto__1(void){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_533_;
}
}
static lean_object* _init_l_Nat_dfold__add___auto__5(void){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_534_;
}
}
static lean_object* _init_l_Nat_dfoldRev__zero___auto__1(void){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg(lean_object* v_n_536_, lean_object* v_f_537_, lean_object* v_init_538_, lean_object* v_h__1_539_, lean_object* v_h__2_540_){
_start:
{
lean_object* v_zero_541_; uint8_t v_isZero_542_; 
v_zero_541_ = lean_unsigned_to_nat(0u);
v_isZero_542_ = lean_nat_dec_eq(v_n_536_, v_zero_541_);
if (v_isZero_542_ == 1)
{
lean_object* v___x_543_; 
lean_dec(v_h__2_540_);
v___x_543_ = lean_apply_3(v_h__1_539_, lean_box(0), v_f_537_, v_init_538_);
return v___x_543_;
}
else
{
lean_object* v_one_544_; lean_object* v_n_545_; lean_object* v___x_546_; 
lean_dec(v_h__1_539_);
v_one_544_ = lean_unsigned_to_nat(1u);
v_n_545_ = lean_nat_sub(v_n_536_, v_one_544_);
v___x_546_ = lean_apply_4(v_h__2_540_, v_n_545_, lean_box(0), v_f_537_, v_init_538_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg___boxed(lean_object* v_n_547_, lean_object* v_f_548_, lean_object* v_init_549_, lean_object* v_h__1_550_, lean_object* v_h__2_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg(v_n_547_, v_f_548_, v_init_549_, v_h__1_550_, v_h__2_551_);
lean_dec(v_n_547_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter(lean_object* v_motive_553_, lean_object* v_n_554_, lean_object* v_00_u03b1_555_, lean_object* v_f_556_, lean_object* v_init_557_, lean_object* v_h__1_558_, lean_object* v_h__2_559_){
_start:
{
lean_object* v_zero_560_; uint8_t v_isZero_561_; 
v_zero_560_ = lean_unsigned_to_nat(0u);
v_isZero_561_ = lean_nat_dec_eq(v_n_554_, v_zero_560_);
if (v_isZero_561_ == 1)
{
lean_object* v___x_562_; 
lean_dec(v_h__2_559_);
v___x_562_ = lean_apply_3(v_h__1_558_, lean_box(0), v_f_556_, v_init_557_);
return v___x_562_;
}
else
{
lean_object* v_one_563_; lean_object* v_n_564_; lean_object* v___x_565_; 
lean_dec(v_h__1_558_);
v_one_563_ = lean_unsigned_to_nat(1u);
v_n_564_ = lean_nat_sub(v_n_554_, v_one_563_);
v___x_565_ = lean_apply_4(v_h__2_559_, v_n_564_, lean_box(0), v_f_556_, v_init_557_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___boxed(lean_object* v_motive_566_, lean_object* v_n_567_, lean_object* v_00_u03b1_568_, lean_object* v_f_569_, lean_object* v_init_570_, lean_object* v_h__1_571_, lean_object* v_h__2_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter(v_motive_566_, v_n_567_, v_00_u03b1_568_, v_f_569_, v_init_570_, v_h__1_571_, v_h__2_572_);
lean_dec(v_n_567_);
return v_res_573_;
}
}
static lean_object* _init_l_Nat_dfoldRev__succ___auto__3(void){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_574_;
}
}
static lean_object* _init_l_Nat_dfoldRev__congr___auto__1(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_575_;
}
}
static lean_object* _init_l_Nat_dfoldRev__add___auto__5(void){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0(lean_object* v_fst_577_, lean_object* v_f_578_, lean_object* v_j_579_, lean_object* v_x_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_nat_add(v_fst_577_, v_j_579_);
v___x_583_ = lean_apply_4(v_f_578_, v___x_582_, lean_box(0), lean_box(0), v___y_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0___boxed(lean_object* v_fst_584_, lean_object* v_f_585_, lean_object* v_j_586_, lean_object* v_x_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Prod_foldI___redArg___lam__0(v_fst_584_, v_f_585_, v_j_586_, v_x_587_, v___y_588_);
lean_dec(v_j_586_);
lean_dec(v_fst_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg(lean_object* v_i_590_, lean_object* v_f_591_, lean_object* v_init_592_){
_start:
{
lean_object* v_fst_593_; lean_object* v_snd_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_fst_593_ = lean_ctor_get(v_i_590_, 0);
lean_inc_n(v_fst_593_, 2);
v_snd_594_ = lean_ctor_get(v_i_590_, 1);
lean_inc(v_snd_594_);
lean_dec_ref(v_i_590_);
v___f_595_ = lean_alloc_closure((void*)(l_Prod_foldI___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_595_, 0, v_fst_593_);
lean_closure_set(v___f_595_, 1, v_f_591_);
v___x_596_ = lean_nat_sub(v_snd_594_, v_fst_593_);
lean_dec(v_fst_593_);
lean_dec(v_snd_594_);
lean_inc(v___x_596_);
v___x_597_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v___x_596_, v___f_595_, v___x_596_, v_init_592_);
lean_dec(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI(lean_object* v_00_u03b1_598_, lean_object* v_i_599_, lean_object* v_f_600_, lean_object* v_init_601_){
_start:
{
lean_object* v_fst_602_; lean_object* v_snd_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_fst_602_ = lean_ctor_get(v_i_599_, 0);
lean_inc_n(v_fst_602_, 2);
v_snd_603_ = lean_ctor_get(v_i_599_, 1);
lean_inc(v_snd_603_);
lean_dec_ref(v_i_599_);
v___f_604_ = lean_alloc_closure((void*)(l_Prod_foldI___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_604_, 0, v_fst_602_);
lean_closure_set(v___f_604_, 1, v_f_600_);
v___x_605_ = lean_nat_sub(v_snd_603_, v_fst_602_);
lean_dec(v_fst_602_);
lean_dec(v_snd_603_);
lean_inc(v___x_605_);
v___x_606_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v___x_605_, v___f_604_, v___x_605_, v_init_601_);
lean_dec(v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT uint8_t l_Prod_anyI___lam__0(lean_object* v_fst_607_, lean_object* v_f_608_, lean_object* v_j_609_, lean_object* v_x_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_nat_add(v_fst_607_, v_j_609_);
v___x_612_ = lean_apply_3(v_f_608_, v___x_611_, lean_box(0), lean_box(0));
v___x_613_ = lean_unbox(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Prod_anyI___lam__0___boxed(lean_object* v_fst_614_, lean_object* v_f_615_, lean_object* v_j_616_, lean_object* v_x_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l_Prod_anyI___lam__0(v_fst_614_, v_f_615_, v_j_616_, v_x_617_);
lean_dec(v_j_616_);
lean_dec(v_fst_614_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT uint8_t l_Prod_anyI(lean_object* v_i_620_, lean_object* v_f_621_){
_start:
{
lean_object* v_fst_622_; lean_object* v_snd_623_; lean_object* v___f_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_fst_622_ = lean_ctor_get(v_i_620_, 0);
lean_inc_n(v_fst_622_, 2);
v_snd_623_ = lean_ctor_get(v_i_620_, 1);
lean_inc(v_snd_623_);
lean_dec_ref(v_i_620_);
v___f_624_ = lean_alloc_closure((void*)(l_Prod_anyI___lam__0___boxed), 4, 2);
lean_closure_set(v___f_624_, 0, v_fst_622_);
lean_closure_set(v___f_624_, 1, v_f_621_);
v___x_625_ = lean_nat_sub(v_snd_623_, v_fst_622_);
lean_dec(v_fst_622_);
lean_dec(v_snd_623_);
lean_inc(v___x_625_);
v___x_626_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v___x_625_, v___f_624_, v___x_625_);
lean_dec(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Prod_anyI___boxed(lean_object* v_i_627_, lean_object* v_f_628_){
_start:
{
uint8_t v_res_629_; lean_object* v_r_630_; 
v_res_629_ = l_Prod_anyI(v_i_627_, v_f_628_);
v_r_630_ = lean_box(v_res_629_);
return v_r_630_;
}
}
LEAN_EXPORT uint8_t l_Prod_allI(lean_object* v_i_631_, lean_object* v_f_632_){
_start:
{
lean_object* v_fst_633_; lean_object* v_snd_634_; lean_object* v___f_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_fst_633_ = lean_ctor_get(v_i_631_, 0);
lean_inc_n(v_fst_633_, 2);
v_snd_634_ = lean_ctor_get(v_i_631_, 1);
lean_inc(v_snd_634_);
lean_dec_ref(v_i_631_);
v___f_635_ = lean_alloc_closure((void*)(l_Prod_anyI___lam__0___boxed), 4, 2);
lean_closure_set(v___f_635_, 0, v_fst_633_);
lean_closure_set(v___f_635_, 1, v_f_632_);
v___x_636_ = lean_nat_sub(v_snd_634_, v_fst_633_);
lean_dec(v_fst_633_);
lean_dec(v_snd_634_);
lean_inc(v___x_636_);
v___x_637_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v___x_636_, v___f_635_, v___x_636_);
lean_dec(v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Prod_allI___boxed(lean_object* v_i_638_, lean_object* v_f_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Prod_allI(v_i_638_, v_f_639_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
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
