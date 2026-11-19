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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(lean_object* v_n_1_, lean_object* v_f_2_, lean_object* v_j_3_, lean_object* v_a_4_){
_start:
{
lean_object* v_zero_5_; uint8_t v_isZero_6_; 
v_zero_5_ = lean_unsigned_to_nat(0u);
v_isZero_6_ = lean_nat_dec_eq(v_j_3_, v_zero_5_);
if (v_isZero_6_ == 1)
{
lean_dec(v_j_3_);
lean_dec(v_f_2_);
return v_a_4_;
}
else
{
lean_object* v_one_7_; lean_object* v_n_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_one_7_ = lean_unsigned_to_nat(1u);
v_n_8_ = lean_nat_sub(v_j_3_, v_one_7_);
v___x_9_ = lean_nat_sub(v_n_1_, v_j_3_);
lean_dec(v_j_3_);
lean_inc(v_f_2_);
v___x_10_ = lean_apply_3(v_f_2_, v___x_9_, lean_box(0), v_a_4_);
v_j_3_ = v_n_8_;
v_a_4_ = v___x_10_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg___boxed(lean_object* v_n_12_, lean_object* v_f_13_, lean_object* v_j_14_, lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v_n_12_, v_f_13_, v_j_14_, v_a_15_);
lean_dec(v_n_12_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_object* v_00_u03b1_17_, lean_object* v_n_18_, lean_object* v_f_19_, lean_object* v_j_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v_n_18_, v_f_19_, v_j_20_, v_a_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___boxed(lean_object* v_00_u03b1_24_, lean_object* v_n_25_, lean_object* v_f_26_, lean_object* v_j_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(v_00_u03b1_24_, v_n_25_, v_f_26_, v_j_27_, v_a_28_, v_a_29_);
lean_dec(v_n_25_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR___redArg(lean_object* v_n_31_, lean_object* v_f_32_, lean_object* v_init_33_){
_start:
{
lean_object* v___x_34_; 
lean_inc(v_n_31_);
v___x_34_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v_n_31_, v_f_32_, v_n_31_, v_init_33_);
lean_dec(v_n_31_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR(lean_object* v_00_u03b1_35_, lean_object* v_n_36_, lean_object* v_f_37_, lean_object* v_init_38_){
_start:
{
lean_object* v___x_39_; 
lean_inc(v_n_36_);
v___x_39_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v_n_36_, v_f_37_, v_n_36_, v_init_38_);
lean_dec(v_n_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___redArg___lam__0(lean_object* v_x_40_, lean_object* v_i_41_, lean_object* v_h_42_, lean_object* v___y_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_apply_3(v_x_40_, v_i_41_, lean_box(0), v___y_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___redArg(lean_object* v_x_45_, lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
lean_object* v_zero_48_; uint8_t v_isZero_49_; 
v_zero_48_ = lean_unsigned_to_nat(0u);
v_isZero_49_ = lean_nat_dec_eq(v_x_45_, v_zero_48_);
if (v_isZero_49_ == 1)
{
lean_dec(v_x_46_);
lean_dec(v_x_45_);
return v_x_47_;
}
else
{
lean_object* v___f_50_; lean_object* v_one_51_; lean_object* v_n_52_; lean_object* v___x_53_; 
lean_inc(v_x_46_);
v___f_50_ = lean_alloc_closure((void*)(l_Nat_foldRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_50_, 0, v_x_46_);
v_one_51_ = lean_unsigned_to_nat(1u);
v_n_52_ = lean_nat_sub(v_x_45_, v_one_51_);
lean_dec(v_x_45_);
lean_inc(v_n_52_);
v___x_53_ = lean_apply_3(v_x_46_, v_n_52_, lean_box(0), v_x_47_);
v_x_45_ = v_n_52_;
v_x_46_ = v___f_50_;
v_x_47_ = v___x_53_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev(lean_object* v_00_u03b1_55_, lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Nat_foldRev___redArg(v_x_56_, v_x_57_, v_x_58_);
return v___x_59_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(lean_object* v_n_60_, lean_object* v_f_61_, lean_object* v_i_62_){
_start:
{
lean_object* v_zero_63_; uint8_t v_isZero_64_; 
v_zero_63_ = lean_unsigned_to_nat(0u);
v_isZero_64_ = lean_nat_dec_eq(v_i_62_, v_zero_63_);
if (v_isZero_64_ == 1)
{
uint8_t v___x_65_; 
lean_dec(v_i_62_);
lean_dec_ref(v_f_61_);
v___x_65_ = 0;
return v___x_65_;
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = lean_nat_sub(v_n_60_, v_i_62_);
lean_inc_ref(v_f_61_);
v___x_67_ = lean_apply_2(v_f_61_, v___x_66_, lean_box(0));
v___x_68_ = lean_unbox(v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v_one_69_; lean_object* v_n_70_; 
v_one_69_ = lean_unsigned_to_nat(1u);
v_n_70_ = lean_nat_sub(v_i_62_, v_one_69_);
lean_dec(v_i_62_);
v_i_62_ = v_n_70_;
goto _start;
}
else
{
uint8_t v___x_72_; 
lean_dec(v_i_62_);
lean_dec_ref(v_f_61_);
v___x_72_ = lean_unbox(v___x_67_);
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg___boxed(lean_object* v_n_73_, lean_object* v_f_74_, lean_object* v_i_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_73_, v_f_74_, v_i_75_);
lean_dec(v_n_73_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(lean_object* v_n_78_, lean_object* v_f_79_, lean_object* v_i_80_, lean_object* v_a_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_78_, v_f_79_, v_i_80_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___boxed(lean_object* v_n_83_, lean_object* v_f_84_, lean_object* v_i_85_, lean_object* v_a_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop(v_n_83_, v_f_84_, v_i_85_, v_a_86_);
lean_dec(v_n_83_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR(lean_object* v_n_89_, lean_object* v_f_90_){
_start:
{
uint8_t v___x_91_; 
lean_inc(v_n_89_);
v___x_91_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v_n_89_, v_f_90_, v_n_89_);
lean_dec(v_n_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR___boxed(lean_object* v_n_92_, lean_object* v_f_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Nat_anyTR(v_n_92_, v_f_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(lean_object* v_n_96_, lean_object* v_f_97_, lean_object* v_i_98_){
_start:
{
lean_object* v_zero_99_; uint8_t v_isZero_100_; 
v_zero_99_ = lean_unsigned_to_nat(0u);
v_isZero_100_ = lean_nat_dec_eq(v_i_98_, v_zero_99_);
if (v_isZero_100_ == 1)
{
lean_dec(v_i_98_);
lean_dec_ref(v_f_97_);
return v_isZero_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_101_ = lean_nat_sub(v_n_96_, v_i_98_);
lean_inc_ref(v_f_97_);
v___x_102_ = lean_apply_2(v_f_97_, v___x_101_, lean_box(0));
v___x_103_ = lean_unbox(v___x_102_);
if (v___x_103_ == 0)
{
uint8_t v___x_104_; 
lean_dec(v_i_98_);
lean_dec_ref(v_f_97_);
v___x_104_ = lean_unbox(v___x_102_);
return v___x_104_;
}
else
{
lean_object* v_one_105_; lean_object* v_n_106_; 
v_one_105_ = lean_unsigned_to_nat(1u);
v_n_106_ = lean_nat_sub(v_i_98_, v_one_105_);
lean_dec(v_i_98_);
v_i_98_ = v_n_106_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg___boxed(lean_object* v_n_108_, lean_object* v_f_109_, lean_object* v_i_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_108_, v_f_109_, v_i_110_);
lean_dec(v_n_108_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(lean_object* v_n_113_, lean_object* v_f_114_, lean_object* v_i_115_, lean_object* v_a_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_113_, v_f_114_, v_i_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___boxed(lean_object* v_n_118_, lean_object* v_f_119_, lean_object* v_i_120_, lean_object* v_a_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop(v_n_118_, v_f_119_, v_i_120_, v_a_121_);
lean_dec(v_n_118_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT uint8_t l_Nat_allTR(lean_object* v_n_124_, lean_object* v_f_125_){
_start:
{
uint8_t v___x_126_; 
lean_inc(v_n_124_);
v___x_126_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v_n_124_, v_f_125_, v_n_124_);
lean_dec(v_n_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Nat_allTR___boxed(lean_object* v_n_127_, lean_object* v_f_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Nat_allTR(v_n_127_, v_f_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg(lean_object* v_x_131_, lean_object* v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_){
_start:
{
lean_object* v_zero_135_; uint8_t v_isZero_136_; 
v_zero_135_ = lean_unsigned_to_nat(0u);
v_isZero_136_ = lean_nat_dec_eq(v_x_131_, v_zero_135_);
if (v_isZero_136_ == 1)
{
lean_object* v___x_137_; 
lean_dec(v_h__2_134_);
v___x_137_ = lean_apply_2(v_h__1_133_, lean_box(0), v_x_132_);
return v___x_137_;
}
else
{
lean_object* v_one_138_; lean_object* v_n_139_; lean_object* v___x_140_; 
lean_dec(v_h__1_133_);
v_one_138_ = lean_unsigned_to_nat(1u);
v_n_139_ = lean_nat_sub(v_x_131_, v_one_138_);
v___x_140_ = lean_apply_3(v_h__2_134_, v_n_139_, lean_box(0), v_x_132_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_141_, lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___redArg(v_x_141_, v_x_142_, v_h__1_143_, v_h__2_144_);
lean_dec(v_x_141_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter(lean_object* v_00_u03b1_146_, lean_object* v_n_147_, lean_object* v_motive_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_h__1_152_, lean_object* v_h__2_153_){
_start:
{
lean_object* v_zero_154_; uint8_t v_isZero_155_; 
v_zero_154_ = lean_unsigned_to_nat(0u);
v_isZero_155_ = lean_nat_dec_eq(v_x_149_, v_zero_154_);
if (v_isZero_155_ == 1)
{
lean_object* v___x_156_; 
lean_dec(v_h__2_153_);
v___x_156_ = lean_apply_2(v_h__1_152_, lean_box(0), v_x_151_);
return v___x_156_;
}
else
{
lean_object* v_one_157_; lean_object* v_n_158_; lean_object* v___x_159_; 
lean_dec(v_h__1_152_);
v_one_157_ = lean_unsigned_to_nat(1u);
v_n_158_ = lean_nat_sub(v_x_149_, v_one_157_);
v___x_159_ = lean_apply_3(v_h__2_153_, v_n_158_, lean_box(0), v_x_151_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter___boxed(lean_object* v_00_u03b1_160_, lean_object* v_n_161_, lean_object* v_motive_162_, lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_h__1_166_, lean_object* v_h__2_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop_match__1_splitter(v_00_u03b1_160_, v_n_161_, v_motive_162_, v_x_163_, v_x_164_, v_x_165_, v_h__1_166_, v_h__2_167_);
lean_dec(v_x_163_);
lean_dec(v_n_161_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_h__1_172_, lean_object* v_h__2_173_){
_start:
{
lean_object* v_zero_174_; uint8_t v_isZero_175_; 
v_zero_174_ = lean_unsigned_to_nat(0u);
v_isZero_175_ = lean_nat_dec_eq(v_x_169_, v_zero_174_);
if (v_isZero_175_ == 1)
{
lean_object* v___x_176_; 
lean_dec(v_h__2_173_);
v___x_176_ = lean_apply_2(v_h__1_172_, v_x_170_, v_x_171_);
return v___x_176_;
}
else
{
lean_object* v_one_177_; lean_object* v_n_178_; lean_object* v___x_179_; 
lean_dec(v_h__1_172_);
v_one_177_ = lean_unsigned_to_nat(1u);
v_n_178_ = lean_nat_sub(v_x_169_, v_one_177_);
v___x_179_ = lean_apply_3(v_h__2_173_, v_n_178_, v_x_170_, v_x_171_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg___boxed(lean_object* v_x_180_, lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_h__1_183_, lean_object* v_h__2_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___redArg(v_x_180_, v_x_181_, v_x_182_, v_h__1_183_, v_h__2_184_);
lean_dec(v_x_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter(lean_object* v_00_u03b1_186_, lean_object* v_motive_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_h__1_191_, lean_object* v_h__2_192_){
_start:
{
lean_object* v_zero_193_; uint8_t v_isZero_194_; 
v_zero_193_ = lean_unsigned_to_nat(0u);
v_isZero_194_ = lean_nat_dec_eq(v_x_188_, v_zero_193_);
if (v_isZero_194_ == 1)
{
lean_object* v___x_195_; 
lean_dec(v_h__2_192_);
v___x_195_ = lean_apply_2(v_h__1_191_, v_x_189_, v_x_190_);
return v___x_195_;
}
else
{
lean_object* v_one_196_; lean_object* v_n_197_; lean_object* v___x_198_; 
lean_dec(v_h__1_191_);
v_one_196_ = lean_unsigned_to_nat(1u);
v_n_197_ = lean_nat_sub(v_x_188_, v_one_196_);
v___x_198_ = lean_apply_3(v_h__2_192_, v_n_197_, v_x_189_, v_x_190_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter___boxed(lean_object* v_00_u03b1_199_, lean_object* v_motive_200_, lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_h__1_204_, lean_object* v_h__2_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Init_Data_Nat_Fold_0__Nat_fold_match__1_splitter(v_00_u03b1_199_, v_motive_200_, v_x_201_, v_x_202_, v_x_203_, v_h__1_204_, v_h__2_205_);
lean_dec(v_x_201_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(lean_object* v_x_207_, lean_object* v_h__1_208_, lean_object* v_h__2_209_){
_start:
{
lean_object* v_zero_210_; uint8_t v_isZero_211_; 
v_zero_210_ = lean_unsigned_to_nat(0u);
v_isZero_211_ = lean_nat_dec_eq(v_x_207_, v_zero_210_);
if (v_isZero_211_ == 1)
{
lean_object* v___x_212_; 
lean_dec(v_h__2_209_);
v___x_212_ = lean_apply_1(v_h__1_208_, lean_box(0));
return v___x_212_;
}
else
{
lean_object* v_one_213_; lean_object* v_n_214_; lean_object* v___x_215_; 
lean_dec(v_h__1_208_);
v_one_213_ = lean_unsigned_to_nat(1u);
v_n_214_ = lean_nat_sub(v_x_207_, v_one_213_);
v___x_215_ = lean_apply_2(v_h__2_209_, v_n_214_, lean_box(0));
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_216_, lean_object* v_h__1_217_, lean_object* v_h__2_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___redArg(v_x_216_, v_h__1_217_, v_h__2_218_);
lean_dec(v_x_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter(lean_object* v_n_220_, lean_object* v_motive_221_, lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_h__1_224_, lean_object* v_h__2_225_){
_start:
{
lean_object* v_zero_226_; uint8_t v_isZero_227_; 
v_zero_226_ = lean_unsigned_to_nat(0u);
v_isZero_227_ = lean_nat_dec_eq(v_x_222_, v_zero_226_);
if (v_isZero_227_ == 1)
{
lean_object* v___x_228_; 
lean_dec(v_h__2_225_);
v___x_228_ = lean_apply_1(v_h__1_224_, lean_box(0));
return v___x_228_;
}
else
{
lean_object* v_one_229_; lean_object* v_n_230_; lean_object* v___x_231_; 
lean_dec(v_h__1_224_);
v_one_229_ = lean_unsigned_to_nat(1u);
v_n_230_ = lean_nat_sub(v_x_222_, v_one_229_);
v___x_231_ = lean_apply_2(v_h__2_225_, v_n_230_, lean_box(0));
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter___boxed(lean_object* v_n_232_, lean_object* v_motive_233_, lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_h__1_236_, lean_object* v_h__2_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop_match__1_splitter(v_n_232_, v_motive_233_, v_x_234_, v_x_235_, v_h__1_236_, v_h__2_237_);
lean_dec(v_x_234_);
lean_dec(v_n_232_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_h__1_241_, lean_object* v_h__2_242_){
_start:
{
lean_object* v_zero_243_; uint8_t v_isZero_244_; 
v_zero_243_ = lean_unsigned_to_nat(0u);
v_isZero_244_ = lean_nat_dec_eq(v_x_239_, v_zero_243_);
if (v_isZero_244_ == 1)
{
lean_object* v___x_245_; 
lean_dec(v_h__2_242_);
v___x_245_ = lean_apply_1(v_h__1_241_, v_x_240_);
return v___x_245_;
}
else
{
lean_object* v_one_246_; lean_object* v_n_247_; lean_object* v___x_248_; 
lean_dec(v_h__1_241_);
v_one_246_ = lean_unsigned_to_nat(1u);
v_n_247_ = lean_nat_sub(v_x_239_, v_one_246_);
v___x_248_ = lean_apply_2(v_h__2_242_, v_n_247_, v_x_240_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg___boxed(lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_h__1_251_, lean_object* v_h__2_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___redArg(v_x_249_, v_x_250_, v_h__1_251_, v_h__2_252_);
lean_dec(v_x_249_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter(lean_object* v_motive_254_, lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_h__1_257_, lean_object* v_h__2_258_){
_start:
{
lean_object* v_zero_259_; uint8_t v_isZero_260_; 
v_zero_259_ = lean_unsigned_to_nat(0u);
v_isZero_260_ = lean_nat_dec_eq(v_x_255_, v_zero_259_);
if (v_isZero_260_ == 1)
{
lean_object* v___x_261_; 
lean_dec(v_h__2_258_);
v___x_261_ = lean_apply_1(v_h__1_257_, v_x_256_);
return v___x_261_;
}
else
{
lean_object* v_one_262_; lean_object* v_n_263_; lean_object* v___x_264_; 
lean_dec(v_h__1_257_);
v_one_262_ = lean_unsigned_to_nat(1u);
v_n_263_ = lean_nat_sub(v_x_255_, v_one_262_);
v___x_264_ = lean_apply_2(v_h__2_258_, v_n_263_, v_x_256_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter___boxed(lean_object* v_motive_265_, lean_object* v_x_266_, lean_object* v_x_267_, lean_object* v_h__1_268_, lean_object* v_h__2_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Init_Data_Nat_Fold_0__Nat_any_match__1_splitter(v_motive_265_, v_x_266_, v_x_267_, v_h__1_268_, v_h__2_269_);
lean_dec(v_x_266_);
return v_res_270_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__10));
v___x_298_ = l_Lean_mkAtom(v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__12);
v___x_300_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_301_ = lean_array_push(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__16));
v___x_313_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_314_ = lean_array_push(v___x_313_, v___x_312_);
return v___x_314_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__17);
v___x_316_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__15));
v___x_317_ = lean_box(2);
v___x_318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
lean_ctor_set(v___x_318_, 2, v___x_315_);
return v___x_318_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__18);
v___x_320_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__13);
v___x_321_ = lean_array_push(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_322_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__19);
v___x_323_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__11));
v___x_324_ = lean_box(2);
v___x_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_323_);
lean_ctor_set(v___x_325_, 2, v___x_322_);
return v___x_325_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__20);
v___x_327_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_328_ = lean_array_push(v___x_327_, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__21);
v___x_330_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__9));
v___x_331_ = lean_box(2);
v___x_332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_329_);
return v___x_332_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__22);
v___x_334_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_335_ = lean_array_push(v___x_334_, v___x_333_);
return v___x_335_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_336_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__23);
v___x_337_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__7));
v___x_338_ = lean_box(2);
v___x_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
lean_ctor_set(v___x_339_, 2, v___x_336_);
return v___x_339_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__24);
v___x_341_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__5));
v___x_342_ = lean_array_push(v___x_341_, v___x_340_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_343_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__25);
v___x_344_ = ((lean_object*)(l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__4));
v___x_345_ = lean_box(2);
v___x_346_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
lean_ctor_set(v___x_346_, 2, v___x_343_);
return v___x_346_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1(void){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(lean_object* v_x_348_){
_start:
{
lean_inc(v_x_348_);
return v_x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg___boxed(lean_object* v_x_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___redArg(v_x_349_);
lean_dec(v_x_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(lean_object* v_n_351_, lean_object* v_00_u03b1_352_, lean_object* v_i_353_, lean_object* v_j_354_, lean_object* v_hi_355_, lean_object* v_w_356_, lean_object* v_x_357_){
_start:
{
lean_inc(v_x_357_);
return v_x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___boxed(lean_object* v_n_358_, lean_object* v_00_u03b1_359_, lean_object* v_i_360_, lean_object* v_j_361_, lean_object* v_hi_362_, lean_object* v_w_363_, lean_object* v_x_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast(v_n_358_, v_00_u03b1_359_, v_i_360_, v_j_361_, v_hi_362_, v_w_363_, v_x_364_);
lean_dec(v_x_364_);
lean_dec(v_j_361_);
lean_dec(v_i_360_);
lean_dec(v_n_358_);
return v_res_365_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast__eq__dfoldCast__iff___auto__9(void){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_366_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_apply__dfoldCast___auto__3(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_367_;
}
}
static lean_object* _init_l_Nat_dfold___auto__1(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(lean_object* v_n_369_, lean_object* v_f_370_, lean_object* v_j_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_zero_373_; uint8_t v_isZero_374_; 
v_zero_373_ = lean_unsigned_to_nat(0u);
v_isZero_374_ = lean_nat_dec_eq(v_j_371_, v_zero_373_);
if (v_isZero_374_ == 1)
{
lean_dec(v_j_371_);
lean_dec(v_f_370_);
return v_a_372_;
}
else
{
lean_object* v_one_375_; lean_object* v_n_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_one_375_ = lean_unsigned_to_nat(1u);
v_n_376_ = lean_nat_sub(v_j_371_, v_one_375_);
v___x_377_ = lean_nat_sub(v_n_369_, v_j_371_);
lean_dec(v_j_371_);
lean_inc(v_f_370_);
v___x_378_ = lean_apply_3(v_f_370_, v___x_377_, lean_box(0), v_a_372_);
v_j_371_ = v_n_376_;
v_a_372_ = v___x_378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg___boxed(lean_object* v_n_380_, lean_object* v_f_381_, lean_object* v_j_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_380_, v_f_381_, v_j_382_, v_a_383_);
lean_dec(v_n_380_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(lean_object* v_n_385_, lean_object* v_00_u03b1_386_, lean_object* v_f_387_, lean_object* v_j_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_385_, v_f_387_, v_j_388_, v_a_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___boxed(lean_object* v_n_392_, lean_object* v_00_u03b1_393_, lean_object* v_f_394_, lean_object* v_j_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop(v_n_392_, v_00_u03b1_393_, v_f_394_, v_j_395_, v_a_396_, v_a_397_);
lean_dec(v_n_392_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfold___redArg(lean_object* v_n_399_, lean_object* v_f_400_, lean_object* v_init_401_){
_start:
{
lean_object* v___x_402_; 
lean_inc(v_n_399_);
v___x_402_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_399_, v_f_400_, v_n_399_, v_init_401_);
lean_dec(v_n_399_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfold(lean_object* v_n_403_, lean_object* v_00_u03b1_404_, lean_object* v_f_405_, lean_object* v_init_406_){
_start:
{
lean_object* v___x_407_; 
lean_inc(v_n_403_);
v___x_407_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_loop___redArg(v_n_403_, v_f_405_, v_n_403_, v_init_406_);
lean_dec(v_n_403_);
return v___x_407_;
}
}
static lean_object* _init_l_Nat_dfoldRev___auto__1(void){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg___lam__0(lean_object* v_f_409_, lean_object* v_i_410_, lean_object* v_h_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_apply_3(v_f_409_, v_i_410_, lean_box(0), v___y_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev___redArg(lean_object* v_n_414_, lean_object* v_f_415_, lean_object* v_init_416_){
_start:
{
lean_object* v_zero_417_; uint8_t v_isZero_418_; 
v_zero_417_ = lean_unsigned_to_nat(0u);
v_isZero_418_ = lean_nat_dec_eq(v_n_414_, v_zero_417_);
if (v_isZero_418_ == 1)
{
lean_dec(v_f_415_);
lean_dec(v_n_414_);
return v_init_416_;
}
else
{
lean_object* v___f_419_; lean_object* v_one_420_; lean_object* v_n_421_; lean_object* v___x_422_; 
lean_inc(v_f_415_);
v___f_419_ = lean_alloc_closure((void*)(l_Nat_dfoldRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_419_, 0, v_f_415_);
v_one_420_ = lean_unsigned_to_nat(1u);
v_n_421_ = lean_nat_sub(v_n_414_, v_one_420_);
lean_dec(v_n_414_);
lean_inc(v_n_421_);
v___x_422_ = lean_apply_3(v_f_415_, v_n_421_, lean_box(0), v_init_416_);
v_n_414_ = v_n_421_;
v_f_415_ = v___f_419_;
v_init_416_ = v___x_422_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_dfoldRev(lean_object* v_n_424_, lean_object* v_00_u03b1_425_, lean_object* v_f_426_, lean_object* v_init_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Nat_dfoldRev___redArg(v_n_424_, v_f_426_, v_init_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Nat_dfold__zero___auto__1(void){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_h__1_432_, lean_object* v_h__2_433_){
_start:
{
lean_object* v_zero_434_; uint8_t v_isZero_435_; 
v_zero_434_ = lean_unsigned_to_nat(0u);
v_isZero_435_ = lean_nat_dec_eq(v_x_430_, v_zero_434_);
if (v_isZero_435_ == 1)
{
lean_object* v___x_436_; 
lean_dec(v_h__2_433_);
v___x_436_ = lean_apply_2(v_h__1_432_, lean_box(0), v_x_431_);
return v___x_436_;
}
else
{
lean_object* v_one_437_; lean_object* v_n_438_; lean_object* v___x_439_; 
lean_dec(v_h__1_432_);
v_one_437_ = lean_unsigned_to_nat(1u);
v_n_438_ = lean_nat_sub(v_x_430_, v_one_437_);
v___x_439_ = lean_apply_3(v_h__2_433_, v_n_438_, lean_box(0), v_x_431_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg___boxed(lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_h__1_442_, lean_object* v_h__2_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___redArg(v_x_440_, v_x_441_, v_h__1_442_, v_h__2_443_);
lean_dec(v_x_440_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter(lean_object* v_n_445_, lean_object* v_00_u03b1_446_, lean_object* v_motive_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_h__1_451_, lean_object* v_h__2_452_){
_start:
{
lean_object* v_zero_453_; uint8_t v_isZero_454_; 
v_zero_453_ = lean_unsigned_to_nat(0u);
v_isZero_454_ = lean_nat_dec_eq(v_x_448_, v_zero_453_);
if (v_isZero_454_ == 1)
{
lean_object* v___x_455_; 
lean_dec(v_h__2_452_);
v___x_455_ = lean_apply_2(v_h__1_451_, lean_box(0), v_x_450_);
return v___x_455_;
}
else
{
lean_object* v_one_456_; lean_object* v_n_457_; lean_object* v___x_458_; 
lean_dec(v_h__1_451_);
v_one_456_ = lean_unsigned_to_nat(1u);
v_n_457_ = lean_nat_sub(v_x_448_, v_one_456_);
v___x_458_ = lean_apply_3(v_h__2_452_, v_n_457_, lean_box(0), v_x_450_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter___boxed(lean_object* v_n_459_, lean_object* v_00_u03b1_460_, lean_object* v_motive_461_, lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_h__1_465_, lean_object* v_h__2_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Init_Data_Nat_Fold_0__Nat_dfold_match__2_splitter(v_n_459_, v_00_u03b1_460_, v_motive_461_, v_x_462_, v_x_463_, v_x_464_, v_h__1_465_, v_h__2_466_);
lean_dec(v_x_462_);
lean_dec(v_n_459_);
return v_res_467_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Fold_0__Nat_dfold__loop__succ___auto__5(void){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_468_;
}
}
static lean_object* _init_l_Nat_dfold__succ___auto__3(void){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_469_;
}
}
static lean_object* _init_l_Nat_dfold__congr___auto__1(void){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_470_;
}
}
static lean_object* _init_l_Nat_dfold__add___auto__5(void){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_471_;
}
}
static lean_object* _init_l_Nat_dfoldRev__zero___auto__1(void){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg(lean_object* v_n_473_, lean_object* v_f_474_, lean_object* v_init_475_, lean_object* v_h__1_476_, lean_object* v_h__2_477_){
_start:
{
lean_object* v_zero_478_; uint8_t v_isZero_479_; 
v_zero_478_ = lean_unsigned_to_nat(0u);
v_isZero_479_ = lean_nat_dec_eq(v_n_473_, v_zero_478_);
if (v_isZero_479_ == 1)
{
lean_object* v___x_480_; 
lean_dec(v_h__2_477_);
v___x_480_ = lean_apply_3(v_h__1_476_, lean_box(0), v_f_474_, v_init_475_);
return v___x_480_;
}
else
{
lean_object* v_one_481_; lean_object* v_n_482_; lean_object* v___x_483_; 
lean_dec(v_h__1_476_);
v_one_481_ = lean_unsigned_to_nat(1u);
v_n_482_ = lean_nat_sub(v_n_473_, v_one_481_);
v___x_483_ = lean_apply_4(v_h__2_477_, v_n_482_, lean_box(0), v_f_474_, v_init_475_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg___boxed(lean_object* v_n_484_, lean_object* v_f_485_, lean_object* v_init_486_, lean_object* v_h__1_487_, lean_object* v_h__2_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___redArg(v_n_484_, v_f_485_, v_init_486_, v_h__1_487_, v_h__2_488_);
lean_dec(v_n_484_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter(lean_object* v_motive_490_, lean_object* v_n_491_, lean_object* v_00_u03b1_492_, lean_object* v_f_493_, lean_object* v_init_494_, lean_object* v_h__1_495_, lean_object* v_h__2_496_){
_start:
{
lean_object* v_zero_497_; uint8_t v_isZero_498_; 
v_zero_497_ = lean_unsigned_to_nat(0u);
v_isZero_498_ = lean_nat_dec_eq(v_n_491_, v_zero_497_);
if (v_isZero_498_ == 1)
{
lean_object* v___x_499_; 
lean_dec(v_h__2_496_);
v___x_499_ = lean_apply_3(v_h__1_495_, lean_box(0), v_f_493_, v_init_494_);
return v___x_499_;
}
else
{
lean_object* v_one_500_; lean_object* v_n_501_; lean_object* v___x_502_; 
lean_dec(v_h__1_495_);
v_one_500_ = lean_unsigned_to_nat(1u);
v_n_501_ = lean_nat_sub(v_n_491_, v_one_500_);
v___x_502_ = lean_apply_4(v_h__2_496_, v_n_501_, lean_box(0), v_f_493_, v_init_494_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter___boxed(lean_object* v_motive_503_, lean_object* v_n_504_, lean_object* v_00_u03b1_505_, lean_object* v_f_506_, lean_object* v_init_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Init_Data_Nat_Fold_0__Nat_dfoldRev_match__1_splitter(v_motive_503_, v_n_504_, v_00_u03b1_505_, v_f_506_, v_init_507_, v_h__1_508_, v_h__2_509_);
lean_dec(v_n_504_);
return v_res_510_;
}
}
static lean_object* _init_l_Nat_dfoldRev__succ___auto__3(void){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_511_;
}
}
static lean_object* _init_l_Nat_dfoldRev__congr___auto__1(void){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_512_;
}
}
static lean_object* _init_l_Nat_dfoldRev__add___auto__5(void){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = lean_obj_once(&l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26, &l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26_once, _init_l___private_Init_Data_Nat_Fold_0__Nat_dfoldCast___auto__1___closed__26);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0(lean_object* v_fst_514_, lean_object* v_f_515_, lean_object* v_j_516_, lean_object* v_x_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_nat_add(v_fst_514_, v_j_516_);
v___x_520_ = lean_apply_4(v_f_515_, v___x_519_, lean_box(0), lean_box(0), v___y_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg___lam__0___boxed(lean_object* v_fst_521_, lean_object* v_f_522_, lean_object* v_j_523_, lean_object* v_x_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Prod_foldI___redArg___lam__0(v_fst_521_, v_f_522_, v_j_523_, v_x_524_, v___y_525_);
lean_dec(v_j_523_);
lean_dec(v_fst_521_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI___redArg(lean_object* v_i_527_, lean_object* v_f_528_, lean_object* v_init_529_){
_start:
{
lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v___f_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_fst_530_ = lean_ctor_get(v_i_527_, 0);
lean_inc_n(v_fst_530_, 2);
v_snd_531_ = lean_ctor_get(v_i_527_, 1);
lean_inc(v_snd_531_);
lean_dec_ref(v_i_527_);
v___f_532_ = lean_alloc_closure((void*)(l_Prod_foldI___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_532_, 0, v_fst_530_);
lean_closure_set(v___f_532_, 1, v_f_528_);
v___x_533_ = lean_nat_sub(v_snd_531_, v_fst_530_);
lean_dec(v_fst_530_);
lean_dec(v_snd_531_);
lean_inc(v___x_533_);
v___x_534_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v___x_533_, v___f_532_, v___x_533_, v_init_529_);
lean_dec(v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Prod_foldI(lean_object* v_00_u03b1_535_, lean_object* v_i_536_, lean_object* v_f_537_, lean_object* v_init_538_){
_start:
{
lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_fst_539_ = lean_ctor_get(v_i_536_, 0);
lean_inc_n(v_fst_539_, 2);
v_snd_540_ = lean_ctor_get(v_i_536_, 1);
lean_inc(v_snd_540_);
lean_dec_ref(v_i_536_);
v___f_541_ = lean_alloc_closure((void*)(l_Prod_foldI___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_541_, 0, v_fst_539_);
lean_closure_set(v___f_541_, 1, v_f_537_);
v___x_542_ = lean_nat_sub(v_snd_540_, v_fst_539_);
lean_dec(v_fst_539_);
lean_dec(v_snd_540_);
lean_inc(v___x_542_);
v___x_543_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___redArg(v___x_542_, v___f_541_, v___x_542_, v_init_538_);
lean_dec(v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT uint8_t l_Prod_anyI___lam__0(lean_object* v_fst_544_, lean_object* v_f_545_, lean_object* v_j_546_, lean_object* v_x_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_548_ = lean_nat_add(v_fst_544_, v_j_546_);
v___x_549_ = lean_apply_3(v_f_545_, v___x_548_, lean_box(0), lean_box(0));
v___x_550_ = lean_unbox(v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Prod_anyI___lam__0___boxed(lean_object* v_fst_551_, lean_object* v_f_552_, lean_object* v_j_553_, lean_object* v_x_554_){
_start:
{
uint8_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_Prod_anyI___lam__0(v_fst_551_, v_f_552_, v_j_553_, v_x_554_);
lean_dec(v_j_553_);
lean_dec(v_fst_551_);
v_r_556_ = lean_box(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT uint8_t l_Prod_anyI(lean_object* v_i_557_, lean_object* v_f_558_){
_start:
{
lean_object* v_fst_559_; lean_object* v_snd_560_; lean_object* v___f_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_fst_559_ = lean_ctor_get(v_i_557_, 0);
lean_inc_n(v_fst_559_, 2);
v_snd_560_ = lean_ctor_get(v_i_557_, 1);
lean_inc(v_snd_560_);
lean_dec_ref(v_i_557_);
v___f_561_ = lean_alloc_closure((void*)(l_Prod_anyI___lam__0___boxed), 4, 2);
lean_closure_set(v___f_561_, 0, v_fst_559_);
lean_closure_set(v___f_561_, 1, v_f_558_);
v___x_562_ = lean_nat_sub(v_snd_560_, v_fst_559_);
lean_dec(v_fst_559_);
lean_dec(v_snd_560_);
lean_inc(v___x_562_);
v___x_563_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___redArg(v___x_562_, v___f_561_, v___x_562_);
lean_dec(v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Prod_anyI___boxed(lean_object* v_i_564_, lean_object* v_f_565_){
_start:
{
uint8_t v_res_566_; lean_object* v_r_567_; 
v_res_566_ = l_Prod_anyI(v_i_564_, v_f_565_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT uint8_t l_Prod_allI(lean_object* v_i_568_, lean_object* v_f_569_){
_start:
{
lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___f_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_fst_570_ = lean_ctor_get(v_i_568_, 0);
lean_inc_n(v_fst_570_, 2);
v_snd_571_ = lean_ctor_get(v_i_568_, 1);
lean_inc(v_snd_571_);
lean_dec_ref(v_i_568_);
v___f_572_ = lean_alloc_closure((void*)(l_Prod_anyI___lam__0___boxed), 4, 2);
lean_closure_set(v___f_572_, 0, v_fst_570_);
lean_closure_set(v___f_572_, 1, v_f_569_);
v___x_573_ = lean_nat_sub(v_snd_571_, v_fst_570_);
lean_dec(v_fst_570_);
lean_dec(v_snd_571_);
lean_inc(v___x_573_);
v___x_574_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___redArg(v___x_573_, v___f_572_, v___x_573_);
lean_dec(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Prod_allI___boxed(lean_object* v_i_575_, lean_object* v_f_576_){
_start:
{
uint8_t v_res_577_; lean_object* v_r_578_; 
v_res_577_ = l_Prod_allI(v_i_575_, v_f_576_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
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
