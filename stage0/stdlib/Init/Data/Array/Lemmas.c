// Lean compiler output
// Module: Init.Data.Array.Lemmas
// Imports: public import Init.Data.List.ToArray import all Init.Data.List.Control import all Init.Data.Array.Basic import all Init.Data.Array.Bootstrap public import Init.Data.Nat.Lemmas public import Init.Data.Nat.MinMax import Init.ByCases import Init.Data.Array.DecidableEq import Init.Data.Bool import Init.Data.Fin.Lemmas import Init.Data.List.Find import Init.Data.List.Nat.Basic import Init.Data.List.Nat.Modify import Init.Data.List.Nat.TakeDrop import Init.Data.List.Range import Init.Data.List.Zip import Init.Data.Nat.Internal.Linear import Init.Data.Nat.Simproc import Init.Data.Option.Lemmas import Init.Data.Prod import Init.Omega import Init.TacticsExtra
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
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableForallForallMemOfDecidablePred___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableForallForallMemOfDecidablePred(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableExistsAndMemOfDecidablePred___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_mapA_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_mapA_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_filterMap__replicate___auto__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__0 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__0_value;
static const lean_string_object l_Array_filterMap__replicate___auto__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__1 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__1_value;
static const lean_string_object l_Array_filterMap__replicate___auto__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__2 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__2_value;
static const lean_string_object l_Array_filterMap__replicate___auto__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__3 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__3_value;
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__4_value_aux_0),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__4_value_aux_1),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__4_value_aux_2),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__4 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__4_value;
static const lean_array_object l_Array_filterMap__replicate___auto__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__5 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__5_value;
static const lean_string_object l_Array_filterMap__replicate___auto__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__6 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__6_value;
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__7_value_aux_0),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__7_value_aux_1),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__7_value_aux_2),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__7 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__7_value;
static const lean_string_object l_Array_filterMap__replicate___auto__7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__8 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__8_value;
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__9 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__9_value;
static const lean_string_object l_Array_filterMap__replicate___auto__7___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__10 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__10_value;
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__11_value_aux_0),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__11_value_aux_1),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__11_value_aux_2),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__11 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__11_value;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__12;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__13;
static const lean_string_object l_Array_filterMap__replicate___auto__7___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__14 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__14_value;
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__15_value_aux_0),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__15_value_aux_1),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__15_value_aux_2),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__15 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__15_value;
static const lean_ctor_object l_Array_filterMap__replicate___auto__7___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__9_value),((lean_object*)&l_Array_filterMap__replicate___auto__7___closed__5_value)}};
static const lean_object* l_Array_filterMap__replicate___auto__7___closed__16 = (const lean_object*)&l_Array_filterMap__replicate___auto__7___closed__16_value;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__17;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__18;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__19;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__20;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__21;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__22;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__23;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__24;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__25;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__26;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__27;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__28;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__29;
static lean_once_cell_t l_Array_filterMap__replicate___auto__7___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMap__replicate___auto__7___closed__30;
LEAN_EXPORT lean_object* l_Array_filterMap__replicate___auto__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListRev___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Array_toListRev___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toListRev___redArg___closed__0 = (const lean_object*)&l_Array_toListRev___redArg___closed__0_value;
static const lean_closure_object l_Array_toListRev___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toListRev___redArg___closed__1 = (const lean_object*)&l_Array_toListRev___redArg___closed__1_value;
static const lean_closure_object l_Array_toListRev___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toListRev___redArg___closed__2 = (const lean_object*)&l_Array_toListRev___redArg___closed__2_value;
static const lean_closure_object l_Array_toListRev___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toListRev___redArg___closed__3 = (const lean_object*)&l_Array_toListRev___redArg___closed__3_value;
static const lean_closure_object l_Array_toListRev___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toListRev___redArg___closed__4 = (const lean_object*)&l_Array_toListRev___redArg___closed__4_value;
static const lean_closure_object l_Array_toListRev___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toListRev___redArg___closed__5 = (const lean_object*)&l_Array_toListRev___redArg___closed__5_value;
static const lean_closure_object l_Array_toListRev___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toListRev___redArg___closed__6 = (const lean_object*)&l_Array_toListRev___redArg___closed__6_value;
static const lean_ctor_object l_Array_toListRev___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_toListRev___redArg___closed__0_value),((lean_object*)&l_Array_toListRev___redArg___closed__1_value)}};
static const lean_object* l_Array_toListRev___redArg___closed__7 = (const lean_object*)&l_Array_toListRev___redArg___closed__7_value;
static const lean_ctor_object l_Array_toListRev___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_toListRev___redArg___closed__7_value),((lean_object*)&l_Array_toListRev___redArg___closed__2_value),((lean_object*)&l_Array_toListRev___redArg___closed__3_value),((lean_object*)&l_Array_toListRev___redArg___closed__4_value),((lean_object*)&l_Array_toListRev___redArg___closed__5_value)}};
static const lean_object* l_Array_toListRev___redArg___closed__8 = (const lean_object*)&l_Array_toListRev___redArg___closed__8_value;
static const lean_ctor_object l_Array_toListRev___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_toListRev___redArg___closed__8_value),((lean_object*)&l_Array_toListRev___redArg___closed__6_value)}};
static const lean_object* l_Array_toListRev___redArg___closed__9 = (const lean_object*)&l_Array_toListRev___redArg___closed__9_value;
static const lean_closure_object l_Array_toListRev___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_toListRev___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toListRev___redArg___closed__10 = (const lean_object*)&l_Array_toListRev___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Array_toListRev___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_toListRev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(lean_object* v_xs_1_, lean_object* v_inst_2_, lean_object* v_i_3_, lean_object* v_h_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_array_fget_borrowed(v_xs_1_, v_i_3_);
lean_inc(v___x_5_);
v___x_6_ = lean_apply_1(v_inst_2_, v___x_5_);
v___x_7_ = lean_unbox(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(lean_object* v_xs_8_, lean_object* v_inst_9_, lean_object* v_i_10_, lean_object* v_h_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(v_xs_8_, v_inst_9_, v_i_10_, v_h_11_);
lean_dec(v_i_10_);
lean_dec_ref(v_xs_8_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableForallForallMemOfDecidablePred___redArg(lean_object* v_xs_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
lean_inc_ref(v_xs_14_);
v___f_16_ = lean_alloc_closure((void*)(l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_16_, 0, v_xs_14_);
lean_closure_set(v___f_16_, 1, v_inst_15_);
v___x_17_ = lean_array_get_size(v_xs_14_);
lean_dec_ref(v_xs_14_);
v___x_18_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(v___x_17_, v___f_16_, v___x_17_, lean_box(0));
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___redArg___boxed(lean_object* v_xs_19_, lean_object* v_inst_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Array_instDecidableForallForallMemOfDecidablePred___redArg(v_xs_19_, v_inst_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableForallForallMemOfDecidablePred(lean_object* v_00_u03b1_23_, lean_object* v_xs_24_, lean_object* v_p_25_, lean_object* v_inst_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = l_Array_instDecidableForallForallMemOfDecidablePred___redArg(v_xs_24_, v_inst_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___boxed(lean_object* v_00_u03b1_28_, lean_object* v_xs_29_, lean_object* v_p_30_, lean_object* v_inst_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Array_instDecidableForallForallMemOfDecidablePred(v_00_u03b1_28_, v_xs_29_, v_p_30_, v_inst_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(lean_object* v_xs_34_, lean_object* v_inst_35_){
_start:
{
lean_object* v___f_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
lean_inc_ref(v_xs_34_);
v___f_36_ = lean_alloc_closure((void*)(l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_36_, 0, v_xs_34_);
lean_closure_set(v___f_36_, 1, v_inst_35_);
v___x_37_ = lean_array_get_size(v_xs_34_);
lean_dec_ref(v_xs_34_);
v___x_38_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(v___x_37_, v___f_36_, v___x_37_, lean_box(0));
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___boxed(lean_object* v_xs_39_, lean_object* v_inst_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_xs_39_, v_inst_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred(lean_object* v_00_u03b1_43_, lean_object* v_xs_44_, lean_object* v_p_45_, lean_object* v_inst_46_){
_start:
{
uint8_t v___x_47_; 
v___x_47_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_xs_44_, v_inst_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableExistsAndMemOfDecidablePred___boxed(lean_object* v_00_u03b1_48_, lean_object* v_xs_49_, lean_object* v_p_50_, lean_object* v_inst_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Array_instDecidableExistsAndMemOfDecidablePred(v_00_u03b1_48_, v_xs_49_, v_p_50_, v_inst_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_mapA_match__1_splitter___redArg(lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_56_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_apply_1(v_h__1_55_, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v_head_59_; lean_object* v_tail_60_; lean_object* v___x_61_; 
lean_dec(v_h__1_55_);
v_head_59_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_head_59_);
v_tail_60_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_tail_60_);
lean_dec_ref_known(v_x_54_, 2);
v___x_61_ = lean_apply_2(v_h__2_56_, v_head_59_, v_tail_60_);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_mapA_match__1_splitter(lean_object* v_00_u03b1_62_, lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
if (lean_obj_tag(v_x_64_) == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_h__2_66_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_apply_1(v_h__1_65_, v___x_67_);
return v___x_68_;
}
else
{
lean_object* v_head_69_; lean_object* v_tail_70_; lean_object* v___x_71_; 
lean_dec(v_h__1_65_);
v_head_69_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_head_69_);
v_tail_70_ = lean_ctor_get(v_x_64_, 1);
lean_inc(v_tail_70_);
lean_dec_ref_known(v_x_64_, 2);
v___x_71_ = lean_apply_2(v_h__2_66_, v_head_69_, v_tail_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
if (v_____do__lift_72_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_h__1_73_);
v___x_75_ = lean_box(0);
v___x_76_ = lean_apply_1(v_h__2_74_, v___x_75_);
return v___x_76_;
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_h__2_74_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_apply_1(v_h__1_73_, v___x_77_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
uint8_t v_____do__lift_24__boxed_82_; lean_object* v_res_83_; 
v_____do__lift_24__boxed_82_ = lean_unbox(v_____do__lift_79_);
v_res_83_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(v_____do__lift_24__boxed_82_, v_h__1_80_, v_h__2_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(lean_object* v_motive_84_, uint8_t v_____do__lift_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
_start:
{
if (v_____do__lift_85_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_h__1_86_);
v___x_88_ = lean_box(0);
v___x_89_ = lean_apply_1(v_h__2_87_, v___x_88_);
return v___x_89_;
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_h__2_87_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_apply_1(v_h__1_86_, v___x_90_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_92_, lean_object* v_____do__lift_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_){
_start:
{
uint8_t v_____do__lift_35__boxed_96_; lean_object* v_res_97_; 
v_____do__lift_35__boxed_96_ = lean_unbox(v_____do__lift_93_);
v_res_97_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(v_motive_92_, v_____do__lift_35__boxed_96_, v_h__1_94_, v_h__2_95_);
return v_res_97_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_98_, lean_object* v_a_99_, lean_object* v_as_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = l_Array_contains___redArg(v_inst_98_, v_as_100_, v_a_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_102_, lean_object* v_a_103_, lean_object* v_as_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Array_instDecidableMemOfLawfulBEq___redArg(v_inst_102_, v_a_103_, v_as_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_a_110_, lean_object* v_as_111_){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = l_Array_contains___redArg(v_inst_108_, v_as_111_, v_a_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_a_116_, lean_object* v_as_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Array_instDecidableMemOfLawfulBEq(v_00_u03b1_113_, v_inst_114_, v_inst_115_, v_a_116_, v_as_117_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_){
_start:
{
lean_object* v_zero_123_; uint8_t v_isZero_124_; 
v_zero_123_ = lean_unsigned_to_nat(0u);
v_isZero_124_ = lean_nat_dec_eq(v_x_120_, v_zero_123_);
if (v_isZero_124_ == 1)
{
lean_object* v___x_125_; 
lean_dec(v_h__2_122_);
v___x_125_ = lean_apply_1(v_h__1_121_, lean_box(0));
return v___x_125_;
}
else
{
lean_object* v_one_126_; lean_object* v_n_127_; lean_object* v___x_128_; 
lean_dec(v_h__1_121_);
v_one_126_ = lean_unsigned_to_nat(1u);
v_n_127_ = lean_nat_sub(v_x_120_, v_one_126_);
v___x_128_ = lean_apply_2(v_h__2_122_, v_n_127_, lean_box(0));
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(v_x_129_, v_h__1_130_, v_h__2_131_);
lean_dec(v_x_129_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_133_, lean_object* v_xs_134_, lean_object* v_motive_135_, lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_){
_start:
{
lean_object* v_zero_140_; uint8_t v_isZero_141_; 
v_zero_140_ = lean_unsigned_to_nat(0u);
v_isZero_141_ = lean_nat_dec_eq(v_x_136_, v_zero_140_);
if (v_isZero_141_ == 1)
{
lean_object* v___x_142_; 
lean_dec(v_h__2_139_);
v___x_142_ = lean_apply_1(v_h__1_138_, lean_box(0));
return v___x_142_;
}
else
{
lean_object* v_one_143_; lean_object* v_n_144_; lean_object* v___x_145_; 
lean_dec(v_h__1_138_);
v_one_143_ = lean_unsigned_to_nat(1u);
v_n_144_ = lean_nat_sub(v_x_136_, v_one_143_);
v___x_145_ = lean_apply_2(v_h__2_139_, v_n_144_, lean_box(0));
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_146_, lean_object* v_xs_147_, lean_object* v_motive_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_146_, v_xs_147_, v_motive_148_, v_x_149_, v_x_150_, v_h__1_151_, v_h__2_152_);
lean_dec(v_x_149_);
lean_dec_ref(v_xs_147_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_){
_start:
{
if (lean_obj_tag(v_____do__lift_154_) == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_h__1_155_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_apply_1(v_h__2_156_, v___x_157_);
return v___x_158_;
}
else
{
lean_object* v_val_159_; lean_object* v___x_160_; 
lean_dec(v_h__2_156_);
v_val_159_ = lean_ctor_get(v_____do__lift_154_, 0);
lean_inc(v_val_159_);
lean_dec_ref_known(v_____do__lift_154_, 1);
v___x_160_ = lean_apply_1(v_h__1_155_, v_val_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter(lean_object* v_00_u03b2_161_, lean_object* v_motive_162_, lean_object* v_____do__lift_163_, lean_object* v_h__1_164_, lean_object* v_h__2_165_){
_start:
{
if (lean_obj_tag(v_____do__lift_163_) == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_h__1_164_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_1(v_h__2_165_, v___x_166_);
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v___x_169_; 
lean_dec(v_h__2_165_);
v_val_168_ = lean_ctor_get(v_____do__lift_163_, 0);
lean_inc(v_val_168_);
lean_dec_ref_known(v_____do__lift_163_, 1);
v___x_169_ = lean_apply_1(v_h__1_164_, v_val_168_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_h__2_172_);
v___x_173_ = lean_box(0);
v___x_174_ = lean_apply_1(v_h__1_171_, v___x_173_);
return v___x_174_;
}
else
{
lean_object* v_val_175_; lean_object* v___x_176_; 
lean_dec(v_h__1_171_);
v_val_175_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v_x_170_, 1);
v___x_176_ = lean_apply_1(v_h__2_172_, v_val_175_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_177_, lean_object* v_motive_178_, lean_object* v_x_179_, lean_object* v_h__1_180_, lean_object* v_h__2_181_){
_start:
{
if (lean_obj_tag(v_x_179_) == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v_h__2_181_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_apply_1(v_h__1_180_, v___x_182_);
return v___x_183_;
}
else
{
lean_object* v_val_184_; lean_object* v___x_185_; 
lean_dec(v_h__1_180_);
v_val_184_ = lean_ctor_get(v_x_179_, 0);
lean_inc(v_val_184_);
lean_dec_ref_known(v_x_179_, 1);
v___x_185_ = lean_apply_1(v_h__2_181_, v_val_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter___redArg(lean_object* v_x_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_){
_start:
{
if (lean_obj_tag(v_x_186_) == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v_h__2_188_);
v___x_189_ = lean_box(0);
v___x_190_ = lean_apply_1(v_h__1_187_, v___x_189_);
return v___x_190_;
}
else
{
lean_object* v_val_191_; lean_object* v___x_192_; 
lean_dec(v_h__1_187_);
v_val_191_ = lean_ctor_get(v_x_186_, 0);
lean_inc(v_val_191_);
lean_dec_ref_known(v_x_186_, 1);
v___x_192_ = lean_apply_1(v_h__2_188_, v_val_191_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter(lean_object* v_00_u03b2_193_, lean_object* v_motive_194_, lean_object* v_x_195_, lean_object* v_h__1_196_, lean_object* v_h__2_197_){
_start:
{
if (lean_obj_tag(v_x_195_) == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v_h__2_197_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_apply_1(v_h__1_196_, v___x_198_);
return v___x_199_;
}
else
{
lean_object* v_val_200_; lean_object* v___x_201_; 
lean_dec(v_h__1_196_);
v_val_200_ = lean_ctor_get(v_x_195_, 0);
lean_inc(v_val_200_);
lean_dec_ref_known(v_x_195_, 1);
v___x_201_ = lean_apply_1(v_h__2_197_, v_val_200_);
return v___x_201_;
}
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__12(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__10));
v___x_229_ = l_Lean_mkAtom(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__13(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__12, &l_Array_filterMap__replicate___auto__7___closed__12_once, _init_l_Array_filterMap__replicate___auto__7___closed__12);
v___x_231_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_232_ = lean_array_push(v___x_231_, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__17(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_244_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_245_ = lean_array_push(v___x_244_, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__18(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__17, &l_Array_filterMap__replicate___auto__7___closed__17_once, _init_l_Array_filterMap__replicate___auto__7___closed__17);
v___x_247_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__15));
v___x_248_ = lean_box(2);
v___x_249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
lean_ctor_set(v___x_249_, 2, v___x_246_);
return v___x_249_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__19(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__18, &l_Array_filterMap__replicate___auto__7___closed__18_once, _init_l_Array_filterMap__replicate___auto__7___closed__18);
v___x_251_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__13, &l_Array_filterMap__replicate___auto__7___closed__13_once, _init_l_Array_filterMap__replicate___auto__7___closed__13);
v___x_252_ = lean_array_push(v___x_251_, v___x_250_);
return v___x_252_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__20(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_254_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__19, &l_Array_filterMap__replicate___auto__7___closed__19_once, _init_l_Array_filterMap__replicate___auto__7___closed__19);
v___x_255_ = lean_array_push(v___x_254_, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__21(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_257_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__20, &l_Array_filterMap__replicate___auto__7___closed__20_once, _init_l_Array_filterMap__replicate___auto__7___closed__20);
v___x_258_ = lean_array_push(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__22(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_260_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__21, &l_Array_filterMap__replicate___auto__7___closed__21_once, _init_l_Array_filterMap__replicate___auto__7___closed__21);
v___x_261_ = lean_array_push(v___x_260_, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__23(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_263_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__22, &l_Array_filterMap__replicate___auto__7___closed__22_once, _init_l_Array_filterMap__replicate___auto__7___closed__22);
v___x_264_ = lean_array_push(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__24(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__23, &l_Array_filterMap__replicate___auto__7___closed__23_once, _init_l_Array_filterMap__replicate___auto__7___closed__23);
v___x_266_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__11));
v___x_267_ = lean_box(2);
v___x_268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
lean_ctor_set(v___x_268_, 2, v___x_265_);
return v___x_268_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__25(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__24, &l_Array_filterMap__replicate___auto__7___closed__24_once, _init_l_Array_filterMap__replicate___auto__7___closed__24);
v___x_270_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_271_ = lean_array_push(v___x_270_, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__26(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__25, &l_Array_filterMap__replicate___auto__7___closed__25_once, _init_l_Array_filterMap__replicate___auto__7___closed__25);
v___x_273_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__9));
v___x_274_ = lean_box(2);
v___x_275_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___x_273_);
lean_ctor_set(v___x_275_, 2, v___x_272_);
return v___x_275_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__27(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__26, &l_Array_filterMap__replicate___auto__7___closed__26_once, _init_l_Array_filterMap__replicate___auto__7___closed__26);
v___x_277_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_278_ = lean_array_push(v___x_277_, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__28(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_279_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__27, &l_Array_filterMap__replicate___auto__7___closed__27_once, _init_l_Array_filterMap__replicate___auto__7___closed__27);
v___x_280_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__7));
v___x_281_ = lean_box(2);
v___x_282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
lean_ctor_set(v___x_282_, 2, v___x_279_);
return v___x_282_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__29(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__28, &l_Array_filterMap__replicate___auto__7___closed__28_once, _init_l_Array_filterMap__replicate___auto__7___closed__28);
v___x_284_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_285_ = lean_array_push(v___x_284_, v___x_283_);
return v___x_285_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__30(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_286_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__29, &l_Array_filterMap__replicate___auto__7___closed__29_once, _init_l_Array_filterMap__replicate___auto__7___closed__29);
v___x_287_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__4));
v___x_288_ = lean_box(2);
v___x_289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
lean_ctor_set(v___x_289_, 2, v___x_286_);
return v___x_289_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__30, &l_Array_filterMap__replicate___auto__7___closed__30_once, _init_l_Array_filterMap__replicate___auto__7___closed__30);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object* v_x_291_, lean_object* v_h__1_292_, lean_object* v_h__2_293_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec(v_h__2_293_);
v___x_294_ = lean_box(0);
v___x_295_ = lean_apply_1(v_h__1_292_, v___x_294_);
return v___x_295_;
}
else
{
lean_object* v_val_296_; lean_object* v___x_297_; 
lean_dec(v_h__1_292_);
v_val_296_ = lean_ctor_get(v_x_291_, 0);
lean_inc(v_val_296_);
lean_dec_ref_known(v_x_291_, 1);
v___x_297_ = lean_apply_1(v_h__2_293_, v_val_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object* v_00_u03b2_298_, lean_object* v_motive_299_, lean_object* v_x_300_, lean_object* v_h__1_301_, lean_object* v_h__2_302_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v_h__2_302_);
v___x_303_ = lean_box(0);
v___x_304_ = lean_apply_1(v_h__1_301_, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v_val_305_; lean_object* v___x_306_; 
lean_dec(v_h__1_301_);
v_val_305_ = lean_ctor_get(v_x_300_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v_x_300_, 1);
v___x_306_ = lean_apply_1(v_h__2_302_, v_val_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(lean_object* v_i_307_, lean_object* v_h__1_308_, lean_object* v_h__2_309_){
_start:
{
lean_object* v_zero_310_; uint8_t v_isZero_311_; 
v_zero_310_ = lean_unsigned_to_nat(0u);
v_isZero_311_ = lean_nat_dec_eq(v_i_307_, v_zero_310_);
if (v_isZero_311_ == 1)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v_h__2_309_);
v___x_312_ = lean_box(0);
v___x_313_ = lean_apply_1(v_h__1_308_, v___x_312_);
return v___x_313_;
}
else
{
lean_object* v_one_314_; lean_object* v_n_315_; lean_object* v___x_316_; 
lean_dec(v_h__1_308_);
v_one_314_ = lean_unsigned_to_nat(1u);
v_n_315_ = lean_nat_sub(v_i_307_, v_one_314_);
v___x_316_ = lean_apply_1(v_h__2_309_, v_n_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg___boxed(lean_object* v_i_317_, lean_object* v_h__1_318_, lean_object* v_h__2_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(v_i_317_, v_h__1_318_, v_h__2_319_);
lean_dec(v_i_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(lean_object* v_motive_321_, lean_object* v_i_322_, lean_object* v_h__1_323_, lean_object* v_h__2_324_){
_start:
{
lean_object* v_zero_325_; uint8_t v_isZero_326_; 
v_zero_325_ = lean_unsigned_to_nat(0u);
v_isZero_326_ = lean_nat_dec_eq(v_i_322_, v_zero_325_);
if (v_isZero_326_ == 1)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_h__2_324_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_apply_1(v_h__1_323_, v___x_327_);
return v___x_328_;
}
else
{
lean_object* v_one_329_; lean_object* v_n_330_; lean_object* v___x_331_; 
lean_dec(v_h__1_323_);
v_one_329_ = lean_unsigned_to_nat(1u);
v_n_330_ = lean_nat_sub(v_i_322_, v_one_329_);
v___x_331_ = lean_apply_1(v_h__2_324_, v_n_330_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___boxed(lean_object* v_motive_332_, lean_object* v_i_333_, lean_object* v_h__1_334_, lean_object* v_h__2_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(v_motive_332_, v_i_333_, v_h__1_334_, v_h__2_335_);
lean_dec(v_i_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_h__1_339_, lean_object* v_h__2_340_){
_start:
{
lean_object* v_zero_341_; uint8_t v_isZero_342_; 
v_zero_341_ = lean_unsigned_to_nat(0u);
v_isZero_342_ = lean_nat_dec_eq(v_x_337_, v_zero_341_);
if (v_isZero_342_ == 1)
{
lean_object* v___x_343_; 
lean_dec(v_h__2_340_);
v___x_343_ = lean_apply_1(v_h__1_339_, v_x_338_);
return v___x_343_;
}
else
{
lean_object* v_one_344_; lean_object* v_n_345_; lean_object* v___x_346_; 
lean_dec(v_h__1_339_);
v_one_344_ = lean_unsigned_to_nat(1u);
v_n_345_ = lean_nat_sub(v_x_337_, v_one_344_);
v___x_346_ = lean_apply_2(v_h__2_340_, v_n_345_, v_x_338_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg___boxed(lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_h__1_349_, lean_object* v_h__2_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(v_x_347_, v_x_348_, v_h__1_349_, v_h__2_350_);
lean_dec(v_x_347_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter(lean_object* v_00_u03b1_352_, lean_object* v_motive_353_, lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_h__1_356_, lean_object* v_h__2_357_){
_start:
{
lean_object* v_zero_358_; uint8_t v_isZero_359_; 
v_zero_358_ = lean_unsigned_to_nat(0u);
v_isZero_359_ = lean_nat_dec_eq(v_x_354_, v_zero_358_);
if (v_isZero_359_ == 1)
{
lean_object* v___x_360_; 
lean_dec(v_h__2_357_);
v___x_360_ = lean_apply_1(v_h__1_356_, v_x_355_);
return v___x_360_;
}
else
{
lean_object* v_one_361_; lean_object* v_n_362_; lean_object* v___x_363_; 
lean_dec(v_h__1_356_);
v_one_361_ = lean_unsigned_to_nat(1u);
v_n_362_ = lean_nat_sub(v_x_354_, v_one_361_);
v___x_363_ = lean_apply_2(v_h__2_357_, v_n_362_, v_x_355_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___boxed(lean_object* v_00_u03b1_364_, lean_object* v_motive_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter(v_00_u03b1_364_, v_motive_365_, v_x_366_, v_x_367_, v_h__1_368_, v_h__2_369_);
lean_dec(v_x_366_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object* v_i_371_, lean_object* v_h__1_372_, lean_object* v_h__2_373_){
_start:
{
lean_object* v_zero_374_; uint8_t v_isZero_375_; 
v_zero_374_ = lean_unsigned_to_nat(0u);
v_isZero_375_ = lean_nat_dec_eq(v_i_371_, v_zero_374_);
if (v_isZero_375_ == 1)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_h__2_373_);
v___x_376_ = lean_box(0);
v___x_377_ = lean_apply_1(v_h__1_372_, v___x_376_);
return v___x_377_;
}
else
{
lean_object* v_one_378_; lean_object* v_n_379_; lean_object* v___x_380_; 
lean_dec(v_h__1_372_);
v_one_378_ = lean_unsigned_to_nat(1u);
v_n_379_ = lean_nat_sub(v_i_371_, v_one_378_);
v___x_380_ = lean_apply_1(v_h__2_373_, v_n_379_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object* v_i_381_, lean_object* v_h__1_382_, lean_object* v_h__2_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_381_, v_h__1_382_, v_h__2_383_);
lean_dec(v_i_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object* v_motive_385_, lean_object* v_i_386_, lean_object* v_h__1_387_, lean_object* v_h__2_388_){
_start:
{
lean_object* v_zero_389_; uint8_t v_isZero_390_; 
v_zero_389_ = lean_unsigned_to_nat(0u);
v_isZero_390_ = lean_nat_dec_eq(v_i_386_, v_zero_389_);
if (v_isZero_390_ == 1)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v_h__2_388_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_apply_1(v_h__1_387_, v___x_391_);
return v___x_392_;
}
else
{
lean_object* v_one_393_; lean_object* v_n_394_; lean_object* v___x_395_; 
lean_dec(v_h__1_387_);
v_one_393_ = lean_unsigned_to_nat(1u);
v_n_394_ = lean_nat_sub(v_i_386_, v_one_393_);
v___x_395_ = lean_apply_1(v_h__2_388_, v_n_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object* v_motive_396_, lean_object* v_i_397_, lean_object* v_h__1_398_, lean_object* v_h__2_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(v_motive_396_, v_i_397_, v_h__1_398_, v_h__2_399_);
lean_dec(v_i_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object* v_i_401_, lean_object* v_h__1_402_, lean_object* v_h__2_403_){
_start:
{
lean_object* v_zero_404_; uint8_t v_isZero_405_; 
v_zero_404_ = lean_unsigned_to_nat(0u);
v_isZero_405_ = lean_nat_dec_eq(v_i_401_, v_zero_404_);
if (v_isZero_405_ == 1)
{
lean_object* v___x_406_; 
lean_dec(v_h__2_403_);
v___x_406_ = lean_apply_1(v_h__1_402_, lean_box(0));
return v___x_406_;
}
else
{
lean_object* v_one_407_; lean_object* v_n_408_; lean_object* v___x_409_; 
lean_dec(v_h__1_402_);
v_one_407_ = lean_unsigned_to_nat(1u);
v_n_408_ = lean_nat_sub(v_i_401_, v_one_407_);
v___x_409_ = lean_apply_2(v_h__2_403_, v_n_408_, lean_box(0));
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object* v_i_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(v_i_410_, v_h__1_411_, v_h__2_412_);
lean_dec(v_i_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(lean_object* v_00_u03b1_414_, lean_object* v_as_415_, lean_object* v_motive_416_, lean_object* v_i_417_, lean_object* v_h_418_, lean_object* v_h__1_419_, lean_object* v_h__2_420_){
_start:
{
lean_object* v_zero_421_; uint8_t v_isZero_422_; 
v_zero_421_ = lean_unsigned_to_nat(0u);
v_isZero_422_ = lean_nat_dec_eq(v_i_417_, v_zero_421_);
if (v_isZero_422_ == 1)
{
lean_object* v___x_423_; 
lean_dec(v_h__2_420_);
v___x_423_ = lean_apply_1(v_h__1_419_, lean_box(0));
return v___x_423_;
}
else
{
lean_object* v_one_424_; lean_object* v_n_425_; lean_object* v___x_426_; 
lean_dec(v_h__1_419_);
v_one_424_ = lean_unsigned_to_nat(1u);
v_n_425_ = lean_nat_sub(v_i_417_, v_one_424_);
v___x_426_ = lean_apply_2(v_h__2_420_, v_n_425_, lean_box(0));
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_427_, lean_object* v_as_428_, lean_object* v_motive_429_, lean_object* v_i_430_, lean_object* v_h_431_, lean_object* v_h__1_432_, lean_object* v_h__2_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(v_00_u03b1_427_, v_as_428_, v_motive_429_, v_i_430_, v_h_431_, v_h__1_432_, v_h__2_433_);
lean_dec(v_i_430_);
lean_dec_ref(v_as_428_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object* v_x_435_, lean_object* v_h__1_436_, lean_object* v_h__2_437_){
_start:
{
if (lean_obj_tag(v_x_435_) == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v_h__1_436_);
v___x_438_ = lean_box(0);
v___x_439_ = lean_apply_1(v_h__2_437_, v___x_438_);
return v___x_439_;
}
else
{
lean_object* v_val_440_; lean_object* v___x_441_; 
lean_dec(v_h__2_437_);
v_val_440_ = lean_ctor_get(v_x_435_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v_x_435_, 1);
v___x_441_ = lean_apply_1(v_h__1_436_, v_val_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object* v_00_u03b2_442_, lean_object* v_motive_443_, lean_object* v_x_444_, lean_object* v_h__1_445_, lean_object* v_h__2_446_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v_h__1_445_);
v___x_447_ = lean_box(0);
v___x_448_ = lean_apply_1(v_h__2_446_, v___x_447_);
return v___x_448_;
}
else
{
lean_object* v_val_449_; lean_object* v___x_450_; 
lean_dec(v_h__2_446_);
v_val_449_ = lean_ctor_get(v_x_444_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v_x_444_, 1);
v___x_450_ = lean_apply_1(v_h__1_445_, v_val_449_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter___redArg(lean_object* v_x_451_, lean_object* v_h__1_452_, lean_object* v_h__2_453_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_h__1_452_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_apply_1(v_h__2_453_, v___x_454_);
return v___x_455_;
}
else
{
lean_object* v_val_456_; lean_object* v___x_457_; 
lean_dec(v_h__2_453_);
v_val_456_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_val_456_);
lean_dec_ref_known(v_x_451_, 1);
v___x_457_ = lean_apply_1(v_h__1_452_, v_val_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter(lean_object* v_00_u03b2_458_, lean_object* v_motive_459_, lean_object* v_x_460_, lean_object* v_h__1_461_, lean_object* v_h__2_462_){
_start:
{
if (lean_obj_tag(v_x_460_) == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v_h__1_461_);
v___x_463_ = lean_box(0);
v___x_464_ = lean_apply_1(v_h__2_462_, v___x_463_);
return v___x_464_;
}
else
{
lean_object* v_val_465_; lean_object* v___x_466_; 
lean_dec(v_h__2_462_);
v_val_465_ = lean_ctor_get(v_x_460_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v_x_460_, 1);
v___x_466_ = lean_apply_1(v_h__1_461_, v_val_465_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___redArg(lean_object* v_x_467_, lean_object* v_h__1_468_, lean_object* v_h__2_469_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec(v_h__2_469_);
v___x_470_ = lean_box(0);
v___x_471_ = lean_apply_1(v_h__1_468_, v___x_470_);
return v___x_471_;
}
else
{
lean_object* v_val_472_; lean_object* v___x_473_; 
lean_dec(v_h__1_468_);
v_val_472_ = lean_ctor_get(v_x_467_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v_x_467_, 1);
v___x_473_ = lean_apply_1(v_h__2_469_, v_val_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(lean_object* v_00_u03b1_474_, lean_object* v_as_475_, lean_object* v_motive_476_, lean_object* v_x_477_, lean_object* v_h__1_478_, lean_object* v_h__2_479_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_h__2_479_);
v___x_480_ = lean_box(0);
v___x_481_ = lean_apply_1(v_h__1_478_, v___x_480_);
return v___x_481_;
}
else
{
lean_object* v_val_482_; lean_object* v___x_483_; 
lean_dec(v_h__1_478_);
v_val_482_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v_x_477_, 1);
v___x_483_ = lean_apply_1(v_h__2_479_, v_val_482_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_484_, lean_object* v_as_485_, lean_object* v_motive_486_, lean_object* v_x_487_, lean_object* v_h__1_488_, lean_object* v_h__2_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(v_00_u03b1_484_, v_as_485_, v_motive_486_, v_x_487_, v_h__1_488_, v_h__2_489_);
lean_dec_ref(v_as_485_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg___lam__0(lean_object* v_x1_491_, lean_object* v_x2_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_493_, 0, v_x2_492_);
lean_ctor_set(v___x_493_, 1, v_x1_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg(lean_object* v_xs_514_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_515_ = lean_box(0);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_array_get_size(v_xs_514_);
v___x_518_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_519_ = lean_nat_dec_lt(v___x_516_, v___x_517_);
if (v___x_519_ == 0)
{
lean_dec_ref(v_xs_514_);
return v___x_515_;
}
else
{
lean_object* v___f_520_; uint8_t v___x_521_; 
v___f_520_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_521_ = lean_nat_dec_le(v___x_517_, v___x_517_);
if (v___x_521_ == 0)
{
if (v___x_519_ == 0)
{
lean_dec_ref(v_xs_514_);
return v___x_515_;
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((size_t)0ULL);
v___x_523_ = lean_usize_of_nat(v___x_517_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_518_, v___f_520_, v_xs_514_, v___x_522_, v___x_523_, v___x_515_);
return v___x_524_;
}
}
else
{
size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((size_t)0ULL);
v___x_526_ = lean_usize_of_nat(v___x_517_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_518_, v___f_520_, v_xs_514_, v___x_525_, v___x_526_, v___x_515_);
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toListRev(lean_object* v_00_u03b1_528_, lean_object* v_xs_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_530_ = lean_box(0);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_array_get_size(v_xs_529_);
v___x_533_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_534_ = lean_nat_dec_lt(v___x_531_, v___x_532_);
if (v___x_534_ == 0)
{
lean_dec_ref(v_xs_529_);
return v___x_530_;
}
else
{
lean_object* v___f_535_; uint8_t v___x_536_; 
v___f_535_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_536_ = lean_nat_dec_le(v___x_532_, v___x_532_);
if (v___x_536_ == 0)
{
if (v___x_534_ == 0)
{
lean_dec_ref(v_xs_529_);
return v___x_530_;
}
else
{
size_t v___x_537_; size_t v___x_538_; lean_object* v___x_539_; 
v___x_537_ = ((size_t)0ULL);
v___x_538_ = lean_usize_of_nat(v___x_532_);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_533_, v___f_535_, v_xs_529_, v___x_537_, v___x_538_, v___x_530_);
return v___x_539_;
}
}
else
{
size_t v___x_540_; size_t v___x_541_; lean_object* v___x_542_; 
v___x_540_ = ((size_t)0ULL);
v___x_541_ = lean_usize_of_nat(v___x_532_);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_533_, v___f_535_, v_xs_529_, v___x_540_, v___x_541_, v___x_530_);
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(lean_object* v_x_543_, lean_object* v_h__1_544_, lean_object* v_h__2_545_){
_start:
{
lean_object* v_zero_546_; uint8_t v_isZero_547_; 
v_zero_546_ = lean_unsigned_to_nat(0u);
v_isZero_547_ = lean_nat_dec_eq(v_x_543_, v_zero_546_);
if (v_isZero_547_ == 1)
{
lean_object* v___x_548_; 
lean_dec(v_h__1_544_);
v___x_548_ = lean_apply_1(v_h__2_545_, lean_box(0));
return v___x_548_;
}
else
{
lean_object* v_one_549_; lean_object* v_n_550_; lean_object* v___x_551_; 
lean_dec(v_h__2_545_);
v_one_549_ = lean_unsigned_to_nat(1u);
v_n_550_ = lean_nat_sub(v_x_543_, v_one_549_);
v___x_551_ = lean_apply_2(v_h__1_544_, v_n_550_, lean_box(0));
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg___boxed(lean_object* v_x_552_, lean_object* v_h__1_553_, lean_object* v_h__2_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(v_x_552_, v_h__1_553_, v_h__2_554_);
lean_dec(v_x_552_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(lean_object* v_n_556_, lean_object* v_motive_557_, lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_h__1_560_, lean_object* v_h__2_561_){
_start:
{
lean_object* v_zero_562_; uint8_t v_isZero_563_; 
v_zero_562_ = lean_unsigned_to_nat(0u);
v_isZero_563_ = lean_nat_dec_eq(v_x_558_, v_zero_562_);
if (v_isZero_563_ == 1)
{
lean_object* v___x_564_; 
lean_dec(v_h__1_560_);
v___x_564_ = lean_apply_1(v_h__2_561_, lean_box(0));
return v___x_564_;
}
else
{
lean_object* v_one_565_; lean_object* v_n_566_; lean_object* v___x_567_; 
lean_dec(v_h__2_561_);
v_one_565_ = lean_unsigned_to_nat(1u);
v_n_566_ = lean_nat_sub(v_x_558_, v_one_565_);
v___x_567_ = lean_apply_2(v_h__1_560_, v_n_566_, lean_box(0));
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___boxed(lean_object* v_n_568_, lean_object* v_motive_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_h__1_572_, lean_object* v_h__2_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(v_n_568_, v_motive_569_, v_x_570_, v_x_571_, v_h__1_572_, v_h__2_573_);
lean_dec(v_x_570_);
lean_dec(v_n_568_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_575_, lean_object* v_h__1_576_, lean_object* v_h__2_577_){
_start:
{
if (lean_obj_tag(v_opt_575_) == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_h__1_576_);
v___x_578_ = lean_box(0);
v___x_579_ = lean_apply_1(v_h__2_577_, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v_val_580_; lean_object* v___x_581_; 
lean_dec(v_h__2_577_);
v_val_580_ = lean_ctor_get(v_opt_575_, 0);
lean_inc(v_val_580_);
lean_dec_ref_known(v_opt_575_, 1);
v___x_581_ = lean_apply_1(v_h__1_576_, v_val_580_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_582_, lean_object* v_motive_583_, lean_object* v_opt_584_, lean_object* v_h__1_585_, lean_object* v_h__2_586_){
_start:
{
if (lean_obj_tag(v_opt_584_) == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_h__1_585_);
v___x_587_ = lean_box(0);
v___x_588_ = lean_apply_1(v_h__2_586_, v___x_587_);
return v___x_588_;
}
else
{
lean_object* v_val_589_; lean_object* v___x_590_; 
lean_dec(v_h__2_586_);
v_val_589_ = lean_ctor_get(v_opt_584_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v_opt_584_, 1);
v___x_590_ = lean_apply_1(v_h__1_585_, v_val_589_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_591_, lean_object* v_h__1_592_, lean_object* v_h__2_593_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v_h__1_592_);
v___x_594_ = lean_box(0);
v___x_595_ = lean_apply_1(v_h__2_593_, v___x_594_);
return v___x_595_;
}
else
{
lean_object* v_val_596_; lean_object* v___x_597_; 
lean_dec(v_h__2_593_);
v_val_596_ = lean_ctor_get(v_x_591_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v_x_591_, 1);
v___x_597_ = lean_apply_1(v_h__1_592_, v_val_596_);
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_598_, lean_object* v_motive_599_, lean_object* v_x_600_, lean_object* v_h__1_601_, lean_object* v_h__2_602_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v_h__1_601_);
v___x_603_ = lean_box(0);
v___x_604_ = lean_apply_1(v_h__2_602_, v___x_603_);
return v___x_604_;
}
else
{
lean_object* v_val_605_; lean_object* v___x_606_; 
lean_dec(v_h__2_602_);
v_val_605_ = lean_ctor_get(v_x_600_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v_x_600_, 1);
v___x_606_ = lean_apply_1(v_h__1_601_, v_val_605_);
return v___x_606_;
}
}
}
lean_object* runtime_initialize_Init_Data_List_ToArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Array_filterMap__replicate___auto__7 = _init_l_Array_filterMap__replicate___auto__7();
lean_mark_persistent(l_Array_filterMap__replicate___auto__7);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_ToArray(uint8_t builtin);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
