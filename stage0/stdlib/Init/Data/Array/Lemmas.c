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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_){
_start:
{
if (lean_obj_tag(v_____do__lift_120_) == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v_h__1_121_);
v___x_123_ = lean_box(0);
v___x_124_ = lean_apply_1(v_h__2_122_, v___x_123_);
return v___x_124_;
}
else
{
lean_object* v_val_125_; lean_object* v___x_126_; 
lean_dec(v_h__2_122_);
v_val_125_ = lean_ctor_get(v_____do__lift_120_, 0);
lean_inc(v_val_125_);
lean_dec_ref_known(v_____do__lift_120_, 1);
v___x_126_ = lean_apply_1(v_h__1_121_, v_val_125_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter(lean_object* v_00_u03b2_127_, lean_object* v_motive_128_, lean_object* v_____do__lift_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_){
_start:
{
if (lean_obj_tag(v_____do__lift_129_) == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__1_130_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__2_131_, v___x_132_);
return v___x_133_;
}
else
{
lean_object* v_val_134_; lean_object* v___x_135_; 
lean_dec(v_h__2_131_);
v_val_134_ = lean_ctor_get(v_____do__lift_129_, 0);
lean_inc(v_val_134_);
lean_dec_ref_known(v_____do__lift_129_, 1);
v___x_135_ = lean_apply_1(v_h__1_130_, v_val_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec(v_h__2_138_);
v___x_139_ = lean_box(0);
v___x_140_ = lean_apply_1(v_h__1_137_, v___x_139_);
return v___x_140_;
}
else
{
lean_object* v_val_141_; lean_object* v___x_142_; 
lean_dec(v_h__1_137_);
v_val_141_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_val_141_);
lean_dec_ref_known(v_x_136_, 1);
v___x_142_ = lean_apply_1(v_h__2_138_, v_val_141_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_143_, lean_object* v_motive_144_, lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_h__2_147_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_apply_1(v_h__1_146_, v___x_148_);
return v___x_149_;
}
else
{
lean_object* v_val_150_; lean_object* v___x_151_; 
lean_dec(v_h__1_146_);
v_val_150_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_val_150_);
lean_dec_ref_known(v_x_145_, 1);
v___x_151_ = lean_apply_1(v_h__2_147_, v_val_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter___redArg(lean_object* v_x_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_h__2_154_);
v___x_155_ = lean_box(0);
v___x_156_ = lean_apply_1(v_h__1_153_, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v_val_157_; lean_object* v___x_158_; 
lean_dec(v_h__1_153_);
v_val_157_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_val_157_);
lean_dec_ref_known(v_x_152_, 1);
v___x_158_ = lean_apply_1(v_h__2_154_, v_val_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter(lean_object* v_00_u03b2_159_, lean_object* v_motive_160_, lean_object* v_x_161_, lean_object* v_h__1_162_, lean_object* v_h__2_163_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_h__2_163_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_apply_1(v_h__1_162_, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v_val_166_; lean_object* v___x_167_; 
lean_dec(v_h__1_162_);
v_val_166_ = lean_ctor_get(v_x_161_, 0);
lean_inc(v_val_166_);
lean_dec_ref_known(v_x_161_, 1);
v___x_167_ = lean_apply_1(v_h__2_163_, v_val_166_);
return v___x_167_;
}
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__12(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__10));
v___x_195_ = l_Lean_mkAtom(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__13(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__12, &l_Array_filterMap__replicate___auto__7___closed__12_once, _init_l_Array_filterMap__replicate___auto__7___closed__12);
v___x_197_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_198_ = lean_array_push(v___x_197_, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__17(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_210_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_211_ = lean_array_push(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__18(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_212_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__17, &l_Array_filterMap__replicate___auto__7___closed__17_once, _init_l_Array_filterMap__replicate___auto__7___closed__17);
v___x_213_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__15));
v___x_214_ = lean_box(2);
v___x_215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
lean_ctor_set(v___x_215_, 2, v___x_212_);
return v___x_215_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__19(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__18, &l_Array_filterMap__replicate___auto__7___closed__18_once, _init_l_Array_filterMap__replicate___auto__7___closed__18);
v___x_217_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__13, &l_Array_filterMap__replicate___auto__7___closed__13_once, _init_l_Array_filterMap__replicate___auto__7___closed__13);
v___x_218_ = lean_array_push(v___x_217_, v___x_216_);
return v___x_218_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__20(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_220_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__19, &l_Array_filterMap__replicate___auto__7___closed__19_once, _init_l_Array_filterMap__replicate___auto__7___closed__19);
v___x_221_ = lean_array_push(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__21(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_223_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__20, &l_Array_filterMap__replicate___auto__7___closed__20_once, _init_l_Array_filterMap__replicate___auto__7___closed__20);
v___x_224_ = lean_array_push(v___x_223_, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__22(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_226_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__21, &l_Array_filterMap__replicate___auto__7___closed__21_once, _init_l_Array_filterMap__replicate___auto__7___closed__21);
v___x_227_ = lean_array_push(v___x_226_, v___x_225_);
return v___x_227_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__23(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_229_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__22, &l_Array_filterMap__replicate___auto__7___closed__22_once, _init_l_Array_filterMap__replicate___auto__7___closed__22);
v___x_230_ = lean_array_push(v___x_229_, v___x_228_);
return v___x_230_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__24(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_231_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__23, &l_Array_filterMap__replicate___auto__7___closed__23_once, _init_l_Array_filterMap__replicate___auto__7___closed__23);
v___x_232_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__11));
v___x_233_ = lean_box(2);
v___x_234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
lean_ctor_set(v___x_234_, 2, v___x_231_);
return v___x_234_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__25(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__24, &l_Array_filterMap__replicate___auto__7___closed__24_once, _init_l_Array_filterMap__replicate___auto__7___closed__24);
v___x_236_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_237_ = lean_array_push(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__26(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_238_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__25, &l_Array_filterMap__replicate___auto__7___closed__25_once, _init_l_Array_filterMap__replicate___auto__7___closed__25);
v___x_239_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__9));
v___x_240_ = lean_box(2);
v___x_241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_238_);
return v___x_241_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__27(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__26, &l_Array_filterMap__replicate___auto__7___closed__26_once, _init_l_Array_filterMap__replicate___auto__7___closed__26);
v___x_243_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_244_ = lean_array_push(v___x_243_, v___x_242_);
return v___x_244_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__28(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_245_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__27, &l_Array_filterMap__replicate___auto__7___closed__27_once, _init_l_Array_filterMap__replicate___auto__7___closed__27);
v___x_246_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__7));
v___x_247_ = lean_box(2);
v___x_248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_246_);
lean_ctor_set(v___x_248_, 2, v___x_245_);
return v___x_248_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__29(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__28, &l_Array_filterMap__replicate___auto__7___closed__28_once, _init_l_Array_filterMap__replicate___auto__7___closed__28);
v___x_250_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_251_ = lean_array_push(v___x_250_, v___x_249_);
return v___x_251_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__30(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_252_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__29, &l_Array_filterMap__replicate___auto__7___closed__29_once, _init_l_Array_filterMap__replicate___auto__7___closed__29);
v___x_253_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__4));
v___x_254_ = lean_box(2);
v___x_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
lean_ctor_set(v___x_255_, 2, v___x_252_);
return v___x_255_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__30, &l_Array_filterMap__replicate___auto__7___closed__30_once, _init_l_Array_filterMap__replicate___auto__7___closed__30);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object* v_x_257_, lean_object* v_h__1_258_, lean_object* v_h__2_259_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_h__2_259_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_apply_1(v_h__1_258_, v___x_260_);
return v___x_261_;
}
else
{
lean_object* v_val_262_; lean_object* v___x_263_; 
lean_dec(v_h__1_258_);
v_val_262_ = lean_ctor_get(v_x_257_, 0);
lean_inc(v_val_262_);
lean_dec_ref_known(v_x_257_, 1);
v___x_263_ = lean_apply_1(v_h__2_259_, v_val_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object* v_00_u03b2_264_, lean_object* v_motive_265_, lean_object* v_x_266_, lean_object* v_h__1_267_, lean_object* v_h__2_268_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v_h__2_268_);
v___x_269_ = lean_box(0);
v___x_270_ = lean_apply_1(v_h__1_267_, v___x_269_);
return v___x_270_;
}
else
{
lean_object* v_val_271_; lean_object* v___x_272_; 
lean_dec(v_h__1_267_);
v_val_271_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_val_271_);
lean_dec_ref_known(v_x_266_, 1);
v___x_272_ = lean_apply_1(v_h__2_268_, v_val_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(lean_object* v_i_273_, lean_object* v_h__1_274_, lean_object* v_h__2_275_){
_start:
{
lean_object* v_zero_276_; uint8_t v_isZero_277_; 
v_zero_276_ = lean_unsigned_to_nat(0u);
v_isZero_277_ = lean_nat_dec_eq(v_i_273_, v_zero_276_);
if (v_isZero_277_ == 1)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_h__2_275_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_apply_1(v_h__1_274_, v___x_278_);
return v___x_279_;
}
else
{
lean_object* v_one_280_; lean_object* v_n_281_; lean_object* v___x_282_; 
lean_dec(v_h__1_274_);
v_one_280_ = lean_unsigned_to_nat(1u);
v_n_281_ = lean_nat_sub(v_i_273_, v_one_280_);
v___x_282_ = lean_apply_1(v_h__2_275_, v_n_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg___boxed(lean_object* v_i_283_, lean_object* v_h__1_284_, lean_object* v_h__2_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(v_i_283_, v_h__1_284_, v_h__2_285_);
lean_dec(v_i_283_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(lean_object* v_motive_287_, lean_object* v_i_288_, lean_object* v_h__1_289_, lean_object* v_h__2_290_){
_start:
{
lean_object* v_zero_291_; uint8_t v_isZero_292_; 
v_zero_291_ = lean_unsigned_to_nat(0u);
v_isZero_292_ = lean_nat_dec_eq(v_i_288_, v_zero_291_);
if (v_isZero_292_ == 1)
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec(v_h__2_290_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_apply_1(v_h__1_289_, v___x_293_);
return v___x_294_;
}
else
{
lean_object* v_one_295_; lean_object* v_n_296_; lean_object* v___x_297_; 
lean_dec(v_h__1_289_);
v_one_295_ = lean_unsigned_to_nat(1u);
v_n_296_ = lean_nat_sub(v_i_288_, v_one_295_);
v___x_297_ = lean_apply_1(v_h__2_290_, v_n_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___boxed(lean_object* v_motive_298_, lean_object* v_i_299_, lean_object* v_h__1_300_, lean_object* v_h__2_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(v_motive_298_, v_i_299_, v_h__1_300_, v_h__2_301_);
lean_dec(v_i_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_){
_start:
{
lean_object* v_zero_307_; uint8_t v_isZero_308_; 
v_zero_307_ = lean_unsigned_to_nat(0u);
v_isZero_308_ = lean_nat_dec_eq(v_x_303_, v_zero_307_);
if (v_isZero_308_ == 1)
{
lean_object* v___x_309_; 
lean_dec(v_h__2_306_);
v___x_309_ = lean_apply_1(v_h__1_305_, v_x_304_);
return v___x_309_;
}
else
{
lean_object* v_one_310_; lean_object* v_n_311_; lean_object* v___x_312_; 
lean_dec(v_h__1_305_);
v_one_310_ = lean_unsigned_to_nat(1u);
v_n_311_ = lean_nat_sub(v_x_303_, v_one_310_);
v___x_312_ = lean_apply_2(v_h__2_306_, v_n_311_, v_x_304_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg___boxed(lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_h__1_315_, lean_object* v_h__2_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(v_x_313_, v_x_314_, v_h__1_315_, v_h__2_316_);
lean_dec(v_x_313_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter(lean_object* v_00_u03b1_318_, lean_object* v_motive_319_, lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_h__1_322_, lean_object* v_h__2_323_){
_start:
{
lean_object* v_zero_324_; uint8_t v_isZero_325_; 
v_zero_324_ = lean_unsigned_to_nat(0u);
v_isZero_325_ = lean_nat_dec_eq(v_x_320_, v_zero_324_);
if (v_isZero_325_ == 1)
{
lean_object* v___x_326_; 
lean_dec(v_h__2_323_);
v___x_326_ = lean_apply_1(v_h__1_322_, v_x_321_);
return v___x_326_;
}
else
{
lean_object* v_one_327_; lean_object* v_n_328_; lean_object* v___x_329_; 
lean_dec(v_h__1_322_);
v_one_327_ = lean_unsigned_to_nat(1u);
v_n_328_ = lean_nat_sub(v_x_320_, v_one_327_);
v___x_329_ = lean_apply_2(v_h__2_323_, v_n_328_, v_x_321_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___boxed(lean_object* v_00_u03b1_330_, lean_object* v_motive_331_, lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_h__1_334_, lean_object* v_h__2_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter(v_00_u03b1_330_, v_motive_331_, v_x_332_, v_x_333_, v_h__1_334_, v_h__2_335_);
lean_dec(v_x_332_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object* v_i_337_, lean_object* v_h__1_338_, lean_object* v_h__2_339_){
_start:
{
lean_object* v_zero_340_; uint8_t v_isZero_341_; 
v_zero_340_ = lean_unsigned_to_nat(0u);
v_isZero_341_ = lean_nat_dec_eq(v_i_337_, v_zero_340_);
if (v_isZero_341_ == 1)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_h__2_339_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_apply_1(v_h__1_338_, v___x_342_);
return v___x_343_;
}
else
{
lean_object* v_one_344_; lean_object* v_n_345_; lean_object* v___x_346_; 
lean_dec(v_h__1_338_);
v_one_344_ = lean_unsigned_to_nat(1u);
v_n_345_ = lean_nat_sub(v_i_337_, v_one_344_);
v___x_346_ = lean_apply_1(v_h__2_339_, v_n_345_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object* v_i_347_, lean_object* v_h__1_348_, lean_object* v_h__2_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_347_, v_h__1_348_, v_h__2_349_);
lean_dec(v_i_347_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object* v_motive_351_, lean_object* v_i_352_, lean_object* v_h__1_353_, lean_object* v_h__2_354_){
_start:
{
lean_object* v_zero_355_; uint8_t v_isZero_356_; 
v_zero_355_ = lean_unsigned_to_nat(0u);
v_isZero_356_ = lean_nat_dec_eq(v_i_352_, v_zero_355_);
if (v_isZero_356_ == 1)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v_h__2_354_);
v___x_357_ = lean_box(0);
v___x_358_ = lean_apply_1(v_h__1_353_, v___x_357_);
return v___x_358_;
}
else
{
lean_object* v_one_359_; lean_object* v_n_360_; lean_object* v___x_361_; 
lean_dec(v_h__1_353_);
v_one_359_ = lean_unsigned_to_nat(1u);
v_n_360_ = lean_nat_sub(v_i_352_, v_one_359_);
v___x_361_ = lean_apply_1(v_h__2_354_, v_n_360_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object* v_motive_362_, lean_object* v_i_363_, lean_object* v_h__1_364_, lean_object* v_h__2_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(v_motive_362_, v_i_363_, v_h__1_364_, v_h__2_365_);
lean_dec(v_i_363_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_){
_start:
{
lean_object* v_zero_370_; uint8_t v_isZero_371_; 
v_zero_370_ = lean_unsigned_to_nat(0u);
v_isZero_371_ = lean_nat_dec_eq(v_x_367_, v_zero_370_);
if (v_isZero_371_ == 1)
{
lean_object* v___x_372_; 
lean_dec(v_h__2_369_);
v___x_372_ = lean_apply_1(v_h__1_368_, lean_box(0));
return v___x_372_;
}
else
{
lean_object* v_one_373_; lean_object* v_n_374_; lean_object* v___x_375_; 
lean_dec(v_h__1_368_);
v_one_373_ = lean_unsigned_to_nat(1u);
v_n_374_ = lean_nat_sub(v_x_367_, v_one_373_);
v___x_375_ = lean_apply_2(v_h__2_369_, v_n_374_, lean_box(0));
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_376_, lean_object* v_h__1_377_, lean_object* v_h__2_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(v_x_376_, v_h__1_377_, v_h__2_378_);
lean_dec(v_x_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_380_, lean_object* v_xs_381_, lean_object* v_motive_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_h__1_385_, lean_object* v_h__2_386_){
_start:
{
lean_object* v_zero_387_; uint8_t v_isZero_388_; 
v_zero_387_ = lean_unsigned_to_nat(0u);
v_isZero_388_ = lean_nat_dec_eq(v_x_383_, v_zero_387_);
if (v_isZero_388_ == 1)
{
lean_object* v___x_389_; 
lean_dec(v_h__2_386_);
v___x_389_ = lean_apply_1(v_h__1_385_, lean_box(0));
return v___x_389_;
}
else
{
lean_object* v_one_390_; lean_object* v_n_391_; lean_object* v___x_392_; 
lean_dec(v_h__1_385_);
v_one_390_ = lean_unsigned_to_nat(1u);
v_n_391_ = lean_nat_sub(v_x_383_, v_one_390_);
v___x_392_ = lean_apply_2(v_h__2_386_, v_n_391_, lean_box(0));
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_393_, lean_object* v_xs_394_, lean_object* v_motive_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_h__1_398_, lean_object* v_h__2_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_393_, v_xs_394_, v_motive_395_, v_x_396_, v_x_397_, v_h__1_398_, v_h__2_399_);
lean_dec(v_x_396_);
lean_dec_ref(v_xs_394_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object* v_x_401_, lean_object* v_h__1_402_, lean_object* v_h__2_403_){
_start:
{
if (lean_obj_tag(v_x_401_) == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_h__1_402_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_apply_1(v_h__2_403_, v___x_404_);
return v___x_405_;
}
else
{
lean_object* v_val_406_; lean_object* v___x_407_; 
lean_dec(v_h__2_403_);
v_val_406_ = lean_ctor_get(v_x_401_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v_x_401_, 1);
v___x_407_ = lean_apply_1(v_h__1_402_, v_val_406_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object* v_00_u03b2_408_, lean_object* v_motive_409_, lean_object* v_x_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec(v_h__1_411_);
v___x_413_ = lean_box(0);
v___x_414_ = lean_apply_1(v_h__2_412_, v___x_413_);
return v___x_414_;
}
else
{
lean_object* v_val_415_; lean_object* v___x_416_; 
lean_dec(v_h__2_412_);
v_val_415_ = lean_ctor_get(v_x_410_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v_x_410_, 1);
v___x_416_ = lean_apply_1(v_h__1_411_, v_val_415_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter___redArg(lean_object* v_x_417_, lean_object* v_h__1_418_, lean_object* v_h__2_419_){
_start:
{
if (lean_obj_tag(v_x_417_) == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_h__1_418_);
v___x_420_ = lean_box(0);
v___x_421_ = lean_apply_1(v_h__2_419_, v___x_420_);
return v___x_421_;
}
else
{
lean_object* v_val_422_; lean_object* v___x_423_; 
lean_dec(v_h__2_419_);
v_val_422_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v_x_417_, 1);
v___x_423_ = lean_apply_1(v_h__1_418_, v_val_422_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter(lean_object* v_00_u03b2_424_, lean_object* v_motive_425_, lean_object* v_x_426_, lean_object* v_h__1_427_, lean_object* v_h__2_428_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_h__1_427_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_apply_1(v_h__2_428_, v___x_429_);
return v___x_430_;
}
else
{
lean_object* v_val_431_; lean_object* v___x_432_; 
lean_dec(v_h__2_428_);
v_val_431_ = lean_ctor_get(v_x_426_, 0);
lean_inc(v_val_431_);
lean_dec_ref_known(v_x_426_, 1);
v___x_432_ = lean_apply_1(v_h__1_427_, v_val_431_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___redArg(lean_object* v_x_433_, lean_object* v_h__1_434_, lean_object* v_h__2_435_){
_start:
{
if (lean_obj_tag(v_x_433_) == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec(v_h__2_435_);
v___x_436_ = lean_box(0);
v___x_437_ = lean_apply_1(v_h__1_434_, v___x_436_);
return v___x_437_;
}
else
{
lean_object* v_val_438_; lean_object* v___x_439_; 
lean_dec(v_h__1_434_);
v_val_438_ = lean_ctor_get(v_x_433_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v_x_433_, 1);
v___x_439_ = lean_apply_1(v_h__2_435_, v_val_438_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(lean_object* v_00_u03b1_440_, lean_object* v_as_441_, lean_object* v_motive_442_, lean_object* v_x_443_, lean_object* v_h__1_444_, lean_object* v_h__2_445_){
_start:
{
if (lean_obj_tag(v_x_443_) == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v_h__2_445_);
v___x_446_ = lean_box(0);
v___x_447_ = lean_apply_1(v_h__1_444_, v___x_446_);
return v___x_447_;
}
else
{
lean_object* v_val_448_; lean_object* v___x_449_; 
lean_dec(v_h__1_444_);
v_val_448_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_val_448_);
lean_dec_ref_known(v_x_443_, 1);
v___x_449_ = lean_apply_1(v_h__2_445_, v_val_448_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_450_, lean_object* v_as_451_, lean_object* v_motive_452_, lean_object* v_x_453_, lean_object* v_h__1_454_, lean_object* v_h__2_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(v_00_u03b1_450_, v_as_451_, v_motive_452_, v_x_453_, v_h__1_454_, v_h__2_455_);
lean_dec_ref(v_as_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg___lam__0(lean_object* v_x1_457_, lean_object* v_x2_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v_x2_458_);
lean_ctor_set(v___x_459_, 1, v_x1_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg(lean_object* v_xs_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_481_ = lean_box(0);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_array_get_size(v_xs_480_);
v___x_484_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_485_ = lean_nat_dec_lt(v___x_482_, v___x_483_);
if (v___x_485_ == 0)
{
lean_dec_ref(v_xs_480_);
return v___x_481_;
}
else
{
lean_object* v___f_486_; uint8_t v___x_487_; 
v___f_486_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_487_ = lean_nat_dec_le(v___x_483_, v___x_483_);
if (v___x_487_ == 0)
{
if (v___x_485_ == 0)
{
lean_dec_ref(v_xs_480_);
return v___x_481_;
}
else
{
size_t v___x_488_; size_t v___x_489_; lean_object* v___x_490_; 
v___x_488_ = ((size_t)0ULL);
v___x_489_ = lean_usize_of_nat(v___x_483_);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_484_, v___f_486_, v_xs_480_, v___x_488_, v___x_489_, v___x_481_);
return v___x_490_;
}
}
else
{
size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v___x_491_ = ((size_t)0ULL);
v___x_492_ = lean_usize_of_nat(v___x_483_);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_484_, v___f_486_, v_xs_480_, v___x_491_, v___x_492_, v___x_481_);
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toListRev(lean_object* v_00_u03b1_494_, lean_object* v_xs_495_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_496_ = lean_box(0);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_array_get_size(v_xs_495_);
v___x_499_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_500_ = lean_nat_dec_lt(v___x_497_, v___x_498_);
if (v___x_500_ == 0)
{
lean_dec_ref(v_xs_495_);
return v___x_496_;
}
else
{
lean_object* v___f_501_; uint8_t v___x_502_; 
v___f_501_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_502_ = lean_nat_dec_le(v___x_498_, v___x_498_);
if (v___x_502_ == 0)
{
if (v___x_500_ == 0)
{
lean_dec_ref(v_xs_495_);
return v___x_496_;
}
else
{
size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v___x_503_ = ((size_t)0ULL);
v___x_504_ = lean_usize_of_nat(v___x_498_);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_499_, v___f_501_, v_xs_495_, v___x_503_, v___x_504_, v___x_496_);
return v___x_505_;
}
}
else
{
size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; 
v___x_506_ = ((size_t)0ULL);
v___x_507_ = lean_usize_of_nat(v___x_498_);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_499_, v___f_501_, v_xs_495_, v___x_506_, v___x_507_, v___x_496_);
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(lean_object* v_x_509_, lean_object* v_h__1_510_, lean_object* v_h__2_511_){
_start:
{
lean_object* v_zero_512_; uint8_t v_isZero_513_; 
v_zero_512_ = lean_unsigned_to_nat(0u);
v_isZero_513_ = lean_nat_dec_eq(v_x_509_, v_zero_512_);
if (v_isZero_513_ == 1)
{
lean_object* v___x_514_; 
lean_dec(v_h__1_510_);
v___x_514_ = lean_apply_1(v_h__2_511_, lean_box(0));
return v___x_514_;
}
else
{
lean_object* v_one_515_; lean_object* v_n_516_; lean_object* v___x_517_; 
lean_dec(v_h__2_511_);
v_one_515_ = lean_unsigned_to_nat(1u);
v_n_516_ = lean_nat_sub(v_x_509_, v_one_515_);
v___x_517_ = lean_apply_2(v_h__1_510_, v_n_516_, lean_box(0));
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg___boxed(lean_object* v_x_518_, lean_object* v_h__1_519_, lean_object* v_h__2_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(v_x_518_, v_h__1_519_, v_h__2_520_);
lean_dec(v_x_518_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(lean_object* v_n_522_, lean_object* v_motive_523_, lean_object* v_x_524_, lean_object* v_x_525_, lean_object* v_h__1_526_, lean_object* v_h__2_527_){
_start:
{
lean_object* v_zero_528_; uint8_t v_isZero_529_; 
v_zero_528_ = lean_unsigned_to_nat(0u);
v_isZero_529_ = lean_nat_dec_eq(v_x_524_, v_zero_528_);
if (v_isZero_529_ == 1)
{
lean_object* v___x_530_; 
lean_dec(v_h__1_526_);
v___x_530_ = lean_apply_1(v_h__2_527_, lean_box(0));
return v___x_530_;
}
else
{
lean_object* v_one_531_; lean_object* v_n_532_; lean_object* v___x_533_; 
lean_dec(v_h__2_527_);
v_one_531_ = lean_unsigned_to_nat(1u);
v_n_532_ = lean_nat_sub(v_x_524_, v_one_531_);
v___x_533_ = lean_apply_2(v_h__1_526_, v_n_532_, lean_box(0));
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___boxed(lean_object* v_n_534_, lean_object* v_motive_535_, lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v_h__1_538_, lean_object* v_h__2_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(v_n_534_, v_motive_535_, v_x_536_, v_x_537_, v_h__1_538_, v_h__2_539_);
lean_dec(v_x_536_);
lean_dec(v_n_534_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_541_, lean_object* v_h__1_542_, lean_object* v_h__2_543_){
_start:
{
if (lean_obj_tag(v_opt_541_) == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_h__1_542_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_apply_1(v_h__2_543_, v___x_544_);
return v___x_545_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_547_; 
lean_dec(v_h__2_543_);
v_val_546_ = lean_ctor_get(v_opt_541_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v_opt_541_, 1);
v___x_547_ = lean_apply_1(v_h__1_542_, v_val_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_548_, lean_object* v_motive_549_, lean_object* v_opt_550_, lean_object* v_h__1_551_, lean_object* v_h__2_552_){
_start:
{
if (lean_obj_tag(v_opt_550_) == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v_h__1_551_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_apply_1(v_h__2_552_, v___x_553_);
return v___x_554_;
}
else
{
lean_object* v_val_555_; lean_object* v___x_556_; 
lean_dec(v_h__2_552_);
v_val_555_ = lean_ctor_get(v_opt_550_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v_opt_550_, 1);
v___x_556_ = lean_apply_1(v_h__1_551_, v_val_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_557_, lean_object* v_h__1_558_, lean_object* v_h__2_559_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_h__1_558_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_apply_1(v_h__2_559_, v___x_560_);
return v___x_561_;
}
else
{
lean_object* v_val_562_; lean_object* v___x_563_; 
lean_dec(v_h__2_559_);
v_val_562_ = lean_ctor_get(v_x_557_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v_x_557_, 1);
v___x_563_ = lean_apply_1(v_h__1_558_, v_val_562_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_564_, lean_object* v_motive_565_, lean_object* v_x_566_, lean_object* v_h__1_567_, lean_object* v_h__2_568_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_h__1_567_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_apply_1(v_h__2_568_, v___x_569_);
return v___x_570_;
}
else
{
lean_object* v_val_571_; lean_object* v___x_572_; 
lean_dec(v_h__2_568_);
v_val_571_ = lean_ctor_get(v_x_566_, 0);
lean_inc(v_val_571_);
lean_dec_ref_known(v_x_566_, 1);
v___x_572_ = lean_apply_1(v_h__1_567_, v_val_571_);
return v___x_572_;
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
