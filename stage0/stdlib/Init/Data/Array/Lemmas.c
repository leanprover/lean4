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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
if (v_____do__lift_54_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_h__1_55_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_apply_1(v_h__2_56_, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_56_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_1(v_h__1_55_, v___x_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
uint8_t v_____do__lift_24__boxed_64_; lean_object* v_res_65_; 
v_____do__lift_24__boxed_64_ = lean_unbox(v_____do__lift_61_);
v_res_65_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(v_____do__lift_24__boxed_64_, v_h__1_62_, v_h__2_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(lean_object* v_motive_66_, uint8_t v_____do__lift_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (v_____do__lift_67_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_h__1_68_);
v___x_70_ = lean_box(0);
v___x_71_ = lean_apply_1(v_h__2_69_, v___x_70_);
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_h__2_69_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_apply_1(v_h__1_68_, v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_74_, lean_object* v_____do__lift_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
uint8_t v_____do__lift_35__boxed_78_; lean_object* v_res_79_; 
v_____do__lift_35__boxed_78_ = lean_unbox(v_____do__lift_75_);
v_res_79_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(v_motive_74_, v_____do__lift_35__boxed_78_, v_h__1_76_, v_h__2_77_);
return v_res_79_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_80_, lean_object* v_a_81_, lean_object* v_as_82_){
_start:
{
uint8_t v___x_83_; 
v___x_83_ = l_Array_contains___redArg(v_inst_80_, v_as_82_, v_a_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_84_, lean_object* v_a_85_, lean_object* v_as_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Array_instDecidableMemOfLawfulBEq___redArg(v_inst_84_, v_a_85_, v_as_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_a_92_, lean_object* v_as_93_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = l_Array_contains___redArg(v_inst_90_, v_as_93_, v_a_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_a_98_, lean_object* v_as_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Array_instDecidableMemOfLawfulBEq(v_00_u03b1_95_, v_inst_96_, v_inst_97_, v_a_98_, v_as_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
if (lean_obj_tag(v_____do__lift_102_) == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_h__1_103_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_apply_1(v_h__2_104_, v___x_105_);
return v___x_106_;
}
else
{
lean_object* v_val_107_; lean_object* v___x_108_; 
lean_dec(v_h__2_104_);
v_val_107_ = lean_ctor_get(v_____do__lift_102_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v_____do__lift_102_, 1);
v___x_108_ = lean_apply_1(v_h__1_103_, v_val_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter(lean_object* v_00_u03b2_109_, lean_object* v_motive_110_, lean_object* v_____do__lift_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
_start:
{
if (lean_obj_tag(v_____do__lift_111_) == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_h__1_112_);
v___x_114_ = lean_box(0);
v___x_115_ = lean_apply_1(v_h__2_113_, v___x_114_);
return v___x_115_;
}
else
{
lean_object* v_val_116_; lean_object* v___x_117_; 
lean_dec(v_h__2_113_);
v_val_116_ = lean_ctor_get(v_____do__lift_111_, 0);
lean_inc(v_val_116_);
lean_dec_ref_known(v_____do__lift_111_, 1);
v___x_117_ = lean_apply_1(v_h__1_112_, v_val_116_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
if (lean_obj_tag(v_x_118_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v_h__2_120_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_apply_1(v_h__1_119_, v___x_121_);
return v___x_122_;
}
else
{
lean_object* v_val_123_; lean_object* v___x_124_; 
lean_dec(v_h__1_119_);
v_val_123_ = lean_ctor_get(v_x_118_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v_x_118_, 1);
v___x_124_ = lean_apply_1(v_h__2_120_, v_val_123_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_125_, lean_object* v_motive_126_, lean_object* v_x_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_h__2_129_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_apply_1(v_h__1_128_, v___x_130_);
return v___x_131_;
}
else
{
lean_object* v_val_132_; lean_object* v___x_133_; 
lean_dec(v_h__1_128_);
v_val_132_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_val_132_);
lean_dec_ref_known(v_x_127_, 1);
v___x_133_ = lean_apply_1(v_h__2_129_, v_val_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter___redArg(lean_object* v_x_134_, lean_object* v_h__1_135_, lean_object* v_h__2_136_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v_h__2_136_);
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_1(v_h__1_135_, v___x_137_);
return v___x_138_;
}
else
{
lean_object* v_val_139_; lean_object* v___x_140_; 
lean_dec(v_h__1_135_);
v_val_139_ = lean_ctor_get(v_x_134_, 0);
lean_inc(v_val_139_);
lean_dec_ref_known(v_x_134_, 1);
v___x_140_ = lean_apply_1(v_h__2_136_, v_val_139_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter(lean_object* v_00_u03b2_141_, lean_object* v_motive_142_, lean_object* v_x_143_, lean_object* v_h__1_144_, lean_object* v_h__2_145_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v_h__2_145_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_apply_1(v_h__1_144_, v___x_146_);
return v___x_147_;
}
else
{
lean_object* v_val_148_; lean_object* v___x_149_; 
lean_dec(v_h__1_144_);
v_val_148_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_val_148_);
lean_dec_ref_known(v_x_143_, 1);
v___x_149_ = lean_apply_1(v_h__2_145_, v_val_148_);
return v___x_149_;
}
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__12(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__10));
v___x_177_ = l_Lean_mkAtom(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__13(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__12, &l_Array_filterMap__replicate___auto__7___closed__12_once, _init_l_Array_filterMap__replicate___auto__7___closed__12);
v___x_179_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_180_ = lean_array_push(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__17(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_192_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_193_ = lean_array_push(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__18(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_194_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__17, &l_Array_filterMap__replicate___auto__7___closed__17_once, _init_l_Array_filterMap__replicate___auto__7___closed__17);
v___x_195_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__15));
v___x_196_ = lean_box(2);
v___x_197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
lean_ctor_set(v___x_197_, 2, v___x_194_);
return v___x_197_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__19(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__18, &l_Array_filterMap__replicate___auto__7___closed__18_once, _init_l_Array_filterMap__replicate___auto__7___closed__18);
v___x_199_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__13, &l_Array_filterMap__replicate___auto__7___closed__13_once, _init_l_Array_filterMap__replicate___auto__7___closed__13);
v___x_200_ = lean_array_push(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__20(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_202_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__19, &l_Array_filterMap__replicate___auto__7___closed__19_once, _init_l_Array_filterMap__replicate___auto__7___closed__19);
v___x_203_ = lean_array_push(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__21(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_205_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__20, &l_Array_filterMap__replicate___auto__7___closed__20_once, _init_l_Array_filterMap__replicate___auto__7___closed__20);
v___x_206_ = lean_array_push(v___x_205_, v___x_204_);
return v___x_206_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__22(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_208_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__21, &l_Array_filterMap__replicate___auto__7___closed__21_once, _init_l_Array_filterMap__replicate___auto__7___closed__21);
v___x_209_ = lean_array_push(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__23(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_211_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__22, &l_Array_filterMap__replicate___auto__7___closed__22_once, _init_l_Array_filterMap__replicate___auto__7___closed__22);
v___x_212_ = lean_array_push(v___x_211_, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__24(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_213_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__23, &l_Array_filterMap__replicate___auto__7___closed__23_once, _init_l_Array_filterMap__replicate___auto__7___closed__23);
v___x_214_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__11));
v___x_215_ = lean_box(2);
v___x_216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
lean_ctor_set(v___x_216_, 2, v___x_213_);
return v___x_216_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__25(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__24, &l_Array_filterMap__replicate___auto__7___closed__24_once, _init_l_Array_filterMap__replicate___auto__7___closed__24);
v___x_218_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_219_ = lean_array_push(v___x_218_, v___x_217_);
return v___x_219_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__26(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_220_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__25, &l_Array_filterMap__replicate___auto__7___closed__25_once, _init_l_Array_filterMap__replicate___auto__7___closed__25);
v___x_221_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__9));
v___x_222_ = lean_box(2);
v___x_223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
lean_ctor_set(v___x_223_, 2, v___x_220_);
return v___x_223_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__27(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__26, &l_Array_filterMap__replicate___auto__7___closed__26_once, _init_l_Array_filterMap__replicate___auto__7___closed__26);
v___x_225_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_226_ = lean_array_push(v___x_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__28(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_227_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__27, &l_Array_filterMap__replicate___auto__7___closed__27_once, _init_l_Array_filterMap__replicate___auto__7___closed__27);
v___x_228_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__7));
v___x_229_ = lean_box(2);
v___x_230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_227_);
return v___x_230_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__29(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__28, &l_Array_filterMap__replicate___auto__7___closed__28_once, _init_l_Array_filterMap__replicate___auto__7___closed__28);
v___x_232_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_233_ = lean_array_push(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__30(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_234_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__29, &l_Array_filterMap__replicate___auto__7___closed__29_once, _init_l_Array_filterMap__replicate___auto__7___closed__29);
v___x_235_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__4));
v___x_236_ = lean_box(2);
v___x_237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_235_);
lean_ctor_set(v___x_237_, 2, v___x_234_);
return v___x_237_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__30, &l_Array_filterMap__replicate___auto__7___closed__30_once, _init_l_Array_filterMap__replicate___auto__7___closed__30);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object* v_x_239_, lean_object* v_h__1_240_, lean_object* v_h__2_241_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_h__2_241_);
v___x_242_ = lean_box(0);
v___x_243_ = lean_apply_1(v_h__1_240_, v___x_242_);
return v___x_243_;
}
else
{
lean_object* v_val_244_; lean_object* v___x_245_; 
lean_dec(v_h__1_240_);
v_val_244_ = lean_ctor_get(v_x_239_, 0);
lean_inc(v_val_244_);
lean_dec_ref_known(v_x_239_, 1);
v___x_245_ = lean_apply_1(v_h__2_241_, v_val_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object* v_00_u03b2_246_, lean_object* v_motive_247_, lean_object* v_x_248_, lean_object* v_h__1_249_, lean_object* v_h__2_250_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v_h__2_250_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_apply_1(v_h__1_249_, v___x_251_);
return v___x_252_;
}
else
{
lean_object* v_val_253_; lean_object* v___x_254_; 
lean_dec(v_h__1_249_);
v_val_253_ = lean_ctor_get(v_x_248_, 0);
lean_inc(v_val_253_);
lean_dec_ref_known(v_x_248_, 1);
v___x_254_ = lean_apply_1(v_h__2_250_, v_val_253_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(lean_object* v_i_255_, lean_object* v_h__1_256_, lean_object* v_h__2_257_){
_start:
{
lean_object* v_zero_258_; uint8_t v_isZero_259_; 
v_zero_258_ = lean_unsigned_to_nat(0u);
v_isZero_259_ = lean_nat_dec_eq(v_i_255_, v_zero_258_);
if (v_isZero_259_ == 1)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_h__2_257_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_apply_1(v_h__1_256_, v___x_260_);
return v___x_261_;
}
else
{
lean_object* v_one_262_; lean_object* v_n_263_; lean_object* v___x_264_; 
lean_dec(v_h__1_256_);
v_one_262_ = lean_unsigned_to_nat(1u);
v_n_263_ = lean_nat_sub(v_i_255_, v_one_262_);
v___x_264_ = lean_apply_1(v_h__2_257_, v_n_263_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg___boxed(lean_object* v_i_265_, lean_object* v_h__1_266_, lean_object* v_h__2_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(v_i_265_, v_h__1_266_, v_h__2_267_);
lean_dec(v_i_265_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(lean_object* v_motive_269_, lean_object* v_i_270_, lean_object* v_h__1_271_, lean_object* v_h__2_272_){
_start:
{
lean_object* v_zero_273_; uint8_t v_isZero_274_; 
v_zero_273_ = lean_unsigned_to_nat(0u);
v_isZero_274_ = lean_nat_dec_eq(v_i_270_, v_zero_273_);
if (v_isZero_274_ == 1)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec(v_h__2_272_);
v___x_275_ = lean_box(0);
v___x_276_ = lean_apply_1(v_h__1_271_, v___x_275_);
return v___x_276_;
}
else
{
lean_object* v_one_277_; lean_object* v_n_278_; lean_object* v___x_279_; 
lean_dec(v_h__1_271_);
v_one_277_ = lean_unsigned_to_nat(1u);
v_n_278_ = lean_nat_sub(v_i_270_, v_one_277_);
v___x_279_ = lean_apply_1(v_h__2_272_, v_n_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___boxed(lean_object* v_motive_280_, lean_object* v_i_281_, lean_object* v_h__1_282_, lean_object* v_h__2_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(v_motive_280_, v_i_281_, v_h__1_282_, v_h__2_283_);
lean_dec(v_i_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object* v_i_285_, lean_object* v_h__1_286_, lean_object* v_h__2_287_){
_start:
{
lean_object* v_zero_288_; uint8_t v_isZero_289_; 
v_zero_288_ = lean_unsigned_to_nat(0u);
v_isZero_289_ = lean_nat_dec_eq(v_i_285_, v_zero_288_);
if (v_isZero_289_ == 1)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec(v_h__2_287_);
v___x_290_ = lean_box(0);
v___x_291_ = lean_apply_1(v_h__1_286_, v___x_290_);
return v___x_291_;
}
else
{
lean_object* v_one_292_; lean_object* v_n_293_; lean_object* v___x_294_; 
lean_dec(v_h__1_286_);
v_one_292_ = lean_unsigned_to_nat(1u);
v_n_293_ = lean_nat_sub(v_i_285_, v_one_292_);
v___x_294_ = lean_apply_1(v_h__2_287_, v_n_293_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object* v_i_295_, lean_object* v_h__1_296_, lean_object* v_h__2_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_295_, v_h__1_296_, v_h__2_297_);
lean_dec(v_i_295_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object* v_motive_299_, lean_object* v_i_300_, lean_object* v_h__1_301_, lean_object* v_h__2_302_){
_start:
{
lean_object* v_zero_303_; uint8_t v_isZero_304_; 
v_zero_303_ = lean_unsigned_to_nat(0u);
v_isZero_304_ = lean_nat_dec_eq(v_i_300_, v_zero_303_);
if (v_isZero_304_ == 1)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v_h__2_302_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_apply_1(v_h__1_301_, v___x_305_);
return v___x_306_;
}
else
{
lean_object* v_one_307_; lean_object* v_n_308_; lean_object* v___x_309_; 
lean_dec(v_h__1_301_);
v_one_307_ = lean_unsigned_to_nat(1u);
v_n_308_ = lean_nat_sub(v_i_300_, v_one_307_);
v___x_309_ = lean_apply_1(v_h__2_302_, v_n_308_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object* v_motive_310_, lean_object* v_i_311_, lean_object* v_h__1_312_, lean_object* v_h__2_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(v_motive_310_, v_i_311_, v_h__1_312_, v_h__2_313_);
lean_dec(v_i_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_315_, lean_object* v_h__1_316_, lean_object* v_h__2_317_){
_start:
{
lean_object* v_zero_318_; uint8_t v_isZero_319_; 
v_zero_318_ = lean_unsigned_to_nat(0u);
v_isZero_319_ = lean_nat_dec_eq(v_x_315_, v_zero_318_);
if (v_isZero_319_ == 1)
{
lean_object* v___x_320_; 
lean_dec(v_h__2_317_);
v___x_320_ = lean_apply_1(v_h__1_316_, lean_box(0));
return v___x_320_;
}
else
{
lean_object* v_one_321_; lean_object* v_n_322_; lean_object* v___x_323_; 
lean_dec(v_h__1_316_);
v_one_321_ = lean_unsigned_to_nat(1u);
v_n_322_ = lean_nat_sub(v_x_315_, v_one_321_);
v___x_323_ = lean_apply_2(v_h__2_317_, v_n_322_, lean_box(0));
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_324_, lean_object* v_h__1_325_, lean_object* v_h__2_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(v_x_324_, v_h__1_325_, v_h__2_326_);
lean_dec(v_x_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_328_, lean_object* v_xs_329_, lean_object* v_motive_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_h__1_333_, lean_object* v_h__2_334_){
_start:
{
lean_object* v_zero_335_; uint8_t v_isZero_336_; 
v_zero_335_ = lean_unsigned_to_nat(0u);
v_isZero_336_ = lean_nat_dec_eq(v_x_331_, v_zero_335_);
if (v_isZero_336_ == 1)
{
lean_object* v___x_337_; 
lean_dec(v_h__2_334_);
v___x_337_ = lean_apply_1(v_h__1_333_, lean_box(0));
return v___x_337_;
}
else
{
lean_object* v_one_338_; lean_object* v_n_339_; lean_object* v___x_340_; 
lean_dec(v_h__1_333_);
v_one_338_ = lean_unsigned_to_nat(1u);
v_n_339_ = lean_nat_sub(v_x_331_, v_one_338_);
v___x_340_ = lean_apply_2(v_h__2_334_, v_n_339_, lean_box(0));
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_341_, lean_object* v_xs_342_, lean_object* v_motive_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_h__1_346_, lean_object* v_h__2_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_341_, v_xs_342_, v_motive_343_, v_x_344_, v_x_345_, v_h__1_346_, v_h__2_347_);
lean_dec(v_x_344_);
lean_dec_ref(v_xs_342_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object* v_x_349_, lean_object* v_h__1_350_, lean_object* v_h__2_351_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v_h__1_350_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_apply_1(v_h__2_351_, v___x_352_);
return v___x_353_;
}
else
{
lean_object* v_val_354_; lean_object* v___x_355_; 
lean_dec(v_h__2_351_);
v_val_354_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_val_354_);
lean_dec_ref_known(v_x_349_, 1);
v___x_355_ = lean_apply_1(v_h__1_350_, v_val_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object* v_00_u03b2_356_, lean_object* v_motive_357_, lean_object* v_x_358_, lean_object* v_h__1_359_, lean_object* v_h__2_360_){
_start:
{
if (lean_obj_tag(v_x_358_) == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec(v_h__1_359_);
v___x_361_ = lean_box(0);
v___x_362_ = lean_apply_1(v_h__2_360_, v___x_361_);
return v___x_362_;
}
else
{
lean_object* v_val_363_; lean_object* v___x_364_; 
lean_dec(v_h__2_360_);
v_val_363_ = lean_ctor_get(v_x_358_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v_x_358_, 1);
v___x_364_ = lean_apply_1(v_h__1_359_, v_val_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter___redArg(lean_object* v_x_365_, lean_object* v_h__1_366_, lean_object* v_h__2_367_){
_start:
{
if (lean_obj_tag(v_x_365_) == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v_h__1_366_);
v___x_368_ = lean_box(0);
v___x_369_ = lean_apply_1(v_h__2_367_, v___x_368_);
return v___x_369_;
}
else
{
lean_object* v_val_370_; lean_object* v___x_371_; 
lean_dec(v_h__2_367_);
v_val_370_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v_x_365_, 1);
v___x_371_ = lean_apply_1(v_h__1_366_, v_val_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter(lean_object* v_00_u03b2_372_, lean_object* v_motive_373_, lean_object* v_x_374_, lean_object* v_h__1_375_, lean_object* v_h__2_376_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_h__1_375_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_apply_1(v_h__2_376_, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v_val_379_; lean_object* v___x_380_; 
lean_dec(v_h__2_376_);
v_val_379_ = lean_ctor_get(v_x_374_, 0);
lean_inc(v_val_379_);
lean_dec_ref_known(v_x_374_, 1);
v___x_380_ = lean_apply_1(v_h__1_375_, v_val_379_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___redArg(lean_object* v_x_381_, lean_object* v_h__1_382_, lean_object* v_h__2_383_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v_h__2_383_);
v___x_384_ = lean_box(0);
v___x_385_ = lean_apply_1(v_h__1_382_, v___x_384_);
return v___x_385_;
}
else
{
lean_object* v_val_386_; lean_object* v___x_387_; 
lean_dec(v_h__1_382_);
v_val_386_ = lean_ctor_get(v_x_381_, 0);
lean_inc(v_val_386_);
lean_dec_ref_known(v_x_381_, 1);
v___x_387_ = lean_apply_1(v_h__2_383_, v_val_386_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(lean_object* v_00_u03b1_388_, lean_object* v_as_389_, lean_object* v_motive_390_, lean_object* v_x_391_, lean_object* v_h__1_392_, lean_object* v_h__2_393_){
_start:
{
if (lean_obj_tag(v_x_391_) == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec(v_h__2_393_);
v___x_394_ = lean_box(0);
v___x_395_ = lean_apply_1(v_h__1_392_, v___x_394_);
return v___x_395_;
}
else
{
lean_object* v_val_396_; lean_object* v___x_397_; 
lean_dec(v_h__1_392_);
v_val_396_ = lean_ctor_get(v_x_391_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v_x_391_, 1);
v___x_397_ = lean_apply_1(v_h__2_393_, v_val_396_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_398_, lean_object* v_as_399_, lean_object* v_motive_400_, lean_object* v_x_401_, lean_object* v_h__1_402_, lean_object* v_h__2_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(v_00_u03b1_398_, v_as_399_, v_motive_400_, v_x_401_, v_h__1_402_, v_h__2_403_);
lean_dec_ref(v_as_399_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg___lam__0(lean_object* v_x1_405_, lean_object* v_x2_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_407_, 0, v_x2_406_);
lean_ctor_set(v___x_407_, 1, v_x1_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg(lean_object* v_xs_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_429_ = lean_box(0);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_array_get_size(v_xs_428_);
v___x_432_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_433_ = lean_nat_dec_lt(v___x_430_, v___x_431_);
if (v___x_433_ == 0)
{
lean_dec_ref(v_xs_428_);
return v___x_429_;
}
else
{
lean_object* v___f_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
v___f_434_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_435_ = ((size_t)0ULL);
v___x_436_ = lean_usize_of_nat(v___x_431_);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_432_, v___f_434_, v_xs_428_, v___x_435_, v___x_436_, v___x_429_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Array_toListRev(lean_object* v_00_u03b1_438_, lean_object* v_xs_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_440_ = lean_box(0);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_array_get_size(v_xs_439_);
v___x_443_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_444_ = lean_nat_dec_lt(v___x_441_, v___x_442_);
if (v___x_444_ == 0)
{
lean_dec_ref(v_xs_439_);
return v___x_440_;
}
else
{
lean_object* v___f_445_; size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
v___f_445_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_446_ = ((size_t)0ULL);
v___x_447_ = lean_usize_of_nat(v___x_442_);
v___x_448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_443_, v___f_445_, v_xs_439_, v___x_446_, v___x_447_, v___x_440_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(lean_object* v_x_449_, lean_object* v_h__1_450_, lean_object* v_h__2_451_){
_start:
{
lean_object* v_zero_452_; uint8_t v_isZero_453_; 
v_zero_452_ = lean_unsigned_to_nat(0u);
v_isZero_453_ = lean_nat_dec_eq(v_x_449_, v_zero_452_);
if (v_isZero_453_ == 1)
{
lean_object* v___x_454_; 
lean_dec(v_h__1_450_);
v___x_454_ = lean_apply_1(v_h__2_451_, lean_box(0));
return v___x_454_;
}
else
{
lean_object* v_one_455_; lean_object* v_n_456_; lean_object* v___x_457_; 
lean_dec(v_h__2_451_);
v_one_455_ = lean_unsigned_to_nat(1u);
v_n_456_ = lean_nat_sub(v_x_449_, v_one_455_);
v___x_457_ = lean_apply_2(v_h__1_450_, v_n_456_, lean_box(0));
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg___boxed(lean_object* v_x_458_, lean_object* v_h__1_459_, lean_object* v_h__2_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(v_x_458_, v_h__1_459_, v_h__2_460_);
lean_dec(v_x_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(lean_object* v_n_462_, lean_object* v_motive_463_, lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v_h__1_466_, lean_object* v_h__2_467_){
_start:
{
lean_object* v_zero_468_; uint8_t v_isZero_469_; 
v_zero_468_ = lean_unsigned_to_nat(0u);
v_isZero_469_ = lean_nat_dec_eq(v_x_464_, v_zero_468_);
if (v_isZero_469_ == 1)
{
lean_object* v___x_470_; 
lean_dec(v_h__1_466_);
v___x_470_ = lean_apply_1(v_h__2_467_, lean_box(0));
return v___x_470_;
}
else
{
lean_object* v_one_471_; lean_object* v_n_472_; lean_object* v___x_473_; 
lean_dec(v_h__2_467_);
v_one_471_ = lean_unsigned_to_nat(1u);
v_n_472_ = lean_nat_sub(v_x_464_, v_one_471_);
v___x_473_ = lean_apply_2(v_h__1_466_, v_n_472_, lean_box(0));
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___boxed(lean_object* v_n_474_, lean_object* v_motive_475_, lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_h__1_478_, lean_object* v_h__2_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(v_n_474_, v_motive_475_, v_x_476_, v_x_477_, v_h__1_478_, v_h__2_479_);
lean_dec(v_x_476_);
lean_dec(v_n_474_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_481_, lean_object* v_h__1_482_, lean_object* v_h__2_483_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v_h__1_482_);
v___x_484_ = lean_box(0);
v___x_485_ = lean_apply_1(v_h__2_483_, v___x_484_);
return v___x_485_;
}
else
{
lean_object* v_val_486_; lean_object* v___x_487_; 
lean_dec(v_h__2_483_);
v_val_486_ = lean_ctor_get(v_x_481_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v_x_481_, 1);
v___x_487_ = lean_apply_1(v_h__1_482_, v_val_486_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_488_, lean_object* v_motive_489_, lean_object* v_x_490_, lean_object* v_h__1_491_, lean_object* v_h__2_492_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v_h__1_491_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_apply_1(v_h__2_492_, v___x_493_);
return v___x_494_;
}
else
{
lean_object* v_val_495_; lean_object* v___x_496_; 
lean_dec(v_h__2_492_);
v_val_495_ = lean_ctor_get(v_x_490_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v_x_490_, 1);
v___x_496_ = lean_apply_1(v_h__1_491_, v_val_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_497_, lean_object* v_h__1_498_, lean_object* v_h__2_499_){
_start:
{
if (lean_obj_tag(v_opt_497_) == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec(v_h__1_498_);
v___x_500_ = lean_box(0);
v___x_501_ = lean_apply_1(v_h__2_499_, v___x_500_);
return v___x_501_;
}
else
{
lean_object* v_val_502_; lean_object* v___x_503_; 
lean_dec(v_h__2_499_);
v_val_502_ = lean_ctor_get(v_opt_497_, 0);
lean_inc(v_val_502_);
lean_dec_ref_known(v_opt_497_, 1);
v___x_503_ = lean_apply_1(v_h__1_498_, v_val_502_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_504_, lean_object* v_motive_505_, lean_object* v_opt_506_, lean_object* v_h__1_507_, lean_object* v_h__2_508_){
_start:
{
if (lean_obj_tag(v_opt_506_) == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v_h__1_507_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_apply_1(v_h__2_508_, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v_val_511_; lean_object* v___x_512_; 
lean_dec(v_h__2_508_);
v_val_511_ = lean_ctor_get(v_opt_506_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v_opt_506_, 1);
v___x_512_ = lean_apply_1(v_h__1_507_, v_val_511_);
return v___x_512_;
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
