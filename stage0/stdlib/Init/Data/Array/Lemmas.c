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
uint8_t l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(lean_object* v_xs_1_, lean_object* v_inst_2_, lean_object* v_i_3_, lean_object* v_h_4_){
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
LEAN_EXPORT void l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1_ = stack[0].m_obj;
lean_object* v_inst_2_ = stack[1].m_obj;
lean_object* v_i_3_ = stack[2].m_obj;
uint8_t v_res_8_;
v_res_8_ = l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(v_xs_1_, v_inst_2_, v_i_3_, lean_box(0));
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(lean_object* v_xs_9_, lean_object* v_inst_10_, lean_object* v_i_11_, lean_object* v_h_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(v_xs_9_, v_inst_10_, v_i_11_, v_h_12_);
lean_dec(v_i_11_);
lean_dec_ref(v_xs_9_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
uint8_t l_Array_instDecidableForallForallMemOfDecidablePred___redArg(lean_object* v_xs_15_, lean_object* v_inst_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
lean_inc_ref(v_xs_15_);
v___f_17_ = lean_alloc_closure((void*)(l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_17_, 0, v_xs_15_);
lean_closure_set(v___f_17_, 1, v_inst_16_);
v___x_18_ = lean_array_get_size(v_xs_15_);
lean_dec_ref(v_xs_15_);
v___x_19_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(v___x_18_, v___f_17_, v___x_18_, lean_box(0));
return v___x_19_;
}
}
LEAN_EXPORT void l_Array_instDecidableForallForallMemOfDecidablePred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_15_ = stack[0].m_obj;
lean_object* v_inst_16_ = stack[1].m_obj;
uint8_t v_res_20_;
v_res_20_ = l_Array_instDecidableForallForallMemOfDecidablePred___redArg(v_xs_15_, v_inst_16_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___redArg___boxed(lean_object* v_xs_21_, lean_object* v_inst_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Array_instDecidableForallForallMemOfDecidablePred___redArg(v_xs_21_, v_inst_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
uint8_t l_Array_instDecidableForallForallMemOfDecidablePred(lean_object* v_00_u03b1_25_, lean_object* v_xs_26_, lean_object* v_p_27_, lean_object* v_inst_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = l_Array_instDecidableForallForallMemOfDecidablePred___redArg(v_xs_26_, v_inst_28_);
return v___x_29_;
}
}
LEAN_EXPORT void l_Array_instDecidableForallForallMemOfDecidablePred_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_26_ = stack[1].m_obj;
lean_object* v_inst_28_ = stack[3].m_obj;
uint8_t v_res_30_;
v_res_30_ = l_Array_instDecidableForallForallMemOfDecidablePred(lean_box(0), v_xs_26_, lean_box(0), v_inst_28_);
stack->m_num = v_res_30_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___boxed(lean_object* v_00_u03b1_31_, lean_object* v_xs_32_, lean_object* v_p_33_, lean_object* v_inst_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Array_instDecidableForallForallMemOfDecidablePred(v_00_u03b1_31_, v_xs_32_, v_p_33_, v_inst_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(lean_object* v_xs_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v___f_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
lean_inc_ref(v_xs_37_);
v___f_39_ = lean_alloc_closure((void*)(l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_39_, 0, v_xs_37_);
lean_closure_set(v___f_39_, 1, v_inst_38_);
v___x_40_ = lean_array_get_size(v_xs_37_);
lean_dec_ref(v_xs_37_);
v___x_41_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(v___x_40_, v___f_39_, v___x_40_, lean_box(0));
return v___x_41_;
}
}
LEAN_EXPORT void l_Array_instDecidableExistsAndMemOfDecidablePred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_37_ = stack[0].m_obj;
lean_object* v_inst_38_ = stack[1].m_obj;
uint8_t v_res_42_;
v_res_42_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_xs_37_, v_inst_38_);
stack->m_num = v_res_42_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___boxed(lean_object* v_xs_43_, lean_object* v_inst_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_xs_43_, v_inst_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred(lean_object* v_00_u03b1_47_, lean_object* v_xs_48_, lean_object* v_p_49_, lean_object* v_inst_50_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_xs_48_, v_inst_50_);
return v___x_51_;
}
}
LEAN_EXPORT void l_Array_instDecidableExistsAndMemOfDecidablePred_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_48_ = stack[1].m_obj;
lean_object* v_inst_50_ = stack[3].m_obj;
uint8_t v_res_52_;
v_res_52_ = l_Array_instDecidableExistsAndMemOfDecidablePred(lean_box(0), v_xs_48_, lean_box(0), v_inst_50_);
stack->m_num = v_res_52_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableExistsAndMemOfDecidablePred___boxed(lean_object* v_00_u03b1_53_, lean_object* v_xs_54_, lean_object* v_p_55_, lean_object* v_inst_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_Array_instDecidableExistsAndMemOfDecidablePred(v_00_u03b1_53_, v_xs_54_, v_p_55_, v_inst_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
if (v_____do__lift_59_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__1_60_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__2_61_, v___x_62_);
return v___x_63_;
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_61_);
v___x_64_ = lean_box(0);
v___x_65_ = lean_apply_1(v_h__1_60_, v___x_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_59_ = stack[0].m_num;
lean_object* v_h__1_60_ = stack[1].m_obj;
lean_object* v_h__2_61_ = stack[2].m_obj;
lean_object* v_res_66_;
v_res_66_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(v_____do__lift_59_, v_h__1_60_, v_h__2_61_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
uint8_t v_____do__lift_24__boxed_70_; lean_object* v_res_71_; 
v_____do__lift_24__boxed_70_ = lean_unbox(v_____do__lift_67_);
v_res_71_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(v_____do__lift_24__boxed_70_, v_h__1_68_, v_h__2_69_);
return v_res_71_;
}
}
lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(lean_object* v_motive_72_, uint8_t v_____do__lift_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_){
_start:
{
if (v_____do__lift_73_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v_h__1_74_);
v___x_76_ = lean_box(0);
v___x_77_ = lean_apply_1(v_h__2_75_, v___x_76_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_h__2_75_);
v___x_78_ = lean_box(0);
v___x_79_ = lean_apply_1(v_h__1_74_, v___x_78_);
return v___x_79_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_73_ = stack[1].m_num;
lean_object* v_h__1_74_ = stack[2].m_obj;
lean_object* v_h__2_75_ = stack[3].m_obj;
lean_object* v_res_80_;
v_res_80_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(lean_box(0), v_____do__lift_73_, v_h__1_74_, v_h__2_75_);
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_81_, lean_object* v_____do__lift_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
uint8_t v_____do__lift_41__boxed_85_; lean_object* v_res_86_; 
v_____do__lift_41__boxed_85_ = lean_unbox(v_____do__lift_82_);
v_res_86_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(v_motive_81_, v_____do__lift_41__boxed_85_, v_h__1_83_, v_h__2_84_);
return v_res_86_;
}
}
uint8_t l_Array_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_87_, lean_object* v_a_88_, lean_object* v_as_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = l_Array_contains___redArg(v_inst_87_, v_as_89_, v_a_88_);
return v___x_90_;
}
}
LEAN_EXPORT void l_Array_instDecidableMemOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_87_ = stack[0].m_obj;
lean_object* v_a_88_ = stack[1].m_obj;
lean_object* v_as_89_ = stack[2].m_obj;
uint8_t v_res_91_;
v_res_91_ = l_Array_instDecidableMemOfLawfulBEq___redArg(v_inst_87_, v_a_88_, v_as_89_);
stack->m_num = v_res_91_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_92_, lean_object* v_a_93_, lean_object* v_as_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Array_instDecidableMemOfLawfulBEq___redArg(v_inst_92_, v_a_93_, v_as_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
uint8_t l_Array_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_a_100_, lean_object* v_as_101_){
_start:
{
uint8_t v___x_102_; 
v___x_102_ = l_Array_contains___redArg(v_inst_98_, v_as_101_, v_a_100_);
return v___x_102_;
}
}
LEAN_EXPORT void l_Array_instDecidableMemOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_98_ = stack[1].m_obj;
lean_object* v_a_100_ = stack[3].m_obj;
lean_object* v_as_101_ = stack[4].m_obj;
uint8_t v_res_103_;
v_res_103_ = l_Array_instDecidableMemOfLawfulBEq(lean_box(0), v_inst_98_, lean_box(0), v_a_100_, v_as_101_);
stack->m_num = v_res_103_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_a_107_, lean_object* v_as_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Array_instDecidableMemOfLawfulBEq(v_00_u03b1_104_, v_inst_105_, v_inst_106_, v_a_107_, v_as_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter(lean_object* v_00_u03b2_118_, lean_object* v_motive_119_, lean_object* v_____do__lift_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_134_, lean_object* v_motive_135_, lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter___redArg(lean_object* v_x_143_, lean_object* v_h__1_144_, lean_object* v_h__2_145_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter(lean_object* v_00_u03b2_150_, lean_object* v_motive_151_, lean_object* v_x_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_){
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
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__12(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__10));
v___x_186_ = l_Lean_mkAtom(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__13(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__12, &l_Array_filterMap__replicate___auto__7___closed__12_once, _init_l_Array_filterMap__replicate___auto__7___closed__12);
v___x_188_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_189_ = lean_array_push(v___x_188_, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__17(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_201_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_202_ = lean_array_push(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__18(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_203_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__17, &l_Array_filterMap__replicate___auto__7___closed__17_once, _init_l_Array_filterMap__replicate___auto__7___closed__17);
v___x_204_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__15));
v___x_205_ = lean_box(2);
v___x_206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
lean_ctor_set(v___x_206_, 2, v___x_203_);
return v___x_206_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__19(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__18, &l_Array_filterMap__replicate___auto__7___closed__18_once, _init_l_Array_filterMap__replicate___auto__7___closed__18);
v___x_208_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__13, &l_Array_filterMap__replicate___auto__7___closed__13_once, _init_l_Array_filterMap__replicate___auto__7___closed__13);
v___x_209_ = lean_array_push(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__20(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_211_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__19, &l_Array_filterMap__replicate___auto__7___closed__19_once, _init_l_Array_filterMap__replicate___auto__7___closed__19);
v___x_212_ = lean_array_push(v___x_211_, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__21(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_214_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__20, &l_Array_filterMap__replicate___auto__7___closed__20_once, _init_l_Array_filterMap__replicate___auto__7___closed__20);
v___x_215_ = lean_array_push(v___x_214_, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__22(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_217_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__21, &l_Array_filterMap__replicate___auto__7___closed__21_once, _init_l_Array_filterMap__replicate___auto__7___closed__21);
v___x_218_ = lean_array_push(v___x_217_, v___x_216_);
return v___x_218_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__23(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_220_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__22, &l_Array_filterMap__replicate___auto__7___closed__22_once, _init_l_Array_filterMap__replicate___auto__7___closed__22);
v___x_221_ = lean_array_push(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__24(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_222_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__23, &l_Array_filterMap__replicate___auto__7___closed__23_once, _init_l_Array_filterMap__replicate___auto__7___closed__23);
v___x_223_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__11));
v___x_224_ = lean_box(2);
v___x_225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_223_);
lean_ctor_set(v___x_225_, 2, v___x_222_);
return v___x_225_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__25(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__24, &l_Array_filterMap__replicate___auto__7___closed__24_once, _init_l_Array_filterMap__replicate___auto__7___closed__24);
v___x_227_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_228_ = lean_array_push(v___x_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__26(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_229_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__25, &l_Array_filterMap__replicate___auto__7___closed__25_once, _init_l_Array_filterMap__replicate___auto__7___closed__25);
v___x_230_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__9));
v___x_231_ = lean_box(2);
v___x_232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
lean_ctor_set(v___x_232_, 2, v___x_229_);
return v___x_232_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__27(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__26, &l_Array_filterMap__replicate___auto__7___closed__26_once, _init_l_Array_filterMap__replicate___auto__7___closed__26);
v___x_234_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_235_ = lean_array_push(v___x_234_, v___x_233_);
return v___x_235_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__28(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_236_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__27, &l_Array_filterMap__replicate___auto__7___closed__27_once, _init_l_Array_filterMap__replicate___auto__7___closed__27);
v___x_237_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__7));
v___x_238_ = lean_box(2);
v___x_239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_236_);
return v___x_239_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__29(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__28, &l_Array_filterMap__replicate___auto__7___closed__28_once, _init_l_Array_filterMap__replicate___auto__7___closed__28);
v___x_241_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_242_ = lean_array_push(v___x_241_, v___x_240_);
return v___x_242_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__30(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_243_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__29, &l_Array_filterMap__replicate___auto__7___closed__29_once, _init_l_Array_filterMap__replicate___auto__7___closed__29);
v___x_244_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__4));
v___x_245_ = lean_box(2);
v___x_246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
lean_ctor_set(v___x_246_, 2, v___x_243_);
return v___x_246_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7(void){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__30, &l_Array_filterMap__replicate___auto__7___closed__30_once, _init_l_Array_filterMap__replicate___auto__7___closed__30);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object* v_x_248_, lean_object* v_h__1_249_, lean_object* v_h__2_250_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object* v_00_u03b2_255_, lean_object* v_motive_256_, lean_object* v_x_257_, lean_object* v_h__1_258_, lean_object* v_h__2_259_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(lean_object* v_i_264_, lean_object* v_h__1_265_, lean_object* v_h__2_266_){
_start:
{
lean_object* v_zero_267_; uint8_t v_isZero_268_; 
v_zero_267_ = lean_unsigned_to_nat(0u);
v_isZero_268_ = lean_nat_dec_eq(v_i_264_, v_zero_267_);
if (v_isZero_268_ == 1)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v_h__2_266_);
v___x_269_ = lean_box(0);
v___x_270_ = lean_apply_1(v_h__1_265_, v___x_269_);
return v___x_270_;
}
else
{
lean_object* v_one_271_; lean_object* v_n_272_; lean_object* v___x_273_; 
lean_dec(v_h__1_265_);
v_one_271_ = lean_unsigned_to_nat(1u);
v_n_272_ = lean_nat_sub(v_i_264_, v_one_271_);
v___x_273_ = lean_apply_1(v_h__2_266_, v_n_272_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg___boxed(lean_object* v_i_274_, lean_object* v_h__1_275_, lean_object* v_h__2_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(v_i_274_, v_h__1_275_, v_h__2_276_);
lean_dec(v_i_274_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(lean_object* v_motive_278_, lean_object* v_i_279_, lean_object* v_h__1_280_, lean_object* v_h__2_281_){
_start:
{
lean_object* v_zero_282_; uint8_t v_isZero_283_; 
v_zero_282_ = lean_unsigned_to_nat(0u);
v_isZero_283_ = lean_nat_dec_eq(v_i_279_, v_zero_282_);
if (v_isZero_283_ == 1)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec(v_h__2_281_);
v___x_284_ = lean_box(0);
v___x_285_ = lean_apply_1(v_h__1_280_, v___x_284_);
return v___x_285_;
}
else
{
lean_object* v_one_286_; lean_object* v_n_287_; lean_object* v___x_288_; 
lean_dec(v_h__1_280_);
v_one_286_ = lean_unsigned_to_nat(1u);
v_n_287_ = lean_nat_sub(v_i_279_, v_one_286_);
v___x_288_ = lean_apply_1(v_h__2_281_, v_n_287_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___boxed(lean_object* v_motive_289_, lean_object* v_i_290_, lean_object* v_h__1_291_, lean_object* v_h__2_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(v_motive_289_, v_i_290_, v_h__1_291_, v_h__2_292_);
lean_dec(v_i_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object* v_i_294_, lean_object* v_h__1_295_, lean_object* v_h__2_296_){
_start:
{
lean_object* v_zero_297_; uint8_t v_isZero_298_; 
v_zero_297_ = lean_unsigned_to_nat(0u);
v_isZero_298_ = lean_nat_dec_eq(v_i_294_, v_zero_297_);
if (v_isZero_298_ == 1)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v_h__2_296_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_apply_1(v_h__1_295_, v___x_299_);
return v___x_300_;
}
else
{
lean_object* v_one_301_; lean_object* v_n_302_; lean_object* v___x_303_; 
lean_dec(v_h__1_295_);
v_one_301_ = lean_unsigned_to_nat(1u);
v_n_302_ = lean_nat_sub(v_i_294_, v_one_301_);
v___x_303_ = lean_apply_1(v_h__2_296_, v_n_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object* v_i_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_304_, v_h__1_305_, v_h__2_306_);
lean_dec(v_i_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object* v_motive_308_, lean_object* v_i_309_, lean_object* v_h__1_310_, lean_object* v_h__2_311_){
_start:
{
lean_object* v_zero_312_; uint8_t v_isZero_313_; 
v_zero_312_ = lean_unsigned_to_nat(0u);
v_isZero_313_ = lean_nat_dec_eq(v_i_309_, v_zero_312_);
if (v_isZero_313_ == 1)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_h__2_311_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_apply_1(v_h__1_310_, v___x_314_);
return v___x_315_;
}
else
{
lean_object* v_one_316_; lean_object* v_n_317_; lean_object* v___x_318_; 
lean_dec(v_h__1_310_);
v_one_316_ = lean_unsigned_to_nat(1u);
v_n_317_ = lean_nat_sub(v_i_309_, v_one_316_);
v___x_318_ = lean_apply_1(v_h__2_311_, v_n_317_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object* v_motive_319_, lean_object* v_i_320_, lean_object* v_h__1_321_, lean_object* v_h__2_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(v_motive_319_, v_i_320_, v_h__1_321_, v_h__2_322_);
lean_dec(v_i_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_324_, lean_object* v_h__1_325_, lean_object* v_h__2_326_){
_start:
{
lean_object* v_zero_327_; uint8_t v_isZero_328_; 
v_zero_327_ = lean_unsigned_to_nat(0u);
v_isZero_328_ = lean_nat_dec_eq(v_x_324_, v_zero_327_);
if (v_isZero_328_ == 1)
{
lean_object* v___x_329_; 
lean_dec(v_h__2_326_);
v___x_329_ = lean_apply_1(v_h__1_325_, lean_box(0));
return v___x_329_;
}
else
{
lean_object* v_one_330_; lean_object* v_n_331_; lean_object* v___x_332_; 
lean_dec(v_h__1_325_);
v_one_330_ = lean_unsigned_to_nat(1u);
v_n_331_ = lean_nat_sub(v_x_324_, v_one_330_);
v___x_332_ = lean_apply_2(v_h__2_326_, v_n_331_, lean_box(0));
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_333_, lean_object* v_h__1_334_, lean_object* v_h__2_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(v_x_333_, v_h__1_334_, v_h__2_335_);
lean_dec(v_x_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_337_, lean_object* v_xs_338_, lean_object* v_motive_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_h__1_342_, lean_object* v_h__2_343_){
_start:
{
lean_object* v_zero_344_; uint8_t v_isZero_345_; 
v_zero_344_ = lean_unsigned_to_nat(0u);
v_isZero_345_ = lean_nat_dec_eq(v_x_340_, v_zero_344_);
if (v_isZero_345_ == 1)
{
lean_object* v___x_346_; 
lean_dec(v_h__2_343_);
v___x_346_ = lean_apply_1(v_h__1_342_, lean_box(0));
return v___x_346_;
}
else
{
lean_object* v_one_347_; lean_object* v_n_348_; lean_object* v___x_349_; 
lean_dec(v_h__1_342_);
v_one_347_ = lean_unsigned_to_nat(1u);
v_n_348_ = lean_nat_sub(v_x_340_, v_one_347_);
v___x_349_ = lean_apply_2(v_h__2_343_, v_n_348_, lean_box(0));
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_350_, lean_object* v_xs_351_, lean_object* v_motive_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_h__1_355_, lean_object* v_h__2_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_350_, v_xs_351_, v_motive_352_, v_x_353_, v_x_354_, v_h__1_355_, v_h__2_356_);
lean_dec(v_x_353_);
lean_dec_ref(v_xs_351_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object* v_x_358_, lean_object* v_h__1_359_, lean_object* v_h__2_360_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object* v_00_u03b2_365_, lean_object* v_motive_366_, lean_object* v_x_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec(v_h__1_368_);
v___x_370_ = lean_box(0);
v___x_371_ = lean_apply_1(v_h__2_369_, v___x_370_);
return v___x_371_;
}
else
{
lean_object* v_val_372_; lean_object* v___x_373_; 
lean_dec(v_h__2_369_);
v_val_372_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_val_372_);
lean_dec_ref_known(v_x_367_, 1);
v___x_373_ = lean_apply_1(v_h__1_368_, v_val_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter___redArg(lean_object* v_x_374_, lean_object* v_h__1_375_, lean_object* v_h__2_376_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter(lean_object* v_00_u03b2_381_, lean_object* v_motive_382_, lean_object* v_x_383_, lean_object* v_h__1_384_, lean_object* v_h__2_385_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v_h__1_384_);
v___x_386_ = lean_box(0);
v___x_387_ = lean_apply_1(v_h__2_385_, v___x_386_);
return v___x_387_;
}
else
{
lean_object* v_val_388_; lean_object* v___x_389_; 
lean_dec(v_h__2_385_);
v_val_388_ = lean_ctor_get(v_x_383_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v_x_383_, 1);
v___x_389_ = lean_apply_1(v_h__1_384_, v_val_388_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___redArg(lean_object* v_x_390_, lean_object* v_h__1_391_, lean_object* v_h__2_392_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_h__2_392_);
v___x_393_ = lean_box(0);
v___x_394_ = lean_apply_1(v_h__1_391_, v___x_393_);
return v___x_394_;
}
else
{
lean_object* v_val_395_; lean_object* v___x_396_; 
lean_dec(v_h__1_391_);
v_val_395_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v_x_390_, 1);
v___x_396_ = lean_apply_1(v_h__2_392_, v_val_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(lean_object* v_00_u03b1_397_, lean_object* v_as_398_, lean_object* v_motive_399_, lean_object* v_x_400_, lean_object* v_h__1_401_, lean_object* v_h__2_402_){
_start:
{
if (lean_obj_tag(v_x_400_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_h__2_402_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_apply_1(v_h__1_401_, v___x_403_);
return v___x_404_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_406_; 
lean_dec(v_h__1_401_);
v_val_405_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v_x_400_, 1);
v___x_406_ = lean_apply_1(v_h__2_402_, v_val_405_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_407_, lean_object* v_as_408_, lean_object* v_motive_409_, lean_object* v_x_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(v_00_u03b1_407_, v_as_408_, v_motive_409_, v_x_410_, v_h__1_411_, v_h__2_412_);
lean_dec_ref(v_as_408_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg___lam__0(lean_object* v_x1_414_, lean_object* v_x2_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_416_, 0, v_x2_415_);
lean_ctor_set(v___x_416_, 1, v_x1_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg(lean_object* v_xs_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_438_ = lean_box(0);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_array_get_size(v_xs_437_);
v___x_441_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_442_ = lean_nat_dec_lt(v___x_439_, v___x_440_);
if (v___x_442_ == 0)
{
lean_dec_ref(v_xs_437_);
return v___x_438_;
}
else
{
lean_object* v___f_443_; uint8_t v___x_444_; 
v___f_443_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_444_ = lean_nat_dec_le(v___x_440_, v___x_440_);
if (v___x_444_ == 0)
{
if (v___x_442_ == 0)
{
lean_dec_ref(v_xs_437_);
return v___x_438_;
}
else
{
size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = ((size_t)0ULL);
v___x_446_ = lean_usize_of_nat(v___x_440_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_441_, v___f_443_, v_xs_437_, v___x_445_, v___x_446_, v___x_438_);
return v___x_447_;
}
}
else
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = ((size_t)0ULL);
v___x_449_ = lean_usize_of_nat(v___x_440_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_441_, v___f_443_, v_xs_437_, v___x_448_, v___x_449_, v___x_438_);
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toListRev(lean_object* v_00_u03b1_451_, lean_object* v_xs_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_453_ = lean_box(0);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_array_get_size(v_xs_452_);
v___x_456_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_457_ = lean_nat_dec_lt(v___x_454_, v___x_455_);
if (v___x_457_ == 0)
{
lean_dec_ref(v_xs_452_);
return v___x_453_;
}
else
{
lean_object* v___f_458_; uint8_t v___x_459_; 
v___f_458_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_459_ = lean_nat_dec_le(v___x_455_, v___x_455_);
if (v___x_459_ == 0)
{
if (v___x_457_ == 0)
{
lean_dec_ref(v_xs_452_);
return v___x_453_;
}
else
{
size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; 
v___x_460_ = ((size_t)0ULL);
v___x_461_ = lean_usize_of_nat(v___x_455_);
v___x_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_456_, v___f_458_, v_xs_452_, v___x_460_, v___x_461_, v___x_453_);
return v___x_462_;
}
}
else
{
size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
v___x_463_ = ((size_t)0ULL);
v___x_464_ = lean_usize_of_nat(v___x_455_);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_456_, v___f_458_, v_xs_452_, v___x_463_, v___x_464_, v___x_453_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(lean_object* v_x_466_, lean_object* v_h__1_467_, lean_object* v_h__2_468_){
_start:
{
lean_object* v_zero_469_; uint8_t v_isZero_470_; 
v_zero_469_ = lean_unsigned_to_nat(0u);
v_isZero_470_ = lean_nat_dec_eq(v_x_466_, v_zero_469_);
if (v_isZero_470_ == 1)
{
lean_object* v___x_471_; 
lean_dec(v_h__1_467_);
v___x_471_ = lean_apply_1(v_h__2_468_, lean_box(0));
return v___x_471_;
}
else
{
lean_object* v_one_472_; lean_object* v_n_473_; lean_object* v___x_474_; 
lean_dec(v_h__2_468_);
v_one_472_ = lean_unsigned_to_nat(1u);
v_n_473_ = lean_nat_sub(v_x_466_, v_one_472_);
v___x_474_ = lean_apply_2(v_h__1_467_, v_n_473_, lean_box(0));
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg___boxed(lean_object* v_x_475_, lean_object* v_h__1_476_, lean_object* v_h__2_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(v_x_475_, v_h__1_476_, v_h__2_477_);
lean_dec(v_x_475_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(lean_object* v_n_479_, lean_object* v_motive_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_h__1_483_, lean_object* v_h__2_484_){
_start:
{
lean_object* v_zero_485_; uint8_t v_isZero_486_; 
v_zero_485_ = lean_unsigned_to_nat(0u);
v_isZero_486_ = lean_nat_dec_eq(v_x_481_, v_zero_485_);
if (v_isZero_486_ == 1)
{
lean_object* v___x_487_; 
lean_dec(v_h__1_483_);
v___x_487_ = lean_apply_1(v_h__2_484_, lean_box(0));
return v___x_487_;
}
else
{
lean_object* v_one_488_; lean_object* v_n_489_; lean_object* v___x_490_; 
lean_dec(v_h__2_484_);
v_one_488_ = lean_unsigned_to_nat(1u);
v_n_489_ = lean_nat_sub(v_x_481_, v_one_488_);
v___x_490_ = lean_apply_2(v_h__1_483_, v_n_489_, lean_box(0));
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___boxed(lean_object* v_n_491_, lean_object* v_motive_492_, lean_object* v_x_493_, lean_object* v_x_494_, lean_object* v_h__1_495_, lean_object* v_h__2_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(v_n_491_, v_motive_492_, v_x_493_, v_x_494_, v_h__1_495_, v_h__2_496_);
lean_dec(v_x_493_);
lean_dec(v_n_491_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec(v_h__1_499_);
v___x_501_ = lean_box(0);
v___x_502_ = lean_apply_1(v_h__2_500_, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_504_; 
lean_dec(v_h__2_500_);
v_val_503_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_x_498_, 1);
v___x_504_ = lean_apply_1(v_h__1_499_, v_val_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_505_, lean_object* v_motive_506_, lean_object* v_x_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_h__1_508_);
v___x_510_ = lean_box(0);
v___x_511_ = lean_apply_1(v_h__2_509_, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v_val_512_; lean_object* v___x_513_; 
lean_dec(v_h__2_509_);
v_val_512_ = lean_ctor_get(v_x_507_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v_x_507_, 1);
v___x_513_ = lean_apply_1(v_h__1_508_, v_val_512_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_514_, lean_object* v_h__1_515_, lean_object* v_h__2_516_){
_start:
{
if (lean_obj_tag(v_opt_514_) == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v_h__1_515_);
v___x_517_ = lean_box(0);
v___x_518_ = lean_apply_1(v_h__2_516_, v___x_517_);
return v___x_518_;
}
else
{
lean_object* v_val_519_; lean_object* v___x_520_; 
lean_dec(v_h__2_516_);
v_val_519_ = lean_ctor_get(v_opt_514_, 0);
lean_inc(v_val_519_);
lean_dec_ref_known(v_opt_514_, 1);
v___x_520_ = lean_apply_1(v_h__1_515_, v_val_519_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_521_, lean_object* v_motive_522_, lean_object* v_opt_523_, lean_object* v_h__1_524_, lean_object* v_h__2_525_){
_start:
{
if (lean_obj_tag(v_opt_523_) == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v_h__1_524_);
v___x_526_ = lean_box(0);
v___x_527_ = lean_apply_1(v_h__2_525_, v___x_526_);
return v___x_527_;
}
else
{
lean_object* v_val_528_; lean_object* v___x_529_; 
lean_dec(v_h__2_525_);
v_val_528_ = lean_ctor_get(v_opt_523_, 0);
lean_inc(v_val_528_);
lean_dec_ref_known(v_opt_523_, 1);
v___x_529_ = lean_apply_1(v_h__1_524_, v_val_528_);
return v___x_529_;
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
