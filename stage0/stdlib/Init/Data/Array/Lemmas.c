// Lean compiler output
// Module: Init.Data.Array.Lemmas
// Imports: public import Init.Data.List.ToArray import all Init.Data.List.Control import all Init.Data.Array.Basic import all Init.Data.Array.Bootstrap public import Init.Data.Nat.Lemmas public import Init.Data.Nat.MinMax import Init.ByCases import Init.Data.Array.DecidableEq import Init.Data.Bool import Init.Data.Fin.Lemmas import Init.Data.List.Find import Init.Data.List.Nat.Basic import Init.Data.List.Nat.Modify import Init.Data.List.Nat.TakeDrop import Init.Data.List.Range import Init.Data.List.Zip import Init.Data.Nat.Linear import Init.Data.Nat.Simproc import Init.Data.Option.Lemmas import Init.Data.Prod import Init.Omega import Init.TacticsExtra
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
uint8_t l_Nat_decidableBallLT___redArg(lean_object*, lean_object*);
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
uint8_t l_Nat_decidableExistsLT_x27___redArg(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableForallForallMemOfDecidablePred___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableForallForallMemOfDecidablePred(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(lean_object* v_xs_1_, lean_object* v_inst_2_, lean_object* v_n_3_, lean_object* v_h_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_array_fget_borrowed(v_xs_1_, v_n_3_);
lean_inc(v___x_5_);
v___x_6_ = lean_apply_1(v_inst_2_, v___x_5_);
v___x_7_ = lean_unbox(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(lean_object* v_xs_8_, lean_object* v_inst_9_, lean_object* v_n_10_, lean_object* v_h_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(v_xs_8_, v_inst_9_, v_n_10_, v_h_11_);
lean_dec(v_n_10_);
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
v___x_18_ = l_Nat_decidableBallLT___redArg(v___x_17_, v___f_16_);
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
LEAN_EXPORT uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0(lean_object* v_xs_34_, lean_object* v_inst_35_, lean_object* v_m_36_, lean_object* v_h_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_38_ = lean_array_fget_borrowed(v_xs_34_, v_m_36_);
lean_inc(v___x_38_);
v___x_39_ = lean_apply_1(v_inst_35_, v___x_38_);
v___x_40_ = lean_unbox(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0___boxed(lean_object* v_xs_41_, lean_object* v_inst_42_, lean_object* v_m_43_, lean_object* v_h_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0(v_xs_41_, v_inst_42_, v_m_43_, v_h_44_);
lean_dec(v_m_43_);
lean_dec_ref(v_xs_41_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(lean_object* v_xs_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v___f_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
lean_inc_ref(v_xs_47_);
v___f_49_ = lean_alloc_closure((void*)(l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_49_, 0, v_xs_47_);
lean_closure_set(v___f_49_, 1, v_inst_48_);
v___x_50_ = lean_array_get_size(v_xs_47_);
lean_dec_ref(v_xs_47_);
v___x_51_ = l_Nat_decidableExistsLT_x27___redArg(v___x_50_, v___f_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___boxed(lean_object* v_xs_52_, lean_object* v_inst_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_xs_52_, v_inst_53_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableExistsAndMemOfDecidablePred(lean_object* v_00_u03b1_56_, lean_object* v_xs_57_, lean_object* v_p_58_, lean_object* v_inst_59_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_xs_57_, v_inst_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableExistsAndMemOfDecidablePred___boxed(lean_object* v_00_u03b1_61_, lean_object* v_xs_62_, lean_object* v_p_63_, lean_object* v_inst_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Array_instDecidableExistsAndMemOfDecidablePred(v_00_u03b1_61_, v_xs_62_, v_p_63_, v_inst_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_mapA_match__1_splitter___redArg(lean_object* v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_h__2_69_);
v___x_70_ = lean_box(0);
v___x_71_ = lean_apply_1(v_h__1_68_, v___x_70_);
return v___x_71_;
}
else
{
lean_object* v_head_72_; lean_object* v_tail_73_; lean_object* v___x_74_; 
lean_dec(v_h__1_68_);
v_head_72_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_head_72_);
v_tail_73_ = lean_ctor_get(v_x_67_, 1);
lean_inc(v_tail_73_);
lean_dec_ref(v_x_67_);
v___x_74_ = lean_apply_2(v_h__2_69_, v_head_72_, v_tail_73_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_mapA_match__1_splitter(lean_object* v_00_u03b1_75_, lean_object* v_motive_76_, lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Init_Data_Array_Lemmas_0__List_mapA_match__1_splitter___redArg(v_x_77_, v_h__1_78_, v_h__2_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_){
_start:
{
if (v_____do__lift_81_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_h__1_82_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_h__2_83_, v___x_84_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_h__2_83_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_apply_1(v_h__1_82_, v___x_86_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
uint8_t v_____do__lift_22__boxed_91_; lean_object* v_res_92_; 
v_____do__lift_22__boxed_91_ = lean_unbox(v_____do__lift_88_);
v_res_92_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(v_____do__lift_22__boxed_91_, v_h__1_89_, v_h__2_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(lean_object* v_motive_93_, uint8_t v_____do__lift_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(v_____do__lift_94_, v_h__1_95_, v_h__2_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_98_, lean_object* v_____do__lift_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_){
_start:
{
uint8_t v_____do__lift_33__boxed_102_; lean_object* v_res_103_; 
v_____do__lift_33__boxed_102_ = lean_unbox(v_____do__lift_99_);
v_res_103_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(v_motive_98_, v_____do__lift_33__boxed_102_, v_h__1_100_, v_h__2_101_);
return v_res_103_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_104_, lean_object* v_a_105_, lean_object* v_as_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = l_Array_contains___redArg(v_inst_104_, v_as_106_, v_a_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_108_, lean_object* v_a_109_, lean_object* v_as_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Array_instDecidableMemOfLawfulBEq___redArg(v_inst_108_, v_a_109_, v_as_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_a_116_, lean_object* v_as_117_){
_start:
{
uint8_t v___x_118_; 
v___x_118_ = l_Array_contains___redArg(v_inst_114_, v_as_117_, v_a_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_a_122_, lean_object* v_as_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Array_instDecidableMemOfLawfulBEq(v_00_u03b1_119_, v_inst_120_, v_inst_121_, v_a_122_, v_as_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_){
_start:
{
lean_object* v_zero_129_; uint8_t v_isZero_130_; 
v_zero_129_ = lean_unsigned_to_nat(0u);
v_isZero_130_ = lean_nat_dec_eq(v_x_126_, v_zero_129_);
if (v_isZero_130_ == 1)
{
lean_object* v___x_131_; 
lean_dec(v_h__2_128_);
v___x_131_ = lean_apply_1(v_h__1_127_, lean_box(0));
return v___x_131_;
}
else
{
lean_object* v_one_132_; lean_object* v_n_133_; lean_object* v___x_134_; 
lean_dec(v_h__1_127_);
v_one_132_ = lean_unsigned_to_nat(1u);
v_n_133_ = lean_nat_sub(v_x_126_, v_one_132_);
v___x_134_ = lean_apply_2(v_h__2_128_, v_n_133_, lean_box(0));
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(v_x_135_, v_h__1_136_, v_h__2_137_);
lean_dec(v_x_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_139_, lean_object* v_xs_140_, lean_object* v_motive_141_, lean_object* v_x_142_, lean_object* v_x_143_, lean_object* v_h__1_144_, lean_object* v_h__2_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(v_x_142_, v_h__1_144_, v_h__2_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_147_, lean_object* v_xs_148_, lean_object* v_motive_149_, lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_h__1_152_, lean_object* v_h__2_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_147_, v_xs_148_, v_motive_149_, v_x_150_, v_x_151_, v_h__1_152_, v_h__2_153_);
lean_dec(v_x_150_);
lean_dec_ref(v_xs_148_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_){
_start:
{
if (lean_obj_tag(v_____do__lift_155_) == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec(v_h__1_156_);
v___x_158_ = lean_box(0);
v___x_159_ = lean_apply_1(v_h__2_157_, v___x_158_);
return v___x_159_;
}
else
{
lean_object* v_val_160_; lean_object* v___x_161_; 
lean_dec(v_h__2_157_);
v_val_160_ = lean_ctor_get(v_____do__lift_155_, 0);
lean_inc(v_val_160_);
lean_dec_ref(v_____do__lift_155_);
v___x_161_ = lean_apply_1(v_h__1_156_, v_val_160_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter(lean_object* v_00_u03b2_162_, lean_object* v_motive_163_, lean_object* v_____do__lift_164_, lean_object* v_h__1_165_, lean_object* v_h__2_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter___redArg(v_____do__lift_164_, v_h__1_165_, v_h__2_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_h__2_170_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_apply_1(v_h__1_169_, v___x_171_);
return v___x_172_;
}
else
{
lean_object* v_val_173_; lean_object* v___x_174_; 
lean_dec(v_h__1_169_);
v_val_173_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_val_173_);
lean_dec_ref(v_x_168_);
v___x_174_ = lean_apply_1(v_h__2_170_, v_val_173_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_175_, lean_object* v_motive_176_, lean_object* v_x_177_, lean_object* v_h__1_178_, lean_object* v_h__2_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___redArg(v_x_177_, v_h__1_178_, v_h__2_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter___redArg(lean_object* v_x_181_, lean_object* v_h__1_182_, lean_object* v_h__2_183_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_h__2_183_);
v___x_184_ = lean_box(0);
v___x_185_ = lean_apply_1(v_h__1_182_, v___x_184_);
return v___x_185_;
}
else
{
lean_object* v_val_186_; lean_object* v___x_187_; 
lean_dec(v_h__1_182_);
v_val_186_ = lean_ctor_get(v_x_181_, 0);
lean_inc(v_val_186_);
lean_dec_ref(v_x_181_);
v___x_187_ = lean_apply_1(v_h__2_183_, v_val_186_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter(lean_object* v_00_u03b2_188_, lean_object* v_motive_189_, lean_object* v_x_190_, lean_object* v_h__1_191_, lean_object* v_h__2_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter___redArg(v_x_190_, v_h__1_191_, v_h__2_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__12(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__10));
v___x_221_ = l_Lean_mkAtom(v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__13(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__12, &l_Array_filterMap__replicate___auto__7___closed__12_once, _init_l_Array_filterMap__replicate___auto__7___closed__12);
v___x_223_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_224_ = lean_array_push(v___x_223_, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__17(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_236_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_237_ = lean_array_push(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__18(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_238_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__17, &l_Array_filterMap__replicate___auto__7___closed__17_once, _init_l_Array_filterMap__replicate___auto__7___closed__17);
v___x_239_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__15));
v___x_240_ = lean_box(2);
v___x_241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_238_);
return v___x_241_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__19(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__18, &l_Array_filterMap__replicate___auto__7___closed__18_once, _init_l_Array_filterMap__replicate___auto__7___closed__18);
v___x_243_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__13, &l_Array_filterMap__replicate___auto__7___closed__13_once, _init_l_Array_filterMap__replicate___auto__7___closed__13);
v___x_244_ = lean_array_push(v___x_243_, v___x_242_);
return v___x_244_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__20(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_246_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__19, &l_Array_filterMap__replicate___auto__7___closed__19_once, _init_l_Array_filterMap__replicate___auto__7___closed__19);
v___x_247_ = lean_array_push(v___x_246_, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__21(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_249_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__20, &l_Array_filterMap__replicate___auto__7___closed__20_once, _init_l_Array_filterMap__replicate___auto__7___closed__20);
v___x_250_ = lean_array_push(v___x_249_, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__22(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_252_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__21, &l_Array_filterMap__replicate___auto__7___closed__21_once, _init_l_Array_filterMap__replicate___auto__7___closed__21);
v___x_253_ = lean_array_push(v___x_252_, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__23(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_255_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__22, &l_Array_filterMap__replicate___auto__7___closed__22_once, _init_l_Array_filterMap__replicate___auto__7___closed__22);
v___x_256_ = lean_array_push(v___x_255_, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__24(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_257_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__23, &l_Array_filterMap__replicate___auto__7___closed__23_once, _init_l_Array_filterMap__replicate___auto__7___closed__23);
v___x_258_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__11));
v___x_259_ = lean_box(2);
v___x_260_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_258_);
lean_ctor_set(v___x_260_, 2, v___x_257_);
return v___x_260_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__25(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__24, &l_Array_filterMap__replicate___auto__7___closed__24_once, _init_l_Array_filterMap__replicate___auto__7___closed__24);
v___x_262_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_263_ = lean_array_push(v___x_262_, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__26(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__25, &l_Array_filterMap__replicate___auto__7___closed__25_once, _init_l_Array_filterMap__replicate___auto__7___closed__25);
v___x_265_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__9));
v___x_266_ = lean_box(2);
v___x_267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_264_);
return v___x_267_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__27(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__26, &l_Array_filterMap__replicate___auto__7___closed__26_once, _init_l_Array_filterMap__replicate___auto__7___closed__26);
v___x_269_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_270_ = lean_array_push(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__28(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__27, &l_Array_filterMap__replicate___auto__7___closed__27_once, _init_l_Array_filterMap__replicate___auto__7___closed__27);
v___x_272_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__7));
v___x_273_ = lean_box(2);
v___x_274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_271_);
return v___x_274_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__29(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__28, &l_Array_filterMap__replicate___auto__7___closed__28_once, _init_l_Array_filterMap__replicate___auto__7___closed__28);
v___x_276_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_277_ = lean_array_push(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__30(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_278_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__29, &l_Array_filterMap__replicate___auto__7___closed__29_once, _init_l_Array_filterMap__replicate___auto__7___closed__29);
v___x_279_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__4));
v___x_280_ = lean_box(2);
v___x_281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_278_);
return v___x_281_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__30, &l_Array_filterMap__replicate___auto__7___closed__30_once, _init_l_Array_filterMap__replicate___auto__7___closed__30);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object* v_x_283_, lean_object* v_h__1_284_, lean_object* v_h__2_285_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v_h__2_285_);
v___x_286_ = lean_box(0);
v___x_287_ = lean_apply_1(v_h__1_284_, v___x_286_);
return v___x_287_;
}
else
{
lean_object* v_val_288_; lean_object* v___x_289_; 
lean_dec(v_h__1_284_);
v_val_288_ = lean_ctor_get(v_x_283_, 0);
lean_inc(v_val_288_);
lean_dec_ref(v_x_283_);
v___x_289_ = lean_apply_1(v_h__2_285_, v_val_288_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object* v_00_u03b2_290_, lean_object* v_motive_291_, lean_object* v_x_292_, lean_object* v_h__1_293_, lean_object* v_h__2_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(v_x_292_, v_h__1_293_, v_h__2_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(lean_object* v_i_296_, lean_object* v_h__1_297_, lean_object* v_h__2_298_){
_start:
{
lean_object* v_zero_299_; uint8_t v_isZero_300_; 
v_zero_299_ = lean_unsigned_to_nat(0u);
v_isZero_300_ = lean_nat_dec_eq(v_i_296_, v_zero_299_);
if (v_isZero_300_ == 1)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_h__2_298_);
v___x_301_ = lean_box(0);
v___x_302_ = lean_apply_1(v_h__1_297_, v___x_301_);
return v___x_302_;
}
else
{
lean_object* v_one_303_; lean_object* v_n_304_; lean_object* v___x_305_; 
lean_dec(v_h__1_297_);
v_one_303_ = lean_unsigned_to_nat(1u);
v_n_304_ = lean_nat_sub(v_i_296_, v_one_303_);
v___x_305_ = lean_apply_1(v_h__2_298_, v_n_304_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg___boxed(lean_object* v_i_306_, lean_object* v_h__1_307_, lean_object* v_h__2_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(v_i_306_, v_h__1_307_, v_h__2_308_);
lean_dec(v_i_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(lean_object* v_motive_310_, lean_object* v_i_311_, lean_object* v_h__1_312_, lean_object* v_h__2_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(v_i_311_, v_h__1_312_, v_h__2_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___boxed(lean_object* v_motive_315_, lean_object* v_i_316_, lean_object* v_h__1_317_, lean_object* v_h__2_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(v_motive_315_, v_i_316_, v_h__1_317_, v_h__2_318_);
lean_dec(v_i_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_h__1_322_, lean_object* v_h__2_323_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg___boxed(lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_h__1_332_, lean_object* v_h__2_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(v_x_330_, v_x_331_, v_h__1_332_, v_h__2_333_);
lean_dec(v_x_330_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter(lean_object* v_00_u03b1_335_, lean_object* v_motive_336_, lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_h__1_339_, lean_object* v_h__2_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(v_x_337_, v_x_338_, v_h__1_339_, v_h__2_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___boxed(lean_object* v_00_u03b1_342_, lean_object* v_motive_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_h__1_346_, lean_object* v_h__2_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter(v_00_u03b1_342_, v_motive_343_, v_x_344_, v_x_345_, v_h__1_346_, v_h__2_347_);
lean_dec(v_x_344_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object* v_i_349_, lean_object* v_h__1_350_, lean_object* v_h__2_351_){
_start:
{
lean_object* v_zero_352_; uint8_t v_isZero_353_; 
v_zero_352_ = lean_unsigned_to_nat(0u);
v_isZero_353_ = lean_nat_dec_eq(v_i_349_, v_zero_352_);
if (v_isZero_353_ == 1)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_h__2_351_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_apply_1(v_h__1_350_, v___x_354_);
return v___x_355_;
}
else
{
lean_object* v_one_356_; lean_object* v_n_357_; lean_object* v___x_358_; 
lean_dec(v_h__1_350_);
v_one_356_ = lean_unsigned_to_nat(1u);
v_n_357_ = lean_nat_sub(v_i_349_, v_one_356_);
v___x_358_ = lean_apply_1(v_h__2_351_, v_n_357_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object* v_i_359_, lean_object* v_h__1_360_, lean_object* v_h__2_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_359_, v_h__1_360_, v_h__2_361_);
lean_dec(v_i_359_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object* v_motive_363_, lean_object* v_i_364_, lean_object* v_h__1_365_, lean_object* v_h__2_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_364_, v_h__1_365_, v_h__2_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object* v_motive_368_, lean_object* v_i_369_, lean_object* v_h__1_370_, lean_object* v_h__2_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(v_motive_368_, v_i_369_, v_h__1_370_, v_h__2_371_);
lean_dec(v_i_369_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object* v_i_373_, lean_object* v_h__1_374_, lean_object* v_h__2_375_){
_start:
{
lean_object* v_zero_376_; uint8_t v_isZero_377_; 
v_zero_376_ = lean_unsigned_to_nat(0u);
v_isZero_377_ = lean_nat_dec_eq(v_i_373_, v_zero_376_);
if (v_isZero_377_ == 1)
{
lean_object* v___x_378_; 
lean_dec(v_h__2_375_);
v___x_378_ = lean_apply_1(v_h__1_374_, lean_box(0));
return v___x_378_;
}
else
{
lean_object* v_one_379_; lean_object* v_n_380_; lean_object* v___x_381_; 
lean_dec(v_h__1_374_);
v_one_379_ = lean_unsigned_to_nat(1u);
v_n_380_ = lean_nat_sub(v_i_373_, v_one_379_);
v___x_381_ = lean_apply_2(v_h__2_375_, v_n_380_, lean_box(0));
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object* v_i_382_, lean_object* v_h__1_383_, lean_object* v_h__2_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(v_i_382_, v_h__1_383_, v_h__2_384_);
lean_dec(v_i_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(lean_object* v_00_u03b1_386_, lean_object* v_as_387_, lean_object* v_motive_388_, lean_object* v_i_389_, lean_object* v_h_390_, lean_object* v_h__1_391_, lean_object* v_h__2_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(v_i_389_, v_h__1_391_, v_h__2_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_394_, lean_object* v_as_395_, lean_object* v_motive_396_, lean_object* v_i_397_, lean_object* v_h_398_, lean_object* v_h__1_399_, lean_object* v_h__2_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(v_00_u03b1_394_, v_as_395_, v_motive_396_, v_i_397_, v_h_398_, v_h__1_399_, v_h__2_400_);
lean_dec(v_i_397_);
lean_dec_ref(v_as_395_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object* v_x_402_, lean_object* v_h__1_403_, lean_object* v_h__2_404_){
_start:
{
if (lean_obj_tag(v_x_402_) == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v_h__1_403_);
v___x_405_ = lean_box(0);
v___x_406_ = lean_apply_1(v_h__2_404_, v___x_405_);
return v___x_406_;
}
else
{
lean_object* v_val_407_; lean_object* v___x_408_; 
lean_dec(v_h__2_404_);
v_val_407_ = lean_ctor_get(v_x_402_, 0);
lean_inc(v_val_407_);
lean_dec_ref(v_x_402_);
v___x_408_ = lean_apply_1(v_h__1_403_, v_val_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object* v_00_u03b2_409_, lean_object* v_motive_410_, lean_object* v_x_411_, lean_object* v_h__1_412_, lean_object* v_h__2_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(v_x_411_, v_h__1_412_, v_h__2_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter___redArg(lean_object* v_x_415_, lean_object* v_h__1_416_, lean_object* v_h__2_417_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_h__1_416_);
v___x_418_ = lean_box(0);
v___x_419_ = lean_apply_1(v_h__2_417_, v___x_418_);
return v___x_419_;
}
else
{
lean_object* v_val_420_; lean_object* v___x_421_; 
lean_dec(v_h__2_417_);
v_val_420_ = lean_ctor_get(v_x_415_, 0);
lean_inc(v_val_420_);
lean_dec_ref(v_x_415_);
v___x_421_ = lean_apply_1(v_h__1_416_, v_val_420_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter(lean_object* v_00_u03b2_422_, lean_object* v_motive_423_, lean_object* v_x_424_, lean_object* v_h__1_425_, lean_object* v_h__2_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter___redArg(v_x_424_, v_h__1_425_, v_h__2_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___redArg(lean_object* v_x_428_, lean_object* v_h__1_429_, lean_object* v_h__2_430_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec(v_h__2_430_);
v___x_431_ = lean_box(0);
v___x_432_ = lean_apply_1(v_h__1_429_, v___x_431_);
return v___x_432_;
}
else
{
lean_object* v_val_433_; lean_object* v___x_434_; 
lean_dec(v_h__1_429_);
v_val_433_ = lean_ctor_get(v_x_428_, 0);
lean_inc(v_val_433_);
lean_dec_ref(v_x_428_);
v___x_434_ = lean_apply_1(v_h__2_430_, v_val_433_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(lean_object* v_00_u03b1_435_, lean_object* v_as_436_, lean_object* v_motive_437_, lean_object* v_x_438_, lean_object* v_h__1_439_, lean_object* v_h__2_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___redArg(v_x_438_, v_h__1_439_, v_h__2_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_442_, lean_object* v_as_443_, lean_object* v_motive_444_, lean_object* v_x_445_, lean_object* v_h__1_446_, lean_object* v_h__2_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(v_00_u03b1_442_, v_as_443_, v_motive_444_, v_x_445_, v_h__1_446_, v_h__2_447_);
lean_dec_ref(v_as_443_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg___lam__0(lean_object* v_x1_449_, lean_object* v_x2_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v_x2_450_);
lean_ctor_set(v___x_451_, 1, v_x1_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg(lean_object* v_xs_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_473_ = lean_box(0);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_array_get_size(v_xs_472_);
v___x_476_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_477_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
if (v___x_477_ == 0)
{
lean_dec_ref(v_xs_472_);
return v___x_473_;
}
else
{
lean_object* v___f_478_; uint8_t v___x_479_; 
v___f_478_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_479_ = lean_nat_dec_le(v___x_475_, v___x_475_);
if (v___x_479_ == 0)
{
if (v___x_477_ == 0)
{
lean_dec_ref(v_xs_472_);
return v___x_473_;
}
else
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((size_t)0ULL);
v___x_481_ = lean_usize_of_nat(v___x_475_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_476_, v___f_478_, v_xs_472_, v___x_480_, v___x_481_, v___x_473_);
return v___x_482_;
}
}
else
{
size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; 
v___x_483_ = ((size_t)0ULL);
v___x_484_ = lean_usize_of_nat(v___x_475_);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_476_, v___f_478_, v_xs_472_, v___x_483_, v___x_484_, v___x_473_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toListRev(lean_object* v_00_u03b1_486_, lean_object* v_xs_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_488_ = lean_box(0);
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = lean_array_get_size(v_xs_487_);
v___x_491_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_492_ = lean_nat_dec_lt(v___x_489_, v___x_490_);
if (v___x_492_ == 0)
{
lean_dec_ref(v_xs_487_);
return v___x_488_;
}
else
{
lean_object* v___f_493_; uint8_t v___x_494_; 
v___f_493_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_494_ = lean_nat_dec_le(v___x_490_, v___x_490_);
if (v___x_494_ == 0)
{
if (v___x_492_ == 0)
{
lean_dec_ref(v_xs_487_);
return v___x_488_;
}
else
{
size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; 
v___x_495_ = ((size_t)0ULL);
v___x_496_ = lean_usize_of_nat(v___x_490_);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_491_, v___f_493_, v_xs_487_, v___x_495_, v___x_496_, v___x_488_);
return v___x_497_;
}
}
else
{
size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v___x_498_ = ((size_t)0ULL);
v___x_499_ = lean_usize_of_nat(v___x_490_);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_491_, v___f_493_, v_xs_487_, v___x_498_, v___x_499_, v___x_488_);
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(lean_object* v_x_501_, lean_object* v_h__1_502_, lean_object* v_h__2_503_){
_start:
{
lean_object* v_zero_504_; uint8_t v_isZero_505_; 
v_zero_504_ = lean_unsigned_to_nat(0u);
v_isZero_505_ = lean_nat_dec_eq(v_x_501_, v_zero_504_);
if (v_isZero_505_ == 1)
{
lean_object* v___x_506_; 
lean_dec(v_h__1_502_);
v___x_506_ = lean_apply_1(v_h__2_503_, lean_box(0));
return v___x_506_;
}
else
{
lean_object* v_one_507_; lean_object* v_n_508_; lean_object* v___x_509_; 
lean_dec(v_h__2_503_);
v_one_507_ = lean_unsigned_to_nat(1u);
v_n_508_ = lean_nat_sub(v_x_501_, v_one_507_);
v___x_509_ = lean_apply_2(v_h__1_502_, v_n_508_, lean_box(0));
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg___boxed(lean_object* v_x_510_, lean_object* v_h__1_511_, lean_object* v_h__2_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(v_x_510_, v_h__1_511_, v_h__2_512_);
lean_dec(v_x_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(lean_object* v_n_514_, lean_object* v_motive_515_, lean_object* v_x_516_, lean_object* v_x_517_, lean_object* v_h__1_518_, lean_object* v_h__2_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(v_x_516_, v_h__1_518_, v_h__2_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___boxed(lean_object* v_n_521_, lean_object* v_motive_522_, lean_object* v_x_523_, lean_object* v_x_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(v_n_521_, v_motive_522_, v_x_523_, v_x_524_, v_h__1_525_, v_h__2_526_);
lean_dec(v_x_523_);
lean_dec(v_n_521_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_528_, lean_object* v_h__1_529_, lean_object* v_h__2_530_){
_start:
{
if (lean_obj_tag(v_opt_528_) == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v_h__1_529_);
v___x_531_ = lean_box(0);
v___x_532_ = lean_apply_1(v_h__2_530_, v___x_531_);
return v___x_532_;
}
else
{
lean_object* v_val_533_; lean_object* v___x_534_; 
lean_dec(v_h__2_530_);
v_val_533_ = lean_ctor_get(v_opt_528_, 0);
lean_inc(v_val_533_);
lean_dec_ref(v_opt_528_);
v___x_534_ = lean_apply_1(v_h__1_529_, v_val_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_535_, lean_object* v_motive_536_, lean_object* v_opt_537_, lean_object* v_h__1_538_, lean_object* v_h__2_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter___redArg(v_opt_537_, v_h__1_538_, v_h__2_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_541_, lean_object* v_h__1_542_, lean_object* v_h__2_543_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
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
v_val_546_ = lean_ctor_get(v_x_541_, 0);
lean_inc(v_val_546_);
lean_dec_ref(v_x_541_);
v___x_547_ = lean_apply_1(v_h__1_542_, v_val_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_548_, lean_object* v_motive_549_, lean_object* v_x_550_, lean_object* v_h__1_551_, lean_object* v_h__2_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(v_x_550_, v_h__1_551_, v_h__2_552_);
return v___x_553_;
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
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Linear(builtin);
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
