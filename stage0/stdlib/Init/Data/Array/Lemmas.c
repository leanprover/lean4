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
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_h__2_79_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_1(v_h__1_78_, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v_head_82_; lean_object* v_tail_83_; lean_object* v___x_84_; 
lean_dec(v_h__1_78_);
v_head_82_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_head_82_);
v_tail_83_ = lean_ctor_get(v_x_77_, 1);
lean_inc(v_tail_83_);
lean_dec_ref(v_x_77_);
v___x_84_ = lean_apply_2(v_h__2_79_, v_head_82_, v_tail_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_){
_start:
{
uint8_t v_____do__lift_26__boxed_95_; lean_object* v_res_96_; 
v_____do__lift_26__boxed_95_ = lean_unbox(v_____do__lift_92_);
v_res_96_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(v_____do__lift_26__boxed_95_, v_h__1_93_, v_h__2_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(lean_object* v_motive_97_, uint8_t v_____do__lift_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
if (v_____do__lift_98_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v_h__1_99_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_apply_1(v_h__2_100_, v___x_101_);
return v___x_102_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_h__2_100_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_apply_1(v_h__1_99_, v___x_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_105_, lean_object* v_____do__lift_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_){
_start:
{
uint8_t v_____do__lift_37__boxed_109_; lean_object* v_res_110_; 
v_____do__lift_37__boxed_109_ = lean_unbox(v_____do__lift_106_);
v_res_110_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(v_motive_105_, v_____do__lift_37__boxed_109_, v_h__1_107_, v_h__2_108_);
return v_res_110_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_111_, lean_object* v_a_112_, lean_object* v_as_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = l_Array_contains___redArg(v_inst_111_, v_as_113_, v_a_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_115_, lean_object* v_a_116_, lean_object* v_as_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Array_instDecidableMemOfLawfulBEq___redArg(v_inst_115_, v_a_116_, v_as_117_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_a_123_, lean_object* v_as_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = l_Array_contains___redArg(v_inst_121_, v_as_124_, v_a_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_a_129_, lean_object* v_as_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Array_instDecidableMemOfLawfulBEq(v_00_u03b1_126_, v_inst_127_, v_inst_128_, v_a_129_, v_as_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_){
_start:
{
lean_object* v_zero_136_; uint8_t v_isZero_137_; 
v_zero_136_ = lean_unsigned_to_nat(0u);
v_isZero_137_ = lean_nat_dec_eq(v_x_133_, v_zero_136_);
if (v_isZero_137_ == 1)
{
lean_object* v___x_138_; 
lean_dec(v_h__2_135_);
v___x_138_ = lean_apply_1(v_h__1_134_, lean_box(0));
return v___x_138_;
}
else
{
lean_object* v_one_139_; lean_object* v_n_140_; lean_object* v___x_141_; 
lean_dec(v_h__1_134_);
v_one_139_ = lean_unsigned_to_nat(1u);
v_n_140_ = lean_nat_sub(v_x_133_, v_one_139_);
v___x_141_ = lean_apply_2(v_h__2_135_, v_n_140_, lean_box(0));
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(v_x_142_, v_h__1_143_, v_h__2_144_);
lean_dec(v_x_142_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_146_, lean_object* v_xs_147_, lean_object* v_motive_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_){
_start:
{
lean_object* v_zero_153_; uint8_t v_isZero_154_; 
v_zero_153_ = lean_unsigned_to_nat(0u);
v_isZero_154_ = lean_nat_dec_eq(v_x_149_, v_zero_153_);
if (v_isZero_154_ == 1)
{
lean_object* v___x_155_; 
lean_dec(v_h__2_152_);
v___x_155_ = lean_apply_1(v_h__1_151_, lean_box(0));
return v___x_155_;
}
else
{
lean_object* v_one_156_; lean_object* v_n_157_; lean_object* v___x_158_; 
lean_dec(v_h__1_151_);
v_one_156_ = lean_unsigned_to_nat(1u);
v_n_157_ = lean_nat_sub(v_x_149_, v_one_156_);
v___x_158_ = lean_apply_2(v_h__2_152_, v_n_157_, lean_box(0));
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_159_, lean_object* v_xs_160_, lean_object* v_motive_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_h__1_164_, lean_object* v_h__2_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_159_, v_xs_160_, v_motive_161_, v_x_162_, v_x_163_, v_h__1_164_, v_h__2_165_);
lean_dec(v_x_162_);
lean_dec_ref(v_xs_160_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_167_, lean_object* v_h__1_168_, lean_object* v_h__2_169_){
_start:
{
if (lean_obj_tag(v_____do__lift_167_) == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec(v_h__1_168_);
v___x_170_ = lean_box(0);
v___x_171_ = lean_apply_1(v_h__2_169_, v___x_170_);
return v___x_171_;
}
else
{
lean_object* v_val_172_; lean_object* v___x_173_; 
lean_dec(v_h__2_169_);
v_val_172_ = lean_ctor_get(v_____do__lift_167_, 0);
lean_inc(v_val_172_);
lean_dec_ref(v_____do__lift_167_);
v___x_173_ = lean_apply_1(v_h__1_168_, v_val_172_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter(lean_object* v_00_u03b2_174_, lean_object* v_motive_175_, lean_object* v_____do__lift_176_, lean_object* v_h__1_177_, lean_object* v_h__2_178_){
_start:
{
if (lean_obj_tag(v_____do__lift_176_) == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_h__1_177_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_apply_1(v_h__2_178_, v___x_179_);
return v___x_180_;
}
else
{
lean_object* v_val_181_; lean_object* v___x_182_; 
lean_dec(v_h__2_178_);
v_val_181_ = lean_ctor_get(v_____do__lift_176_, 0);
lean_inc(v_val_181_);
lean_dec_ref(v_____do__lift_176_);
v___x_182_ = lean_apply_1(v_h__1_177_, v_val_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_183_, lean_object* v_h__1_184_, lean_object* v_h__2_185_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v_h__2_185_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_apply_1(v_h__1_184_, v___x_186_);
return v___x_187_;
}
else
{
lean_object* v_val_188_; lean_object* v___x_189_; 
lean_dec(v_h__1_184_);
v_val_188_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_val_188_);
lean_dec_ref(v_x_183_);
v___x_189_ = lean_apply_1(v_h__2_185_, v_val_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_190_, lean_object* v_motive_191_, lean_object* v_x_192_, lean_object* v_h__1_193_, lean_object* v_h__2_194_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_h__2_194_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_apply_1(v_h__1_193_, v___x_195_);
return v___x_196_;
}
else
{
lean_object* v_val_197_; lean_object* v___x_198_; 
lean_dec(v_h__1_193_);
v_val_197_ = lean_ctor_get(v_x_192_, 0);
lean_inc(v_val_197_);
lean_dec_ref(v_x_192_);
v___x_198_ = lean_apply_1(v_h__2_194_, v_val_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter___redArg(lean_object* v_x_199_, lean_object* v_h__1_200_, lean_object* v_h__2_201_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_h__2_201_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_apply_1(v_h__1_200_, v___x_202_);
return v___x_203_;
}
else
{
lean_object* v_val_204_; lean_object* v___x_205_; 
lean_dec(v_h__1_200_);
v_val_204_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_val_204_);
lean_dec_ref(v_x_199_);
v___x_205_ = lean_apply_1(v_h__2_201_, v_val_204_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter(lean_object* v_00_u03b2_206_, lean_object* v_motive_207_, lean_object* v_x_208_, lean_object* v_h__1_209_, lean_object* v_h__2_210_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_h__2_210_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_apply_1(v_h__1_209_, v___x_211_);
return v___x_212_;
}
else
{
lean_object* v_val_213_; lean_object* v___x_214_; 
lean_dec(v_h__1_209_);
v_val_213_ = lean_ctor_get(v_x_208_, 0);
lean_inc(v_val_213_);
lean_dec_ref(v_x_208_);
v___x_214_ = lean_apply_1(v_h__2_210_, v_val_213_);
return v___x_214_;
}
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__12(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__10));
v___x_242_ = l_Lean_mkAtom(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__13(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__12, &l_Array_filterMap__replicate___auto__7___closed__12_once, _init_l_Array_filterMap__replicate___auto__7___closed__12);
v___x_244_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_245_ = lean_array_push(v___x_244_, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__17(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_257_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_258_ = lean_array_push(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__18(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_259_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__17, &l_Array_filterMap__replicate___auto__7___closed__17_once, _init_l_Array_filterMap__replicate___auto__7___closed__17);
v___x_260_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__15));
v___x_261_ = lean_box(2);
v___x_262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
lean_ctor_set(v___x_262_, 2, v___x_259_);
return v___x_262_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__19(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__18, &l_Array_filterMap__replicate___auto__7___closed__18_once, _init_l_Array_filterMap__replicate___auto__7___closed__18);
v___x_264_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__13, &l_Array_filterMap__replicate___auto__7___closed__13_once, _init_l_Array_filterMap__replicate___auto__7___closed__13);
v___x_265_ = lean_array_push(v___x_264_, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__20(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_267_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__19, &l_Array_filterMap__replicate___auto__7___closed__19_once, _init_l_Array_filterMap__replicate___auto__7___closed__19);
v___x_268_ = lean_array_push(v___x_267_, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__21(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_270_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__20, &l_Array_filterMap__replicate___auto__7___closed__20_once, _init_l_Array_filterMap__replicate___auto__7___closed__20);
v___x_271_ = lean_array_push(v___x_270_, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__22(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_273_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__21, &l_Array_filterMap__replicate___auto__7___closed__21_once, _init_l_Array_filterMap__replicate___auto__7___closed__21);
v___x_274_ = lean_array_push(v___x_273_, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__23(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__16));
v___x_276_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__22, &l_Array_filterMap__replicate___auto__7___closed__22_once, _init_l_Array_filterMap__replicate___auto__7___closed__22);
v___x_277_ = lean_array_push(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__24(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_278_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__23, &l_Array_filterMap__replicate___auto__7___closed__23_once, _init_l_Array_filterMap__replicate___auto__7___closed__23);
v___x_279_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__11));
v___x_280_ = lean_box(2);
v___x_281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_278_);
return v___x_281_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__25(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__24, &l_Array_filterMap__replicate___auto__7___closed__24_once, _init_l_Array_filterMap__replicate___auto__7___closed__24);
v___x_283_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_284_ = lean_array_push(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__26(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_285_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__25, &l_Array_filterMap__replicate___auto__7___closed__25_once, _init_l_Array_filterMap__replicate___auto__7___closed__25);
v___x_286_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__9));
v___x_287_ = lean_box(2);
v___x_288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
lean_ctor_set(v___x_288_, 2, v___x_285_);
return v___x_288_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__27(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__26, &l_Array_filterMap__replicate___auto__7___closed__26_once, _init_l_Array_filterMap__replicate___auto__7___closed__26);
v___x_290_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_291_ = lean_array_push(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__28(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__27, &l_Array_filterMap__replicate___auto__7___closed__27_once, _init_l_Array_filterMap__replicate___auto__7___closed__27);
v___x_293_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__7));
v___x_294_ = lean_box(2);
v___x_295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
lean_ctor_set(v___x_295_, 2, v___x_292_);
return v___x_295_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__29(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__28, &l_Array_filterMap__replicate___auto__7___closed__28_once, _init_l_Array_filterMap__replicate___auto__7___closed__28);
v___x_297_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__5));
v___x_298_ = lean_array_push(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7___closed__30(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__29, &l_Array_filterMap__replicate___auto__7___closed__29_once, _init_l_Array_filterMap__replicate___auto__7___closed__29);
v___x_300_ = ((lean_object*)(l_Array_filterMap__replicate___auto__7___closed__4));
v___x_301_ = lean_box(2);
v___x_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_299_);
return v___x_302_;
}
}
static lean_object* _init_l_Array_filterMap__replicate___auto__7(void){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Array_filterMap__replicate___auto__7___closed__30, &l_Array_filterMap__replicate___auto__7___closed__30_once, _init_l_Array_filterMap__replicate___auto__7___closed__30);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(lean_object* v_x_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_h__2_306_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_apply_1(v_h__1_305_, v___x_307_);
return v___x_308_;
}
else
{
lean_object* v_val_309_; lean_object* v___x_310_; 
lean_dec(v_h__1_305_);
v_val_309_ = lean_ctor_get(v_x_304_, 0);
lean_inc(v_val_309_);
lean_dec_ref(v_x_304_);
v___x_310_ = lean_apply_1(v_h__2_306_, v_val_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter(lean_object* v_00_u03b2_311_, lean_object* v_motive_312_, lean_object* v_x_313_, lean_object* v_h__1_314_, lean_object* v_h__2_315_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_h__2_315_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_apply_1(v_h__1_314_, v___x_316_);
return v___x_317_;
}
else
{
lean_object* v_val_318_; lean_object* v___x_319_; 
lean_dec(v_h__1_314_);
v_val_318_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_val_318_);
lean_dec_ref(v_x_313_);
v___x_319_ = lean_apply_1(v_h__2_315_, v_val_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(lean_object* v_i_320_, lean_object* v_h__1_321_, lean_object* v_h__2_322_){
_start:
{
lean_object* v_zero_323_; uint8_t v_isZero_324_; 
v_zero_323_ = lean_unsigned_to_nat(0u);
v_isZero_324_ = lean_nat_dec_eq(v_i_320_, v_zero_323_);
if (v_isZero_324_ == 1)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v_h__2_322_);
v___x_325_ = lean_box(0);
v___x_326_ = lean_apply_1(v_h__1_321_, v___x_325_);
return v___x_326_;
}
else
{
lean_object* v_one_327_; lean_object* v_n_328_; lean_object* v___x_329_; 
lean_dec(v_h__1_321_);
v_one_327_ = lean_unsigned_to_nat(1u);
v_n_328_ = lean_nat_sub(v_i_320_, v_one_327_);
v___x_329_ = lean_apply_1(v_h__2_322_, v_n_328_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg___boxed(lean_object* v_i_330_, lean_object* v_h__1_331_, lean_object* v_h__2_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(v_i_330_, v_h__1_331_, v_h__2_332_);
lean_dec(v_i_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(lean_object* v_motive_334_, lean_object* v_i_335_, lean_object* v_h__1_336_, lean_object* v_h__2_337_){
_start:
{
lean_object* v_zero_338_; uint8_t v_isZero_339_; 
v_zero_338_ = lean_unsigned_to_nat(0u);
v_isZero_339_ = lean_nat_dec_eq(v_i_335_, v_zero_338_);
if (v_isZero_339_ == 1)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v_h__2_337_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_apply_1(v_h__1_336_, v___x_340_);
return v___x_341_;
}
else
{
lean_object* v_one_342_; lean_object* v_n_343_; lean_object* v___x_344_; 
lean_dec(v_h__1_336_);
v_one_342_ = lean_unsigned_to_nat(1u);
v_n_343_ = lean_nat_sub(v_i_335_, v_one_342_);
v___x_344_ = lean_apply_1(v_h__2_337_, v_n_343_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___boxed(lean_object* v_motive_345_, lean_object* v_i_346_, lean_object* v_h__1_347_, lean_object* v_h__2_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(v_motive_345_, v_i_346_, v_h__1_347_, v_h__2_348_);
lean_dec(v_i_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_h__1_352_, lean_object* v_h__2_353_){
_start:
{
lean_object* v_zero_354_; uint8_t v_isZero_355_; 
v_zero_354_ = lean_unsigned_to_nat(0u);
v_isZero_355_ = lean_nat_dec_eq(v_x_350_, v_zero_354_);
if (v_isZero_355_ == 1)
{
lean_object* v___x_356_; 
lean_dec(v_h__2_353_);
v___x_356_ = lean_apply_1(v_h__1_352_, v_x_351_);
return v___x_356_;
}
else
{
lean_object* v_one_357_; lean_object* v_n_358_; lean_object* v___x_359_; 
lean_dec(v_h__1_352_);
v_one_357_ = lean_unsigned_to_nat(1u);
v_n_358_ = lean_nat_sub(v_x_350_, v_one_357_);
v___x_359_ = lean_apply_2(v_h__2_353_, v_n_358_, v_x_351_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg___boxed(lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_h__1_362_, lean_object* v_h__2_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(v_x_360_, v_x_361_, v_h__1_362_, v_h__2_363_);
lean_dec(v_x_360_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter(lean_object* v_00_u03b1_365_, lean_object* v_motive_366_, lean_object* v_x_367_, lean_object* v_x_368_, lean_object* v_h__1_369_, lean_object* v_h__2_370_){
_start:
{
lean_object* v_zero_371_; uint8_t v_isZero_372_; 
v_zero_371_ = lean_unsigned_to_nat(0u);
v_isZero_372_ = lean_nat_dec_eq(v_x_367_, v_zero_371_);
if (v_isZero_372_ == 1)
{
lean_object* v___x_373_; 
lean_dec(v_h__2_370_);
v___x_373_ = lean_apply_1(v_h__1_369_, v_x_368_);
return v___x_373_;
}
else
{
lean_object* v_one_374_; lean_object* v_n_375_; lean_object* v___x_376_; 
lean_dec(v_h__1_369_);
v_one_374_ = lean_unsigned_to_nat(1u);
v_n_375_ = lean_nat_sub(v_x_367_, v_one_374_);
v___x_376_ = lean_apply_2(v_h__2_370_, v_n_375_, v_x_368_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___boxed(lean_object* v_00_u03b1_377_, lean_object* v_motive_378_, lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_h__1_381_, lean_object* v_h__2_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter(v_00_u03b1_377_, v_motive_378_, v_x_379_, v_x_380_, v_h__1_381_, v_h__2_382_);
lean_dec(v_x_379_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object* v_i_384_, lean_object* v_h__1_385_, lean_object* v_h__2_386_){
_start:
{
lean_object* v_zero_387_; uint8_t v_isZero_388_; 
v_zero_387_ = lean_unsigned_to_nat(0u);
v_isZero_388_ = lean_nat_dec_eq(v_i_384_, v_zero_387_);
if (v_isZero_388_ == 1)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_h__2_386_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_apply_1(v_h__1_385_, v___x_389_);
return v___x_390_;
}
else
{
lean_object* v_one_391_; lean_object* v_n_392_; lean_object* v___x_393_; 
lean_dec(v_h__1_385_);
v_one_391_ = lean_unsigned_to_nat(1u);
v_n_392_ = lean_nat_sub(v_i_384_, v_one_391_);
v___x_393_ = lean_apply_1(v_h__2_386_, v_n_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object* v_i_394_, lean_object* v_h__1_395_, lean_object* v_h__2_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_394_, v_h__1_395_, v_h__2_396_);
lean_dec(v_i_394_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(lean_object* v_motive_398_, lean_object* v_i_399_, lean_object* v_h__1_400_, lean_object* v_h__2_401_){
_start:
{
lean_object* v_zero_402_; uint8_t v_isZero_403_; 
v_zero_402_ = lean_unsigned_to_nat(0u);
v_isZero_403_ = lean_nat_dec_eq(v_i_399_, v_zero_402_);
if (v_isZero_403_ == 1)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_h__2_401_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_apply_1(v_h__1_400_, v___x_404_);
return v___x_405_;
}
else
{
lean_object* v_one_406_; lean_object* v_n_407_; lean_object* v___x_408_; 
lean_dec(v_h__1_400_);
v_one_406_ = lean_unsigned_to_nat(1u);
v_n_407_ = lean_nat_sub(v_i_399_, v_one_406_);
v___x_408_ = lean_apply_1(v_h__2_401_, v_n_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object* v_motive_409_, lean_object* v_i_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(v_motive_409_, v_i_410_, v_h__1_411_, v_h__2_412_);
lean_dec(v_i_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object* v_i_414_, lean_object* v_h__1_415_, lean_object* v_h__2_416_){
_start:
{
lean_object* v_zero_417_; uint8_t v_isZero_418_; 
v_zero_417_ = lean_unsigned_to_nat(0u);
v_isZero_418_ = lean_nat_dec_eq(v_i_414_, v_zero_417_);
if (v_isZero_418_ == 1)
{
lean_object* v___x_419_; 
lean_dec(v_h__2_416_);
v___x_419_ = lean_apply_1(v_h__1_415_, lean_box(0));
return v___x_419_;
}
else
{
lean_object* v_one_420_; lean_object* v_n_421_; lean_object* v___x_422_; 
lean_dec(v_h__1_415_);
v_one_420_ = lean_unsigned_to_nat(1u);
v_n_421_ = lean_nat_sub(v_i_414_, v_one_420_);
v___x_422_ = lean_apply_2(v_h__2_416_, v_n_421_, lean_box(0));
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object* v_i_423_, lean_object* v_h__1_424_, lean_object* v_h__2_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(v_i_423_, v_h__1_424_, v_h__2_425_);
lean_dec(v_i_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(lean_object* v_00_u03b1_427_, lean_object* v_as_428_, lean_object* v_motive_429_, lean_object* v_i_430_, lean_object* v_h_431_, lean_object* v_h__1_432_, lean_object* v_h__2_433_){
_start:
{
lean_object* v_zero_434_; uint8_t v_isZero_435_; 
v_zero_434_ = lean_unsigned_to_nat(0u);
v_isZero_435_ = lean_nat_dec_eq(v_i_430_, v_zero_434_);
if (v_isZero_435_ == 1)
{
lean_object* v___x_436_; 
lean_dec(v_h__2_433_);
v___x_436_ = lean_apply_1(v_h__1_432_, lean_box(0));
return v___x_436_;
}
else
{
lean_object* v_one_437_; lean_object* v_n_438_; lean_object* v___x_439_; 
lean_dec(v_h__1_432_);
v_one_437_ = lean_unsigned_to_nat(1u);
v_n_438_ = lean_nat_sub(v_i_430_, v_one_437_);
v___x_439_ = lean_apply_2(v_h__2_433_, v_n_438_, lean_box(0));
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_440_, lean_object* v_as_441_, lean_object* v_motive_442_, lean_object* v_i_443_, lean_object* v_h_444_, lean_object* v_h__1_445_, lean_object* v_h__2_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(v_00_u03b1_440_, v_as_441_, v_motive_442_, v_i_443_, v_h_444_, v_h__1_445_, v_h__2_446_);
lean_dec(v_i_443_);
lean_dec_ref(v_as_441_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(lean_object* v_x_448_, lean_object* v_h__1_449_, lean_object* v_h__2_450_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v_h__1_449_);
v___x_451_ = lean_box(0);
v___x_452_ = lean_apply_1(v_h__2_450_, v___x_451_);
return v___x_452_;
}
else
{
lean_object* v_val_453_; lean_object* v___x_454_; 
lean_dec(v_h__2_450_);
v_val_453_ = lean_ctor_get(v_x_448_, 0);
lean_inc(v_val_453_);
lean_dec_ref(v_x_448_);
v___x_454_ = lean_apply_1(v_h__1_449_, v_val_453_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter(lean_object* v_00_u03b2_455_, lean_object* v_motive_456_, lean_object* v_x_457_, lean_object* v_h__1_458_, lean_object* v_h__2_459_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec(v_h__1_458_);
v___x_460_ = lean_box(0);
v___x_461_ = lean_apply_1(v_h__2_459_, v___x_460_);
return v___x_461_;
}
else
{
lean_object* v_val_462_; lean_object* v___x_463_; 
lean_dec(v_h__2_459_);
v_val_462_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_val_462_);
lean_dec_ref(v_x_457_);
v___x_463_ = lean_apply_1(v_h__1_458_, v_val_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter___redArg(lean_object* v_x_464_, lean_object* v_h__1_465_, lean_object* v_h__2_466_){
_start:
{
if (lean_obj_tag(v_x_464_) == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v_h__1_465_);
v___x_467_ = lean_box(0);
v___x_468_ = lean_apply_1(v_h__2_466_, v___x_467_);
return v___x_468_;
}
else
{
lean_object* v_val_469_; lean_object* v___x_470_; 
lean_dec(v_h__2_466_);
v_val_469_ = lean_ctor_get(v_x_464_, 0);
lean_inc(v_val_469_);
lean_dec_ref(v_x_464_);
v___x_470_ = lean_apply_1(v_h__1_465_, v_val_469_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter(lean_object* v_00_u03b2_471_, lean_object* v_motive_472_, lean_object* v_x_473_, lean_object* v_h__1_474_, lean_object* v_h__2_475_){
_start:
{
if (lean_obj_tag(v_x_473_) == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v_h__1_474_);
v___x_476_ = lean_box(0);
v___x_477_ = lean_apply_1(v_h__2_475_, v___x_476_);
return v___x_477_;
}
else
{
lean_object* v_val_478_; lean_object* v___x_479_; 
lean_dec(v_h__2_475_);
v_val_478_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_val_478_);
lean_dec_ref(v_x_473_);
v___x_479_ = lean_apply_1(v_h__1_474_, v_val_478_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___redArg(lean_object* v_x_480_, lean_object* v_h__1_481_, lean_object* v_h__2_482_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v_h__2_482_);
v___x_483_ = lean_box(0);
v___x_484_ = lean_apply_1(v_h__1_481_, v___x_483_);
return v___x_484_;
}
else
{
lean_object* v_val_485_; lean_object* v___x_486_; 
lean_dec(v_h__1_481_);
v_val_485_ = lean_ctor_get(v_x_480_, 0);
lean_inc(v_val_485_);
lean_dec_ref(v_x_480_);
v___x_486_ = lean_apply_1(v_h__2_482_, v_val_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(lean_object* v_00_u03b1_487_, lean_object* v_as_488_, lean_object* v_motive_489_, lean_object* v_x_490_, lean_object* v_h__1_491_, lean_object* v_h__2_492_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v_h__2_492_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_apply_1(v_h__1_491_, v___x_493_);
return v___x_494_;
}
else
{
lean_object* v_val_495_; lean_object* v___x_496_; 
lean_dec(v_h__1_491_);
v_val_495_ = lean_ctor_get(v_x_490_, 0);
lean_inc(v_val_495_);
lean_dec_ref(v_x_490_);
v___x_496_ = lean_apply_1(v_h__2_492_, v_val_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_497_, lean_object* v_as_498_, lean_object* v_motive_499_, lean_object* v_x_500_, lean_object* v_h__1_501_, lean_object* v_h__2_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(v_00_u03b1_497_, v_as_498_, v_motive_499_, v_x_500_, v_h__1_501_, v_h__2_502_);
lean_dec_ref(v_as_498_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg___lam__0(lean_object* v_x1_504_, lean_object* v_x2_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_506_, 0, v_x2_505_);
lean_ctor_set(v___x_506_, 1, v_x1_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Array_toListRev___redArg(lean_object* v_xs_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_528_ = lean_box(0);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_array_get_size(v_xs_527_);
v___x_531_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_532_ = lean_nat_dec_lt(v___x_529_, v___x_530_);
if (v___x_532_ == 0)
{
lean_dec_ref(v_xs_527_);
return v___x_528_;
}
else
{
lean_object* v___f_533_; uint8_t v___x_534_; 
v___f_533_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_534_ = lean_nat_dec_le(v___x_530_, v___x_530_);
if (v___x_534_ == 0)
{
if (v___x_532_ == 0)
{
lean_dec_ref(v_xs_527_);
return v___x_528_;
}
else
{
size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; 
v___x_535_ = ((size_t)0ULL);
v___x_536_ = lean_usize_of_nat(v___x_530_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_531_, v___f_533_, v_xs_527_, v___x_535_, v___x_536_, v___x_528_);
return v___x_537_;
}
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((size_t)0ULL);
v___x_539_ = lean_usize_of_nat(v___x_530_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_531_, v___f_533_, v_xs_527_, v___x_538_, v___x_539_, v___x_528_);
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toListRev(lean_object* v_00_u03b1_541_, lean_object* v_xs_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_543_ = lean_box(0);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_array_get_size(v_xs_542_);
v___x_546_ = ((lean_object*)(l_Array_toListRev___redArg___closed__9));
v___x_547_ = lean_nat_dec_lt(v___x_544_, v___x_545_);
if (v___x_547_ == 0)
{
lean_dec_ref(v_xs_542_);
return v___x_543_;
}
else
{
lean_object* v___f_548_; uint8_t v___x_549_; 
v___f_548_ = ((lean_object*)(l_Array_toListRev___redArg___closed__10));
v___x_549_ = lean_nat_dec_le(v___x_545_, v___x_545_);
if (v___x_549_ == 0)
{
if (v___x_547_ == 0)
{
lean_dec_ref(v_xs_542_);
return v___x_543_;
}
else
{
size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
v___x_550_ = ((size_t)0ULL);
v___x_551_ = lean_usize_of_nat(v___x_545_);
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_546_, v___f_548_, v_xs_542_, v___x_550_, v___x_551_, v___x_543_);
return v___x_552_;
}
}
else
{
size_t v___x_553_; size_t v___x_554_; lean_object* v___x_555_; 
v___x_553_ = ((size_t)0ULL);
v___x_554_ = lean_usize_of_nat(v___x_545_);
v___x_555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_546_, v___f_548_, v_xs_542_, v___x_553_, v___x_554_, v___x_543_);
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(lean_object* v_x_556_, lean_object* v_h__1_557_, lean_object* v_h__2_558_){
_start:
{
lean_object* v_zero_559_; uint8_t v_isZero_560_; 
v_zero_559_ = lean_unsigned_to_nat(0u);
v_isZero_560_ = lean_nat_dec_eq(v_x_556_, v_zero_559_);
if (v_isZero_560_ == 1)
{
lean_object* v___x_561_; 
lean_dec(v_h__1_557_);
v___x_561_ = lean_apply_1(v_h__2_558_, lean_box(0));
return v___x_561_;
}
else
{
lean_object* v_one_562_; lean_object* v_n_563_; lean_object* v___x_564_; 
lean_dec(v_h__2_558_);
v_one_562_ = lean_unsigned_to_nat(1u);
v_n_563_ = lean_nat_sub(v_x_556_, v_one_562_);
v___x_564_ = lean_apply_2(v_h__1_557_, v_n_563_, lean_box(0));
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg___boxed(lean_object* v_x_565_, lean_object* v_h__1_566_, lean_object* v_h__2_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(v_x_565_, v_h__1_566_, v_h__2_567_);
lean_dec(v_x_565_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(lean_object* v_n_569_, lean_object* v_motive_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_h__1_573_, lean_object* v_h__2_574_){
_start:
{
lean_object* v_zero_575_; uint8_t v_isZero_576_; 
v_zero_575_ = lean_unsigned_to_nat(0u);
v_isZero_576_ = lean_nat_dec_eq(v_x_571_, v_zero_575_);
if (v_isZero_576_ == 1)
{
lean_object* v___x_577_; 
lean_dec(v_h__1_573_);
v___x_577_ = lean_apply_1(v_h__2_574_, lean_box(0));
return v___x_577_;
}
else
{
lean_object* v_one_578_; lean_object* v_n_579_; lean_object* v___x_580_; 
lean_dec(v_h__2_574_);
v_one_578_ = lean_unsigned_to_nat(1u);
v_n_579_ = lean_nat_sub(v_x_571_, v_one_578_);
v___x_580_ = lean_apply_2(v_h__1_573_, v_n_579_, lean_box(0));
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___boxed(lean_object* v_n_581_, lean_object* v_motive_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_h__1_585_, lean_object* v_h__2_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(v_n_581_, v_motive_582_, v_x_583_, v_x_584_, v_h__1_585_, v_h__2_586_);
lean_dec(v_x_583_);
lean_dec(v_n_581_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_588_, lean_object* v_h__1_589_, lean_object* v_h__2_590_){
_start:
{
if (lean_obj_tag(v_opt_588_) == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec(v_h__1_589_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_apply_1(v_h__2_590_, v___x_591_);
return v___x_592_;
}
else
{
lean_object* v_val_593_; lean_object* v___x_594_; 
lean_dec(v_h__2_590_);
v_val_593_ = lean_ctor_get(v_opt_588_, 0);
lean_inc(v_val_593_);
lean_dec_ref(v_opt_588_);
v___x_594_ = lean_apply_1(v_h__1_589_, v_val_593_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_595_, lean_object* v_motive_596_, lean_object* v_opt_597_, lean_object* v_h__1_598_, lean_object* v_h__2_599_){
_start:
{
if (lean_obj_tag(v_opt_597_) == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v_h__1_598_);
v___x_600_ = lean_box(0);
v___x_601_ = lean_apply_1(v_h__2_599_, v___x_600_);
return v___x_601_;
}
else
{
lean_object* v_val_602_; lean_object* v___x_603_; 
lean_dec(v_h__2_599_);
v_val_602_ = lean_ctor_get(v_opt_597_, 0);
lean_inc(v_val_602_);
lean_dec_ref(v_opt_597_);
v___x_603_ = lean_apply_1(v_h__1_598_, v_val_602_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_h__1_605_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_apply_1(v_h__2_606_, v___x_607_);
return v___x_608_;
}
else
{
lean_object* v_val_609_; lean_object* v___x_610_; 
lean_dec(v_h__2_606_);
v_val_609_ = lean_ctor_get(v_x_604_, 0);
lean_inc(v_val_609_);
lean_dec_ref(v_x_604_);
v___x_610_ = lean_apply_1(v_h__1_605_, v_val_609_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_611_, lean_object* v_motive_612_, lean_object* v_x_613_, lean_object* v_h__1_614_, lean_object* v_h__2_615_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
lean_dec(v_h__1_614_);
v___x_616_ = lean_box(0);
v___x_617_ = lean_apply_1(v_h__2_615_, v___x_616_);
return v___x_617_;
}
else
{
lean_object* v_val_618_; lean_object* v___x_619_; 
lean_dec(v_h__2_615_);
v_val_618_ = lean_ctor_get(v_x_613_, 0);
lean_inc(v_val_618_);
lean_dec_ref(v_x_613_);
v___x_619_ = lean_apply_1(v_h__1_614_, v_val_618_);
return v___x_619_;
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
