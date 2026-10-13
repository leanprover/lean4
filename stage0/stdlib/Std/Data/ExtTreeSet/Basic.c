// Lean compiler output
// Module: Std.Data.ExtTreeSet.Basic
// Imports: public import Std.Data.ExtTreeMap.Basic
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
lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_ExtTreeSet___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__0 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__0_value;
static const lean_string_object l_Std_ExtTreeSet___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__1 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__1_value;
static const lean_string_object l_Std_ExtTreeSet___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__2 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__2_value;
static const lean_string_object l_Std_ExtTreeSet___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__3 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__3_value;
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__4 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__4_value;
static const lean_array_object l_Std_ExtTreeSet___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__5 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__5_value;
static const lean_string_object l_Std_ExtTreeSet___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__6 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__6_value;
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__7 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__7_value;
static const lean_string_object l_Std_ExtTreeSet___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__8 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__8_value;
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__9 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__9_value;
static const lean_string_object l_Std_ExtTreeSet___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__10 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__10_value;
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__11 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__11_value;
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__12;
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__13;
static const lean_string_object l_Std_ExtTreeSet___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__14 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__14_value;
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__15 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__15_value;
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__16 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__16_value;
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__15_value),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_ExtTreeSet___auto__1___closed__17 = (const lean_object*)&l_Std_ExtTreeSet___auto__1___closed__17_value;
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__18;
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__19;
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__20;
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__21;
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__22;
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__23;
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__24;
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__25;
LEAN_EXPORT lean_object* l_Std_ExtTreeSet___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___redArg();
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg();
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_ExtTreeSet_getGE_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_ExtTreeSet_getGE_x21___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeSet_getGE_x21___redArg___closed__0_value;
static const lean_string_object l_Std_ExtTreeSet_getGE_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_ExtTreeSet_getGE_x21___redArg___closed__1 = (const lean_object*)&l_Std_ExtTreeSet_getGE_x21___redArg___closed__1_value;
static const lean_string_object l_Std_ExtTreeSet_getGE_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_ExtTreeSet_getGE_x21___redArg___closed__2 = (const lean_object*)&l_Std_ExtTreeSet_getGE_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet_getGE_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtTreeSet_foldr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeSet_foldr___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__0_value;
static const lean_closure_object l_Std_ExtTreeSet_foldr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeSet_foldr___redArg___closed__1 = (const lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__1_value;
static const lean_closure_object l_Std_ExtTreeSet_foldr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeSet_foldr___redArg___closed__2 = (const lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__2_value;
static const lean_closure_object l_Std_ExtTreeSet_foldr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeSet_foldr___redArg___closed__3 = (const lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__3_value;
static const lean_closure_object l_Std_ExtTreeSet_foldr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeSet_foldr___redArg___closed__4 = (const lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__4_value;
static const lean_closure_object l_Std_ExtTreeSet_foldr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeSet_foldr___redArg___closed__5 = (const lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__5_value;
static const lean_closure_object l_Std_ExtTreeSet_foldr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeSet_foldr___redArg___closed__6 = (const lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__6_value;
static const lean_ctor_object l_Std_ExtTreeSet_foldr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__0_value),((lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__1_value)}};
static const lean_object* l_Std_ExtTreeSet_foldr___redArg___closed__7 = (const lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__7_value;
static const lean_ctor_object l_Std_ExtTreeSet_foldr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__7_value),((lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__2_value),((lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__3_value),((lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__4_value),((lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__5_value)}};
static const lean_object* l_Std_ExtTreeSet_foldr___redArg___closed__8 = (const lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__8_value;
static const lean_ctor_object l_Std_ExtTreeSet_foldr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__8_value),((lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__6_value)}};
static const lean_object* l_Std_ExtTreeSet_foldr___redArg___closed__9 = (const lean_object*)&l_Std_ExtTreeSet_foldr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_ExtTreeSet_partition___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_ExtTreeSet_partition___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeSet_partition___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_ExtTreeSet_any___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_ExtTreeSet_any___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeSet_any___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtTreeSet_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtTreeSet_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeSet_toList___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeSet_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtTreeSet_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtTreeSet_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeSet_toArray___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeSet_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0;
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.ExtTreeSet.ofList "};
static const lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__12, &l_Std_ExtTreeSet___auto__1___closed__12_once, _init_l_Std_ExtTreeSet___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__17));
v___x_45_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__13, &l_Std_ExtTreeSet___auto__1___closed__13_once, _init_l_Std_ExtTreeSet___auto__1___closed__13);
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__18, &l_Std_ExtTreeSet___auto__1___closed__18_once, _init_l_Std_ExtTreeSet___auto__1___closed__18);
v___x_48_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__11));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__19, &l_Std_ExtTreeSet___auto__1___closed__19_once, _init_l_Std_ExtTreeSet___auto__1___closed__19);
v___x_52_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__20, &l_Std_ExtTreeSet___auto__1___closed__20_once, _init_l_Std_ExtTreeSet___auto__1___closed__20);
v___x_55_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__9));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__22(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__21, &l_Std_ExtTreeSet___auto__1___closed__21_once, _init_l_Std_ExtTreeSet___auto__1___closed__21);
v___x_59_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__23(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__22, &l_Std_ExtTreeSet___auto__1___closed__22_once, _init_l_Std_ExtTreeSet___auto__1___closed__22);
v___x_62_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__7));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__24(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__23, &l_Std_ExtTreeSet___auto__1___closed__23_once, _init_l_Std_ExtTreeSet___auto__1___closed__23);
v___x_66_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__25(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__24, &l_Std_ExtTreeSet___auto__1___closed__24_once, _init_l_Std_ExtTreeSet___auto__1___closed__24);
v___x_69_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__4));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__25, &l_Std_ExtTreeSet___auto__1___closed__25_once, _init_l_Std_ExtTreeSet___auto__1___closed__25);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(1);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___redArg___boxed(lean_object* v___dummy_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_ExtTreeSet_empty___redArg();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty(lean_object* v_00_u03b1_77_, lean_object* v_cmp_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_box(1);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___boxed(lean_object* v_00_u03b1_80_, lean_object* v_cmp_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_ExtTreeSet_empty(v_00_u03b1_80_, v_cmp_81_);
lean_dec_ref(v_cmp_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(1);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_ExtTreeSet_instEmptyCollection___redArg();
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection(lean_object* v_00_u03b1_87_, lean_object* v_cmp_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(1);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_90_, lean_object* v_cmp_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_ExtTreeSet_instEmptyCollection(v_00_u03b1_90_, v_cmp_91_);
lean_dec_ref(v_cmp_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(1);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___redArg___boxed(lean_object* v___dummy_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_ExtTreeSet_instInhabited___redArg();
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited(lean_object* v_00_u03b1_97_, lean_object* v_cmp_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_box(1);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___boxed(lean_object* v_00_u03b1_100_, lean_object* v_cmp_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_ExtTreeSet_instInhabited(v_00_u03b1_100_, v_cmp_101_);
lean_dec_ref(v_cmp_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insert___redArg(lean_object* v_cmp_103_, lean_object* v_l_104_, lean_object* v_a_105_){
_start:
{
uint8_t v___x_106_; 
lean_inc(v_l_104_);
lean_inc(v_a_105_);
lean_inc_ref(v_cmp_103_);
v___x_106_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_103_, v_a_105_, v_l_104_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_box(0);
v___x_108_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_103_, v_a_105_, v___x_107_, v_l_104_);
return v___x_108_;
}
else
{
lean_dec(v_a_105_);
lean_dec_ref(v_cmp_103_);
return v_l_104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insert(lean_object* v_00_u03b1_109_, lean_object* v_cmp_110_, lean_object* v_inst_111_, lean_object* v_l_112_, lean_object* v_a_113_){
_start:
{
uint8_t v___x_114_; 
lean_inc(v_l_112_);
lean_inc(v_a_113_);
lean_inc_ref(v_cmp_110_);
v___x_114_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_110_, v_a_113_, v_l_112_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_box(0);
v___x_116_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_110_, v_a_113_, v___x_115_, v_l_112_);
return v___x_116_;
}
else
{
lean_dec(v_a_113_);
lean_dec_ref(v_cmp_110_);
return v_l_112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0(lean_object* v_cmp_117_, lean_object* v_e_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_box(1);
lean_inc(v_e_118_);
lean_inc_ref(v_cmp_117_);
v___x_120_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_117_, v_e_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_box(0);
v___x_122_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_117_, v_e_118_, v___x_121_, v___x_119_);
return v___x_122_;
}
else
{
lean_dec(v_e_118_);
lean_dec_ref(v_cmp_117_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg(lean_object* v_cmp_123_){
_start:
{
lean_object* v___f_124_; 
v___f_124_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_124_, 0, v_cmp_123_);
return v___f_124_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp(lean_object* v_00_u03b1_125_, lean_object* v_cmp_126_, lean_object* v_inst_127_){
_start:
{
lean_object* v___f_128_; 
v___f_128_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_128_, 0, v_cmp_126_);
return v___f_128_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0(lean_object* v_cmp_129_, lean_object* v_e_130_, lean_object* v_s_131_){
_start:
{
uint8_t v___x_132_; 
lean_inc(v_s_131_);
lean_inc(v_e_130_);
lean_inc_ref(v_cmp_129_);
v___x_132_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_129_, v_e_130_, v_s_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_box(0);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_129_, v_e_130_, v___x_133_, v_s_131_);
return v___x_134_;
}
else
{
lean_dec(v_e_130_);
lean_dec_ref(v_cmp_129_);
return v_s_131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp___redArg(lean_object* v_cmp_135_){
_start:
{
lean_object* v___f_136_; 
v___f_136_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_136_, 0, v_cmp_135_);
return v___f_136_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp(lean_object* v_00_u03b1_137_, lean_object* v_cmp_138_, lean_object* v_inst_139_){
_start:
{
lean_object* v___f_140_; 
v___f_140_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_140_, 0, v_cmp_138_);
return v___f_140_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_containsThenInsert___redArg(lean_object* v_cmp_141_, lean_object* v_t_142_, lean_object* v_a_143_){
_start:
{
uint8_t v___x_144_; 
lean_inc(v_t_142_);
lean_inc(v_a_143_);
lean_inc_ref(v_cmp_141_);
v___x_144_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_141_, v_a_143_, v_t_142_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = lean_box(0);
v___x_146_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_141_, v_a_143_, v___x_145_, v_t_142_);
v___x_147_ = lean_box(v___x_144_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
return v___x_148_;
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_a_143_);
lean_dec_ref(v_cmp_141_);
v___x_149_ = lean_box(v___x_144_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_t_142_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_containsThenInsert(lean_object* v_00_u03b1_151_, lean_object* v_cmp_152_, lean_object* v_inst_153_, lean_object* v_t_154_, lean_object* v_a_155_){
_start:
{
uint8_t v___x_156_; 
lean_inc(v_t_154_);
lean_inc(v_a_155_);
lean_inc_ref(v_cmp_152_);
v___x_156_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_152_, v_a_155_, v_t_154_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_157_ = lean_box(0);
v___x_158_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_152_, v_a_155_, v___x_157_, v_t_154_);
v___x_159_ = lean_box(v___x_156_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_a_155_);
lean_dec_ref(v_cmp_152_);
v___x_161_ = lean_box(v___x_156_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_t_154_);
return v___x_162_;
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_contains___redArg(lean_object* v_cmp_163_, lean_object* v_l_164_, lean_object* v_a_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_163_, v_a_165_, v_l_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_contains___redArg___boxed(lean_object* v_cmp_167_, lean_object* v_l_168_, lean_object* v_a_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_Std_ExtTreeSet_contains___redArg(v_cmp_167_, v_l_168_, v_a_169_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_contains(lean_object* v_00_u03b1_172_, lean_object* v_cmp_173_, lean_object* v_inst_174_, lean_object* v_l_175_, lean_object* v_a_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_173_, v_a_176_, v_l_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_contains___boxed(lean_object* v_00_u03b1_178_, lean_object* v_cmp_179_, lean_object* v_inst_180_, lean_object* v_l_181_, lean_object* v_a_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Std_ExtTreeSet_contains(v_00_u03b1_178_, v_cmp_179_, v_inst_180_, v_l_181_, v_a_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg(){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(0);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg___boxed(lean_object* v___dummy_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg();
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp(lean_object* v_00_u03b1_189_, lean_object* v_cmp_190_, lean_object* v_inst_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(0);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_193_, lean_object* v_cmp_194_, lean_object* v_inst_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_ExtTreeSet_instMembershipOfTransCmp(v_00_u03b1_193_, v_cmp_194_, v_inst_195_);
lean_dec_ref(v_cmp_194_);
return v_res_196_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableMem___redArg(lean_object* v_cmp_197_, lean_object* v_m_198_, lean_object* v_a_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_197_, v_a_199_, v_m_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableMem___redArg___boxed(lean_object* v_cmp_201_, lean_object* v_m_202_, lean_object* v_a_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Std_ExtTreeSet_instDecidableMem___redArg(v_cmp_201_, v_m_202_, v_a_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableMem(lean_object* v_00_u03b1_206_, lean_object* v_cmp_207_, lean_object* v_inst_208_, lean_object* v_m_209_, lean_object* v_a_210_){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_207_, v_a_210_, v_m_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableMem___boxed(lean_object* v_00_u03b1_212_, lean_object* v_cmp_213_, lean_object* v_inst_214_, lean_object* v_m_215_, lean_object* v_a_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Std_ExtTreeSet_instDecidableMem(v_00_u03b1_212_, v_cmp_213_, v_inst_214_, v_m_215_, v_a_216_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___redArg(lean_object* v_t_219_){
_start:
{
if (lean_obj_tag(v_t_219_) == 0)
{
lean_object* v_size_220_; 
v_size_220_ = lean_ctor_get(v_t_219_, 0);
lean_inc(v_size_220_);
return v_size_220_;
}
else
{
lean_object* v___x_221_; 
v___x_221_ = lean_unsigned_to_nat(0u);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___redArg___boxed(lean_object* v_t_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_ExtTreeSet_size___redArg(v_t_222_);
lean_dec(v_t_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size(lean_object* v_00_u03b1_224_, lean_object* v_cmp_225_, lean_object* v_t_226_){
_start:
{
if (lean_obj_tag(v_t_226_) == 0)
{
lean_object* v_size_227_; 
v_size_227_ = lean_ctor_get(v_t_226_, 0);
lean_inc(v_size_227_);
return v_size_227_;
}
else
{
lean_object* v___x_228_; 
v___x_228_ = lean_unsigned_to_nat(0u);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___boxed(lean_object* v_00_u03b1_229_, lean_object* v_cmp_230_, lean_object* v_t_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_ExtTreeSet_size(v_00_u03b1_229_, v_cmp_230_, v_t_231_);
lean_dec(v_t_231_);
lean_dec_ref(v_cmp_230_);
return v_res_232_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_isEmpty___redArg(lean_object* v_t_233_){
_start:
{
if (lean_obj_tag(v_t_233_) == 0)
{
uint8_t v___x_234_; 
v___x_234_ = 0;
return v___x_234_;
}
else
{
uint8_t v___x_235_; 
v___x_235_ = 1;
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_isEmpty___redArg___boxed(lean_object* v_t_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Std_ExtTreeSet_isEmpty___redArg(v_t_236_);
lean_dec(v_t_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_isEmpty(lean_object* v_00_u03b1_239_, lean_object* v_cmp_240_, lean_object* v_t_241_){
_start:
{
if (lean_obj_tag(v_t_241_) == 0)
{
uint8_t v___x_242_; 
v___x_242_ = 0;
return v___x_242_;
}
else
{
uint8_t v___x_243_; 
v___x_243_ = 1;
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_isEmpty___boxed(lean_object* v_00_u03b1_244_, lean_object* v_cmp_245_, lean_object* v_t_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Std_ExtTreeSet_isEmpty(v_00_u03b1_244_, v_cmp_245_, v_t_246_);
lean_dec(v_t_246_);
lean_dec_ref(v_cmp_245_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_erase___redArg(lean_object* v_cmp_249_, lean_object* v_t_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_249_, v_a_251_, v_t_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_erase(lean_object* v_00_u03b1_253_, lean_object* v_cmp_254_, lean_object* v_inst_255_, lean_object* v_t_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_254_, v_a_257_, v_t_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x3f___redArg(lean_object* v_cmp_259_, lean_object* v_t_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_259_, v_t_260_, v_a_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x3f(lean_object* v_00_u03b1_263_, lean_object* v_cmp_264_, lean_object* v_inst_265_, lean_object* v_t_266_, lean_object* v_a_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_264_, v_t_266_, v_a_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get___redArg(lean_object* v_cmp_269_, lean_object* v_t_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_269_, v_t_270_, v_a_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get(lean_object* v_00_u03b1_273_, lean_object* v_cmp_274_, lean_object* v_inst_275_, lean_object* v_t_276_, lean_object* v_a_277_, lean_object* v_h_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_274_, v_t_276_, v_a_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___redArg(lean_object* v_cmp_280_, lean_object* v_inst_281_, lean_object* v_t_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_280_, v_t_282_, v_a_283_, v_inst_281_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___redArg___boxed(lean_object* v_cmp_285_, lean_object* v_inst_286_, lean_object* v_t_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_ExtTreeSet_get_x21___redArg(v_cmp_285_, v_inst_286_, v_t_287_, v_a_288_);
lean_dec(v_inst_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21(lean_object* v_00_u03b1_290_, lean_object* v_cmp_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_t_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_291_, v_t_294_, v_a_295_, v_inst_293_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___boxed(lean_object* v_00_u03b1_297_, lean_object* v_cmp_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_t_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Std_ExtTreeSet_get_x21(v_00_u03b1_297_, v_cmp_298_, v_inst_299_, v_inst_300_, v_t_301_, v_a_302_);
lean_dec(v_inst_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg(lean_object* v_cmp_304_, lean_object* v_t_305_, lean_object* v_a_306_, lean_object* v_fallback_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_304_, v_t_305_, v_a_306_, v_fallback_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg___boxed(lean_object* v_cmp_309_, lean_object* v_t_310_, lean_object* v_a_311_, lean_object* v_fallback_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_ExtTreeSet_getD___redArg(v_cmp_309_, v_t_310_, v_a_311_, v_fallback_312_);
lean_dec(v_fallback_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD(lean_object* v_00_u03b1_314_, lean_object* v_cmp_315_, lean_object* v_inst_316_, lean_object* v_t_317_, lean_object* v_a_318_, lean_object* v_fallback_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_315_, v_t_317_, v_a_318_, v_fallback_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___boxed(lean_object* v_00_u03b1_321_, lean_object* v_cmp_322_, lean_object* v_inst_323_, lean_object* v_t_324_, lean_object* v_a_325_, lean_object* v_fallback_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_ExtTreeSet_getD(v_00_u03b1_321_, v_cmp_322_, v_inst_323_, v_t_324_, v_a_325_, v_fallback_326_);
lean_dec(v_fallback_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg(lean_object* v_t_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg___boxed(lean_object* v_t_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_ExtTreeSet_min_x3f___redArg(v_t_330_);
lean_dec(v_t_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f(lean_object* v_00_u03b1_332_, lean_object* v_cmp_333_, lean_object* v_inst_334_, lean_object* v_t_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___boxed(lean_object* v_00_u03b1_337_, lean_object* v_cmp_338_, lean_object* v_inst_339_, lean_object* v_t_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_ExtTreeSet_min_x3f(v_00_u03b1_337_, v_cmp_338_, v_inst_339_, v_t_340_);
lean_dec(v_t_340_);
lean_dec_ref(v_cmp_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg(lean_object* v_t_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg___boxed(lean_object* v_t_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_ExtTreeSet_min___redArg(v_t_344_);
lean_dec(v_t_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min(lean_object* v_00_u03b1_346_, lean_object* v_cmp_347_, lean_object* v_inst_348_, lean_object* v_t_349_, lean_object* v_h_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___boxed(lean_object* v_00_u03b1_352_, lean_object* v_cmp_353_, lean_object* v_inst_354_, lean_object* v_t_355_, lean_object* v_h_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_ExtTreeSet_min(v_00_u03b1_352_, v_cmp_353_, v_inst_354_, v_t_355_, v_h_356_);
lean_dec(v_t_355_);
lean_dec_ref(v_cmp_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg(lean_object* v_inst_358_, lean_object* v_t_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_358_, v_t_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg___boxed(lean_object* v_inst_361_, lean_object* v_t_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_ExtTreeSet_min_x21___redArg(v_inst_361_, v_t_362_);
lean_dec(v_t_362_);
lean_dec(v_inst_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21(lean_object* v_00_u03b1_364_, lean_object* v_cmp_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_t_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_367_, v_t_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___boxed(lean_object* v_00_u03b1_370_, lean_object* v_cmp_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_t_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_ExtTreeSet_min_x21(v_00_u03b1_370_, v_cmp_371_, v_inst_372_, v_inst_373_, v_t_374_);
lean_dec(v_t_374_);
lean_dec(v_inst_373_);
lean_dec_ref(v_cmp_371_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg(lean_object* v_t_376_, lean_object* v_fallback_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_376_, v_fallback_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg___boxed(lean_object* v_t_379_, lean_object* v_fallback_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_ExtTreeSet_minD___redArg(v_t_379_, v_fallback_380_);
lean_dec(v_fallback_380_);
lean_dec(v_t_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD(lean_object* v_00_u03b1_382_, lean_object* v_cmp_383_, lean_object* v_inst_384_, lean_object* v_t_385_, lean_object* v_fallback_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_385_, v_fallback_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___boxed(lean_object* v_00_u03b1_388_, lean_object* v_cmp_389_, lean_object* v_inst_390_, lean_object* v_t_391_, lean_object* v_fallback_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_ExtTreeSet_minD(v_00_u03b1_388_, v_cmp_389_, v_inst_390_, v_t_391_, v_fallback_392_);
lean_dec(v_fallback_392_);
lean_dec(v_t_391_);
lean_dec_ref(v_cmp_389_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg(lean_object* v_t_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg___boxed(lean_object* v_t_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_ExtTreeSet_max_x3f___redArg(v_t_396_);
lean_dec(v_t_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f(lean_object* v_00_u03b1_398_, lean_object* v_cmp_399_, lean_object* v_inst_400_, lean_object* v_t_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___boxed(lean_object* v_00_u03b1_403_, lean_object* v_cmp_404_, lean_object* v_inst_405_, lean_object* v_t_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_ExtTreeSet_max_x3f(v_00_u03b1_403_, v_cmp_404_, v_inst_405_, v_t_406_);
lean_dec(v_t_406_);
lean_dec_ref(v_cmp_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg(lean_object* v_t_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg___boxed(lean_object* v_t_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_ExtTreeSet_max___redArg(v_t_410_);
lean_dec(v_t_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max(lean_object* v_00_u03b1_412_, lean_object* v_cmp_413_, lean_object* v_inst_414_, lean_object* v_t_415_, lean_object* v_h_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___boxed(lean_object* v_00_u03b1_418_, lean_object* v_cmp_419_, lean_object* v_inst_420_, lean_object* v_t_421_, lean_object* v_h_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_ExtTreeSet_max(v_00_u03b1_418_, v_cmp_419_, v_inst_420_, v_t_421_, v_h_422_);
lean_dec(v_t_421_);
lean_dec_ref(v_cmp_419_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg(lean_object* v_inst_424_, lean_object* v_t_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_424_, v_t_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg___boxed(lean_object* v_inst_427_, lean_object* v_t_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_ExtTreeSet_max_x21___redArg(v_inst_427_, v_t_428_);
lean_dec(v_t_428_);
lean_dec(v_inst_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21(lean_object* v_00_u03b1_430_, lean_object* v_cmp_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_t_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_433_, v_t_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___boxed(lean_object* v_00_u03b1_436_, lean_object* v_cmp_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_t_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_ExtTreeSet_max_x21(v_00_u03b1_436_, v_cmp_437_, v_inst_438_, v_inst_439_, v_t_440_);
lean_dec(v_t_440_);
lean_dec(v_inst_439_);
lean_dec_ref(v_cmp_437_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg(lean_object* v_t_442_, lean_object* v_fallback_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_442_, v_fallback_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg___boxed(lean_object* v_t_445_, lean_object* v_fallback_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_ExtTreeSet_maxD___redArg(v_t_445_, v_fallback_446_);
lean_dec(v_fallback_446_);
lean_dec(v_t_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD(lean_object* v_00_u03b1_448_, lean_object* v_cmp_449_, lean_object* v_inst_450_, lean_object* v_t_451_, lean_object* v_fallback_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_451_, v_fallback_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___boxed(lean_object* v_00_u03b1_454_, lean_object* v_cmp_455_, lean_object* v_inst_456_, lean_object* v_t_457_, lean_object* v_fallback_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_ExtTreeSet_maxD(v_00_u03b1_454_, v_cmp_455_, v_inst_456_, v_t_457_, v_fallback_458_);
lean_dec(v_fallback_458_);
lean_dec(v_t_457_);
lean_dec_ref(v_cmp_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg(lean_object* v_t_460_, lean_object* v_n_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_460_, v_n_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg___boxed(lean_object* v_t_463_, lean_object* v_n_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_ExtTreeSet_atIdx_x3f___redArg(v_t_463_, v_n_464_);
lean_dec(v_t_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f(lean_object* v_00_u03b1_466_, lean_object* v_cmp_467_, lean_object* v_inst_468_, lean_object* v_t_469_, lean_object* v_n_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_469_, v_n_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___boxed(lean_object* v_00_u03b1_472_, lean_object* v_cmp_473_, lean_object* v_inst_474_, lean_object* v_t_475_, lean_object* v_n_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_ExtTreeSet_atIdx_x3f(v_00_u03b1_472_, v_cmp_473_, v_inst_474_, v_t_475_, v_n_476_);
lean_dec(v_t_475_);
lean_dec_ref(v_cmp_473_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg(lean_object* v_t_478_, lean_object* v_n_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_478_, v_n_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg___boxed(lean_object* v_t_481_, lean_object* v_n_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_ExtTreeSet_atIdx___redArg(v_t_481_, v_n_482_);
lean_dec(v_t_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx(lean_object* v_00_u03b1_484_, lean_object* v_cmp_485_, lean_object* v_inst_486_, lean_object* v_t_487_, lean_object* v_n_488_, lean_object* v_h_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_487_, v_n_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___boxed(lean_object* v_00_u03b1_491_, lean_object* v_cmp_492_, lean_object* v_inst_493_, lean_object* v_t_494_, lean_object* v_n_495_, lean_object* v_h_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_ExtTreeSet_atIdx(v_00_u03b1_491_, v_cmp_492_, v_inst_493_, v_t_494_, v_n_495_, v_h_496_);
lean_dec(v_t_494_);
lean_dec_ref(v_cmp_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg(lean_object* v_inst_498_, lean_object* v_t_499_, lean_object* v_n_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_498_, v_t_499_, v_n_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg___boxed(lean_object* v_inst_502_, lean_object* v_t_503_, lean_object* v_n_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_ExtTreeSet_atIdx_x21___redArg(v_inst_502_, v_t_503_, v_n_504_);
lean_dec(v_t_503_);
lean_dec(v_inst_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21(lean_object* v_00_u03b1_506_, lean_object* v_cmp_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_t_510_, lean_object* v_n_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_509_, v_t_510_, v_n_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___boxed(lean_object* v_00_u03b1_513_, lean_object* v_cmp_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_t_517_, lean_object* v_n_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_ExtTreeSet_atIdx_x21(v_00_u03b1_513_, v_cmp_514_, v_inst_515_, v_inst_516_, v_t_517_, v_n_518_);
lean_dec(v_t_517_);
lean_dec(v_inst_516_);
lean_dec_ref(v_cmp_514_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg(lean_object* v_t_520_, lean_object* v_n_521_, lean_object* v_fallback_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_520_, v_n_521_, v_fallback_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg___boxed(lean_object* v_t_524_, lean_object* v_n_525_, lean_object* v_fallback_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_ExtTreeSet_atIdxD___redArg(v_t_524_, v_n_525_, v_fallback_526_);
lean_dec(v_fallback_526_);
lean_dec(v_t_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD(lean_object* v_00_u03b1_528_, lean_object* v_cmp_529_, lean_object* v_inst_530_, lean_object* v_t_531_, lean_object* v_n_532_, lean_object* v_fallback_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_531_, v_n_532_, v_fallback_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___boxed(lean_object* v_00_u03b1_535_, lean_object* v_cmp_536_, lean_object* v_inst_537_, lean_object* v_t_538_, lean_object* v_n_539_, lean_object* v_fallback_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_ExtTreeSet_atIdxD(v_00_u03b1_535_, v_cmp_536_, v_inst_537_, v_t_538_, v_n_539_, v_fallback_540_);
lean_dec(v_fallback_540_);
lean_dec(v_t_538_);
lean_dec_ref(v_cmp_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f___redArg(lean_object* v_cmp_542_, lean_object* v_t_543_, lean_object* v_k_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_box(0);
v___x_546_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_542_, v_k_544_, v___x_545_, v_t_543_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f(lean_object* v_00_u03b1_547_, lean_object* v_cmp_548_, lean_object* v_inst_549_, lean_object* v_t_550_, lean_object* v_k_551_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_box(0);
v___x_553_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_548_, v_k_551_, v___x_552_, v_t_550_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f___redArg(lean_object* v_cmp_554_, lean_object* v_t_555_, lean_object* v_k_556_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_box(0);
v___x_558_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_554_, v_k_556_, v___x_557_, v_t_555_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f(lean_object* v_00_u03b1_559_, lean_object* v_cmp_560_, lean_object* v_inst_561_, lean_object* v_t_562_, lean_object* v_k_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_box(0);
v___x_565_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_560_, v_k_563_, v___x_564_, v_t_562_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f___redArg(lean_object* v_cmp_566_, lean_object* v_t_567_, lean_object* v_k_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_box(0);
v___x_570_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_566_, v_k_568_, v___x_569_, v_t_567_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f(lean_object* v_00_u03b1_571_, lean_object* v_cmp_572_, lean_object* v_inst_573_, lean_object* v_t_574_, lean_object* v_k_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_box(0);
v___x_577_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_572_, v_k_575_, v___x_576_, v_t_574_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f___redArg(lean_object* v_cmp_578_, lean_object* v_t_579_, lean_object* v_k_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_box(0);
v___x_582_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_578_, v_k_580_, v___x_581_, v_t_579_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f(lean_object* v_00_u03b1_583_, lean_object* v_cmp_584_, lean_object* v_inst_585_, lean_object* v_t_586_, lean_object* v_k_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_box(0);
v___x_589_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_584_, v_k_587_, v___x_588_, v_t_586_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE___redArg(lean_object* v_cmp_590_, lean_object* v_t_591_, lean_object* v_k_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_590_, v_k_592_, v_t_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE(lean_object* v_00_u03b1_594_, lean_object* v_cmp_595_, lean_object* v_inst_596_, lean_object* v_t_597_, lean_object* v_k_598_, lean_object* v_h_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_595_, v_k_598_, v_t_597_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT___redArg(lean_object* v_cmp_601_, lean_object* v_t_602_, lean_object* v_k_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_601_, v_k_603_, v_t_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT(lean_object* v_00_u03b1_605_, lean_object* v_cmp_606_, lean_object* v_inst_607_, lean_object* v_t_608_, lean_object* v_k_609_, lean_object* v_h_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_606_, v_k_609_, v_t_608_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE___redArg(lean_object* v_cmp_612_, lean_object* v_t_613_, lean_object* v_k_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_612_, v_k_614_, v_t_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE(lean_object* v_00_u03b1_616_, lean_object* v_cmp_617_, lean_object* v_inst_618_, lean_object* v_t_619_, lean_object* v_k_620_, lean_object* v_h_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_617_, v_k_620_, v_t_619_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT___redArg(lean_object* v_cmp_623_, lean_object* v_t_624_, lean_object* v_k_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_623_, v_k_625_, v_t_624_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT(lean_object* v_00_u03b1_627_, lean_object* v_cmp_628_, lean_object* v_inst_629_, lean_object* v_t_630_, lean_object* v_k_631_, lean_object* v_h_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_628_, v_k_631_, v_t_630_);
return v___x_633_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_637_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__2));
v___x_638_ = lean_unsigned_to_nat(14u);
v___x_639_ = lean_unsigned_to_nat(22u);
v___x_640_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__1));
v___x_641_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__0));
v___x_642_ = l_mkPanicMessageWithDecl(v___x_641_, v___x_640_, v___x_639_, v___x_638_, v___x_637_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___redArg(lean_object* v_cmp_643_, lean_object* v_inst_644_, lean_object* v_t_645_, lean_object* v_k_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_box(0);
v___x_648_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_643_, v_k_646_, v___x_647_, v_t_645_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_650_ = l_panic___redArg(v_inst_644_, v___x_649_);
return v___x_650_;
}
else
{
lean_object* v_val_651_; 
v_val_651_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v___x_648_, 1);
return v_val_651_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___redArg___boxed(lean_object* v_cmp_652_, lean_object* v_inst_653_, lean_object* v_t_654_, lean_object* v_k_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Std_ExtTreeSet_getGE_x21___redArg(v_cmp_652_, v_inst_653_, v_t_654_, v_k_655_);
lean_dec(v_inst_653_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21(lean_object* v_00_u03b1_657_, lean_object* v_cmp_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_t_661_, lean_object* v_k_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_box(0);
v___x_664_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_658_, v_k_662_, v___x_663_, v_t_661_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_666_ = l_panic___redArg(v_inst_660_, v___x_665_);
return v___x_666_;
}
else
{
lean_object* v_val_667_; 
v_val_667_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v___x_664_, 1);
return v_val_667_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___boxed(lean_object* v_00_u03b1_668_, lean_object* v_cmp_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_t_672_, lean_object* v_k_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_ExtTreeSet_getGE_x21(v_00_u03b1_668_, v_cmp_669_, v_inst_670_, v_inst_671_, v_t_672_, v_k_673_);
lean_dec(v_inst_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg(lean_object* v_cmp_675_, lean_object* v_inst_676_, lean_object* v_t_677_, lean_object* v_k_678_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_box(0);
v___x_680_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_675_, v_k_678_, v___x_679_, v_t_677_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_682_ = l_panic___redArg(v_inst_676_, v___x_681_);
return v___x_682_;
}
else
{
lean_object* v_val_683_; 
v_val_683_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v___x_680_, 1);
return v_val_683_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg___boxed(lean_object* v_cmp_684_, lean_object* v_inst_685_, lean_object* v_t_686_, lean_object* v_k_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_ExtTreeSet_getGT_x21___redArg(v_cmp_684_, v_inst_685_, v_t_686_, v_k_687_);
lean_dec(v_inst_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21(lean_object* v_00_u03b1_689_, lean_object* v_cmp_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_t_693_, lean_object* v_k_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_box(0);
v___x_696_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_690_, v_k_694_, v___x_695_, v_t_693_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_698_ = l_panic___redArg(v_inst_692_, v___x_697_);
return v___x_698_;
}
else
{
lean_object* v_val_699_; 
v_val_699_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v___x_696_, 1);
return v_val_699_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___boxed(lean_object* v_00_u03b1_700_, lean_object* v_cmp_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_t_704_, lean_object* v_k_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_ExtTreeSet_getGT_x21(v_00_u03b1_700_, v_cmp_701_, v_inst_702_, v_inst_703_, v_t_704_, v_k_705_);
lean_dec(v_inst_703_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg(lean_object* v_cmp_707_, lean_object* v_inst_708_, lean_object* v_t_709_, lean_object* v_k_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_box(0);
v___x_712_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_707_, v_k_710_, v___x_711_, v_t_709_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_714_ = l_panic___redArg(v_inst_708_, v___x_713_);
return v___x_714_;
}
else
{
lean_object* v_val_715_; 
v_val_715_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_val_715_);
lean_dec_ref_known(v___x_712_, 1);
return v_val_715_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg___boxed(lean_object* v_cmp_716_, lean_object* v_inst_717_, lean_object* v_t_718_, lean_object* v_k_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_ExtTreeSet_getLE_x21___redArg(v_cmp_716_, v_inst_717_, v_t_718_, v_k_719_);
lean_dec(v_inst_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21(lean_object* v_00_u03b1_721_, lean_object* v_cmp_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_t_725_, lean_object* v_k_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_box(0);
v___x_728_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_722_, v_k_726_, v___x_727_, v_t_725_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_730_ = l_panic___redArg(v_inst_724_, v___x_729_);
return v___x_730_;
}
else
{
lean_object* v_val_731_; 
v_val_731_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_val_731_);
lean_dec_ref_known(v___x_728_, 1);
return v_val_731_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___boxed(lean_object* v_00_u03b1_732_, lean_object* v_cmp_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_t_736_, lean_object* v_k_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_ExtTreeSet_getLE_x21(v_00_u03b1_732_, v_cmp_733_, v_inst_734_, v_inst_735_, v_t_736_, v_k_737_);
lean_dec(v_inst_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg(lean_object* v_cmp_739_, lean_object* v_inst_740_, lean_object* v_t_741_, lean_object* v_k_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_box(0);
v___x_744_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_739_, v_k_742_, v___x_743_, v_t_741_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_746_ = l_panic___redArg(v_inst_740_, v___x_745_);
return v___x_746_;
}
else
{
lean_object* v_val_747_; 
v_val_747_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_val_747_);
lean_dec_ref_known(v___x_744_, 1);
return v_val_747_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg___boxed(lean_object* v_cmp_748_, lean_object* v_inst_749_, lean_object* v_t_750_, lean_object* v_k_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Std_ExtTreeSet_getLT_x21___redArg(v_cmp_748_, v_inst_749_, v_t_750_, v_k_751_);
lean_dec(v_inst_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21(lean_object* v_00_u03b1_753_, lean_object* v_cmp_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_t_757_, lean_object* v_k_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_box(0);
v___x_760_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_754_, v_k_758_, v___x_759_, v_t_757_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_762_ = l_panic___redArg(v_inst_756_, v___x_761_);
return v___x_762_;
}
else
{
lean_object* v_val_763_; 
v_val_763_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_val_763_);
lean_dec_ref_known(v___x_760_, 1);
return v_val_763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___boxed(lean_object* v_00_u03b1_764_, lean_object* v_cmp_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_t_768_, lean_object* v_k_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_ExtTreeSet_getLT_x21(v_00_u03b1_764_, v_cmp_765_, v_inst_766_, v_inst_767_, v_t_768_, v_k_769_);
lean_dec(v_inst_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg(lean_object* v_cmp_771_, lean_object* v_t_772_, lean_object* v_k_773_, lean_object* v_fallback_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_box(0);
v___x_776_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_771_, v_k_773_, v___x_775_, v_t_772_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_inc(v_fallback_774_);
return v_fallback_774_;
}
else
{
lean_object* v_val_777_; 
v_val_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v___x_776_, 1);
return v_val_777_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg___boxed(lean_object* v_cmp_778_, lean_object* v_t_779_, lean_object* v_k_780_, lean_object* v_fallback_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Std_ExtTreeSet_getGED___redArg(v_cmp_778_, v_t_779_, v_k_780_, v_fallback_781_);
lean_dec(v_fallback_781_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED(lean_object* v_00_u03b1_783_, lean_object* v_cmp_784_, lean_object* v_inst_785_, lean_object* v_t_786_, lean_object* v_k_787_, lean_object* v_fallback_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_box(0);
v___x_790_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_784_, v_k_787_, v___x_789_, v_t_786_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_inc(v_fallback_788_);
return v_fallback_788_;
}
else
{
lean_object* v_val_791_; 
v_val_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_val_791_);
lean_dec_ref_known(v___x_790_, 1);
return v_val_791_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___boxed(lean_object* v_00_u03b1_792_, lean_object* v_cmp_793_, lean_object* v_inst_794_, lean_object* v_t_795_, lean_object* v_k_796_, lean_object* v_fallback_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_ExtTreeSet_getGED(v_00_u03b1_792_, v_cmp_793_, v_inst_794_, v_t_795_, v_k_796_, v_fallback_797_);
lean_dec(v_fallback_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg(lean_object* v_cmp_799_, lean_object* v_t_800_, lean_object* v_k_801_, lean_object* v_fallback_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_box(0);
v___x_804_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_799_, v_k_801_, v___x_803_, v_t_800_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_inc(v_fallback_802_);
return v_fallback_802_;
}
else
{
lean_object* v_val_805_; 
v_val_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_val_805_);
lean_dec_ref_known(v___x_804_, 1);
return v_val_805_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg___boxed(lean_object* v_cmp_806_, lean_object* v_t_807_, lean_object* v_k_808_, lean_object* v_fallback_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_ExtTreeSet_getGTD___redArg(v_cmp_806_, v_t_807_, v_k_808_, v_fallback_809_);
lean_dec(v_fallback_809_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD(lean_object* v_00_u03b1_811_, lean_object* v_cmp_812_, lean_object* v_inst_813_, lean_object* v_t_814_, lean_object* v_k_815_, lean_object* v_fallback_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_box(0);
v___x_818_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_812_, v_k_815_, v___x_817_, v_t_814_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_inc(v_fallback_816_);
return v_fallback_816_;
}
else
{
lean_object* v_val_819_; 
v_val_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_val_819_);
lean_dec_ref_known(v___x_818_, 1);
return v_val_819_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___boxed(lean_object* v_00_u03b1_820_, lean_object* v_cmp_821_, lean_object* v_inst_822_, lean_object* v_t_823_, lean_object* v_k_824_, lean_object* v_fallback_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_ExtTreeSet_getGTD(v_00_u03b1_820_, v_cmp_821_, v_inst_822_, v_t_823_, v_k_824_, v_fallback_825_);
lean_dec(v_fallback_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg(lean_object* v_cmp_827_, lean_object* v_t_828_, lean_object* v_k_829_, lean_object* v_fallback_830_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_box(0);
v___x_832_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_827_, v_k_829_, v___x_831_, v_t_828_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_inc(v_fallback_830_);
return v_fallback_830_;
}
else
{
lean_object* v_val_833_; 
v_val_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v___x_832_, 1);
return v_val_833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg___boxed(lean_object* v_cmp_834_, lean_object* v_t_835_, lean_object* v_k_836_, lean_object* v_fallback_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_ExtTreeSet_getLED___redArg(v_cmp_834_, v_t_835_, v_k_836_, v_fallback_837_);
lean_dec(v_fallback_837_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED(lean_object* v_00_u03b1_839_, lean_object* v_cmp_840_, lean_object* v_inst_841_, lean_object* v_t_842_, lean_object* v_k_843_, lean_object* v_fallback_844_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_box(0);
v___x_846_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_840_, v_k_843_, v___x_845_, v_t_842_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_inc(v_fallback_844_);
return v_fallback_844_;
}
else
{
lean_object* v_val_847_; 
v_val_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v___x_846_, 1);
return v_val_847_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___boxed(lean_object* v_00_u03b1_848_, lean_object* v_cmp_849_, lean_object* v_inst_850_, lean_object* v_t_851_, lean_object* v_k_852_, lean_object* v_fallback_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_ExtTreeSet_getLED(v_00_u03b1_848_, v_cmp_849_, v_inst_850_, v_t_851_, v_k_852_, v_fallback_853_);
lean_dec(v_fallback_853_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg(lean_object* v_cmp_855_, lean_object* v_t_856_, lean_object* v_k_857_, lean_object* v_fallback_858_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_box(0);
v___x_860_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_855_, v_k_857_, v___x_859_, v_t_856_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_inc(v_fallback_858_);
return v_fallback_858_;
}
else
{
lean_object* v_val_861_; 
v_val_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_val_861_);
lean_dec_ref_known(v___x_860_, 1);
return v_val_861_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg___boxed(lean_object* v_cmp_862_, lean_object* v_t_863_, lean_object* v_k_864_, lean_object* v_fallback_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_ExtTreeSet_getLTD___redArg(v_cmp_862_, v_t_863_, v_k_864_, v_fallback_865_);
lean_dec(v_fallback_865_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD(lean_object* v_00_u03b1_867_, lean_object* v_cmp_868_, lean_object* v_inst_869_, lean_object* v_t_870_, lean_object* v_k_871_, lean_object* v_fallback_872_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_box(0);
v___x_874_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_868_, v_k_871_, v___x_873_, v_t_870_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_inc(v_fallback_872_);
return v_fallback_872_;
}
else
{
lean_object* v_val_875_; 
v_val_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_875_);
lean_dec_ref_known(v___x_874_, 1);
return v_val_875_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___boxed(lean_object* v_00_u03b1_876_, lean_object* v_cmp_877_, lean_object* v_inst_878_, lean_object* v_t_879_, lean_object* v_k_880_, lean_object* v_fallback_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_ExtTreeSet_getLTD(v_00_u03b1_876_, v_cmp_877_, v_inst_878_, v_t_879_, v_k_880_, v_fallback_881_);
lean_dec(v_fallback_881_);
return v_res_882_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_filter___redArg___lam__0(lean_object* v_f_883_, lean_object* v_a_884_, lean_object* v_x_885_){
_start:
{
lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_886_ = lean_apply_1(v_f_883_, v_a_884_);
v___x_887_ = lean_unbox(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg___lam__0___boxed(lean_object* v_f_888_, lean_object* v_a_889_, lean_object* v_x_890_){
_start:
{
uint8_t v_res_891_; lean_object* v_r_892_; 
v_res_891_ = l_Std_ExtTreeSet_filter___redArg___lam__0(v_f_888_, v_a_889_, v_x_890_);
v_r_892_ = lean_box(v_res_891_);
return v_r_892_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg(lean_object* v_f_893_, lean_object* v_m_894_){
_start:
{
lean_object* v___f_895_; lean_object* v___x_896_; 
v___f_895_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_895_, 0, v_f_893_);
v___x_896_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_895_, v_m_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter(lean_object* v_00_u03b1_897_, lean_object* v_cmp_898_, lean_object* v_f_899_, lean_object* v_m_900_){
_start:
{
lean_object* v___f_901_; lean_object* v___x_902_; 
v___f_901_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_901_, 0, v_f_899_);
v___x_902_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_901_, v_m_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___boxed(lean_object* v_00_u03b1_903_, lean_object* v_cmp_904_, lean_object* v_f_905_, lean_object* v_m_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_ExtTreeSet_filter(v_00_u03b1_903_, v_cmp_904_, v_f_905_, v_m_906_);
lean_dec_ref(v_cmp_904_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg___lam__0(lean_object* v_f_908_, lean_object* v_c_909_, lean_object* v_a_910_, lean_object* v_x_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_apply_2(v_f_908_, v_c_909_, v_a_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg(lean_object* v_inst_913_, lean_object* v_f_914_, lean_object* v_init_915_, lean_object* v_t_916_){
_start:
{
lean_object* v___f_917_; lean_object* v___x_918_; 
v___f_917_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_917_, 0, v_f_914_);
v___x_918_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_913_, v___f_917_, v_init_915_, v_t_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM(lean_object* v_00_u03b1_919_, lean_object* v_cmp_920_, lean_object* v_00_u03b4_921_, lean_object* v_m_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_f_926_, lean_object* v_init_927_, lean_object* v_t_928_){
_start:
{
lean_object* v___f_929_; lean_object* v___x_930_; 
v___f_929_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_929_, 0, v_f_926_);
v___x_930_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_923_, v___f_929_, v_init_927_, v_t_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___boxed(lean_object* v_00_u03b1_931_, lean_object* v_cmp_932_, lean_object* v_00_u03b4_933_, lean_object* v_m_934_, lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_f_938_, lean_object* v_init_939_, lean_object* v_t_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_ExtTreeSet_foldlM(v_00_u03b1_931_, v_cmp_932_, v_00_u03b4_933_, v_m_934_, v_inst_935_, v_inst_936_, v_inst_937_, v_f_938_, v_init_939_, v_t_940_);
lean_dec_ref(v_cmp_932_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___redArg(lean_object* v_f_942_, lean_object* v_init_943_, lean_object* v_t_944_){
_start:
{
lean_object* v___f_945_; lean_object* v___x_946_; 
v___f_945_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_945_, 0, v_f_942_);
v___x_946_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_945_, v_init_943_, v_t_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl(lean_object* v_00_u03b1_947_, lean_object* v_cmp_948_, lean_object* v_00_u03b4_949_, lean_object* v_inst_950_, lean_object* v_f_951_, lean_object* v_init_952_, lean_object* v_t_953_){
_start:
{
lean_object* v___f_954_; lean_object* v___x_955_; 
v___f_954_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_954_, 0, v_f_951_);
v___x_955_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_954_, v_init_952_, v_t_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___boxed(lean_object* v_00_u03b1_956_, lean_object* v_cmp_957_, lean_object* v_00_u03b4_958_, lean_object* v_inst_959_, lean_object* v_f_960_, lean_object* v_init_961_, lean_object* v_t_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_ExtTreeSet_foldl(v_00_u03b1_956_, v_cmp_957_, v_00_u03b4_958_, v_inst_959_, v_f_960_, v_init_961_, v_t_962_);
lean_dec_ref(v_cmp_957_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg___lam__0(lean_object* v_f_964_, lean_object* v_a_965_, lean_object* v_x_966_, lean_object* v_acc_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = lean_apply_2(v_f_964_, v_a_965_, v_acc_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg(lean_object* v_inst_969_, lean_object* v_f_970_, lean_object* v_init_971_, lean_object* v_t_972_){
_start:
{
lean_object* v___f_973_; lean_object* v___x_974_; 
v___f_973_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_973_, 0, v_f_970_);
v___x_974_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_969_, v___f_973_, v_init_971_, v_t_972_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM(lean_object* v_00_u03b1_975_, lean_object* v_cmp_976_, lean_object* v_00_u03b4_977_, lean_object* v_m_978_, lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_f_982_, lean_object* v_init_983_, lean_object* v_t_984_){
_start:
{
lean_object* v___f_985_; lean_object* v___x_986_; 
v___f_985_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_985_, 0, v_f_982_);
v___x_986_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_979_, v___f_985_, v_init_983_, v_t_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___boxed(lean_object* v_00_u03b1_987_, lean_object* v_cmp_988_, lean_object* v_00_u03b4_989_, lean_object* v_m_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_f_994_, lean_object* v_init_995_, lean_object* v_t_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std_ExtTreeSet_foldrM(v_00_u03b1_987_, v_cmp_988_, v_00_u03b4_989_, v_m_990_, v_inst_991_, v_inst_992_, v_inst_993_, v_f_994_, v_init_995_, v_t_996_);
lean_dec_ref(v_cmp_988_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg___lam__0(lean_object* v_f_998_, lean_object* v_x1_999_, lean_object* v_x2_1000_, lean_object* v_x3_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_apply_2(v_f_998_, v_x1_999_, v_x3_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg(lean_object* v_f_1022_, lean_object* v_init_1023_, lean_object* v_t_1024_){
_start:
{
lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___f_1025_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1025_, 0, v_f_1022_);
v___x_1026_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1027_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1026_, v___f_1025_, v_init_1023_, v_t_1024_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr(lean_object* v_00_u03b1_1028_, lean_object* v_cmp_1029_, lean_object* v_00_u03b4_1030_, lean_object* v_inst_1031_, lean_object* v_f_1032_, lean_object* v_init_1033_, lean_object* v_t_1034_){
_start:
{
lean_object* v___f_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___f_1035_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1035_, 0, v_f_1032_);
v___x_1036_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1037_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1036_, v___f_1035_, v_init_1033_, v_t_1034_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___boxed(lean_object* v_00_u03b1_1038_, lean_object* v_cmp_1039_, lean_object* v_00_u03b4_1040_, lean_object* v_inst_1041_, lean_object* v_f_1042_, lean_object* v_init_1043_, lean_object* v_t_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Std_ExtTreeSet_foldr(v_00_u03b1_1038_, v_cmp_1039_, v_00_u03b4_1040_, v_inst_1041_, v_f_1042_, v_init_1043_, v_t_1044_);
lean_dec_ref(v_cmp_1039_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg___lam__0(lean_object* v_f_1046_, lean_object* v_cmp_1047_, lean_object* v_x_1048_, lean_object* v_a_1049_, lean_object* v_b_1050_){
_start:
{
lean_object* v_fst_1051_; lean_object* v_snd_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1066_; 
v_fst_1051_ = lean_ctor_get(v_x_1048_, 0);
v_snd_1052_ = lean_ctor_get(v_x_1048_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_1048_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1054_ = v_x_1048_;
v_isShared_1055_ = v_isSharedCheck_1066_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_snd_1052_);
lean_inc(v_fst_1051_);
lean_dec(v_x_1048_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1066_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
lean_inc(v_a_1049_);
v___x_1056_ = lean_apply_1(v_f_1046_, v_a_1049_);
v___x_1057_ = lean_unbox(v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1058_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1047_, v_a_1049_, v_b_1050_, v_snd_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v___x_1058_);
v___x_1060_ = v___x_1054_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_fst_1051_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1062_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1047_, v_a_1049_, v_b_1050_, v_fst_1051_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1062_);
v___x_1064_ = v___x_1054_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_snd_1052_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg(lean_object* v_cmp_1069_, lean_object* v_f_1070_, lean_object* v_t_1071_){
_start:
{
lean_object* v___f_1072_; lean_object* v___x_1073_; lean_object* v_p_1074_; lean_object* v_fst_1075_; lean_object* v_snd_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v___f_1072_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1072_, 0, v_f_1070_);
lean_closure_set(v___f_1072_, 1, v_cmp_1069_);
v___x_1073_ = ((lean_object*)(l_Std_ExtTreeSet_partition___redArg___closed__0));
v_p_1074_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1072_, v___x_1073_, v_t_1071_);
v_fst_1075_ = lean_ctor_get(v_p_1074_, 0);
v_snd_1076_ = lean_ctor_get(v_p_1074_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_p_1074_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v_p_1074_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_snd_1076_);
lean_inc(v_fst_1075_);
lean_dec(v_p_1074_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_fst_1075_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_snd_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition(lean_object* v_00_u03b1_1084_, lean_object* v_cmp_1085_, lean_object* v_inst_1086_, lean_object* v_f_1087_, lean_object* v_t_1088_){
_start:
{
lean_object* v___f_1089_; lean_object* v___x_1090_; lean_object* v_p_1091_; lean_object* v_fst_1092_; lean_object* v_snd_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v___f_1089_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1089_, 0, v_f_1087_);
lean_closure_set(v___f_1089_, 1, v_cmp_1085_);
v___x_1090_ = ((lean_object*)(l_Std_ExtTreeSet_partition___redArg___closed__0));
v_p_1091_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1089_, v___x_1090_, v_t_1088_);
v_fst_1092_ = lean_ctor_get(v_p_1091_, 0);
v_snd_1093_ = lean_ctor_get(v_p_1091_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_p_1091_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v_p_1091_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_snd_1093_);
lean_inc(v_fst_1092_);
lean_dec(v_p_1091_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_fst_1092_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_snd_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg___lam__0(lean_object* v_f_1101_, lean_object* v_x_1102_, lean_object* v_k_1103_, lean_object* v_v_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_apply_1(v_f_1101_, v_k_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg(lean_object* v_inst_1106_, lean_object* v_f_1107_, lean_object* v_t_1108_){
_start:
{
lean_object* v___f_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___f_1109_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1109_, 0, v_f_1107_);
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1106_, v___f_1109_, v___x_1110_, v_t_1108_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM(lean_object* v_00_u03b1_1112_, lean_object* v_cmp_1113_, lean_object* v_m_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_f_1118_, lean_object* v_t_1119_){
_start:
{
lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___f_1120_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1120_, 0, v_f_1118_);
v___x_1121_ = lean_box(0);
v___x_1122_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1115_, v___f_1120_, v___x_1121_, v_t_1119_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___boxed(lean_object* v_00_u03b1_1123_, lean_object* v_cmp_1124_, lean_object* v_m_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_f_1129_, lean_object* v_t_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Std_ExtTreeSet_forM(v_00_u03b1_1123_, v_cmp_1124_, v_m_1125_, v_inst_1126_, v_inst_1127_, v_inst_1128_, v_f_1129_, v_t_1130_);
lean_dec_ref(v_cmp_1124_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__0(lean_object* v_f_1132_, lean_object* v_a_1133_, lean_object* v_b_1134_, lean_object* v_c_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_apply_2(v_f_1132_, v_a_1133_, v_c_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__1(lean_object* v_toPure_1137_, lean_object* v_____do__lift_1138_){
_start:
{
lean_object* v_a_1139_; lean_object* v___x_1140_; 
v_a_1139_ = lean_ctor_get(v_____do__lift_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref(v_____do__lift_1138_);
v___x_1140_ = lean_apply_2(v_toPure_1137_, lean_box(0), v_a_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg(lean_object* v_inst_1141_, lean_object* v_f_1142_, lean_object* v_init_1143_, lean_object* v_t_1144_){
_start:
{
lean_object* v_toApplicative_1145_; lean_object* v_toBind_1146_; lean_object* v_toPure_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; 
v_toApplicative_1145_ = lean_ctor_get(v_inst_1141_, 0);
v_toBind_1146_ = lean_ctor_get(v_inst_1141_, 1);
lean_inc(v_toBind_1146_);
v_toPure_1147_ = lean_ctor_get(v_toApplicative_1145_, 1);
lean_inc(v_toPure_1147_);
v___f_1148_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1148_, 0, v_f_1142_);
v___x_1149_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1141_, v___f_1148_, v_init_1143_, v_t_1144_);
v___f_1150_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1150_, 0, v_toPure_1147_);
v___x_1151_ = lean_apply_4(v_toBind_1146_, lean_box(0), lean_box(0), v___x_1149_, v___f_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn(lean_object* v_00_u03b1_1152_, lean_object* v_cmp_1153_, lean_object* v_00_u03b4_1154_, lean_object* v_m_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_f_1159_, lean_object* v_init_1160_, lean_object* v_t_1161_){
_start:
{
lean_object* v_toApplicative_1162_; lean_object* v_toBind_1163_; lean_object* v_toPure_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___f_1167_; lean_object* v___x_1168_; 
v_toApplicative_1162_ = lean_ctor_get(v_inst_1156_, 0);
v_toBind_1163_ = lean_ctor_get(v_inst_1156_, 1);
lean_inc(v_toBind_1163_);
v_toPure_1164_ = lean_ctor_get(v_toApplicative_1162_, 1);
lean_inc(v_toPure_1164_);
v___f_1165_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1165_, 0, v_f_1159_);
v___x_1166_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1156_, v___f_1165_, v_init_1160_, v_t_1161_);
v___f_1167_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1167_, 0, v_toPure_1164_);
v___x_1168_ = lean_apply_4(v_toBind_1163_, lean_box(0), lean_box(0), v___x_1166_, v___f_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_cmp_1170_, lean_object* v_00_u03b4_1171_, lean_object* v_m_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_f_1176_, lean_object* v_init_1177_, lean_object* v_t_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Std_ExtTreeSet_forIn(v_00_u03b1_1169_, v_cmp_1170_, v_00_u03b4_1171_, v_m_1172_, v_inst_1173_, v_inst_1174_, v_inst_1175_, v_f_1176_, v_init_1177_, v_t_1178_);
lean_dec_ref(v_cmp_1170_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_1180_, lean_object* v_t_1181_, lean_object* v_f_1182_){
_start:
{
lean_object* v___f_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___f_1183_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1183_, 0, v_f_1182_);
v___x_1184_ = lean_box(0);
v___x_1185_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1180_, v___f_1183_, v___x_1184_, v_t_1181_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1186_){
_start:
{
lean_object* v___f_1187_; 
v___f_1187_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1187_, 0, v_inst_1186_);
return v___f_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1188_, lean_object* v_cmp_1189_, lean_object* v_m_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_){
_start:
{
lean_object* v___f_1194_; 
v___f_1194_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1194_, 0, v_inst_1192_);
return v___f_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1195_, lean_object* v_cmp_1196_, lean_object* v_m_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(v_00_u03b1_1195_, v_cmp_1196_, v_m_1197_, v_inst_1198_, v_inst_1199_, v_inst_1200_);
lean_dec_ref(v_cmp_1196_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_1202_, lean_object* v_00_u03b2_1203_, lean_object* v_m_1204_, lean_object* v_init_1205_, lean_object* v_f_1206_){
_start:
{
lean_object* v_toApplicative_1207_; lean_object* v_toBind_1208_; lean_object* v_toPure_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v___f_1212_; lean_object* v___x_1213_; 
v_toApplicative_1207_ = lean_ctor_get(v_inst_1202_, 0);
v_toBind_1208_ = lean_ctor_get(v_inst_1202_, 1);
lean_inc(v_toBind_1208_);
v_toPure_1209_ = lean_ctor_get(v_toApplicative_1207_, 1);
lean_inc(v_toPure_1209_);
v___f_1210_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1210_, 0, v_f_1206_);
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1202_, v___f_1210_, v_init_1205_, v_m_1204_);
v___f_1212_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1212_, 0, v_toPure_1209_);
v___x_1213_ = lean_apply_4(v_toBind_1208_, lean_box(0), lean_box(0), v___x_1211_, v___f_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1214_){
_start:
{
lean_object* v___f_1215_; 
v___f_1215_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1215_, 0, v_inst_1214_);
return v___f_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1216_, lean_object* v_cmp_1217_, lean_object* v_m_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_){
_start:
{
lean_object* v___f_1222_; 
v___f_1222_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1222_, 0, v_inst_1220_);
return v___f_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1223_, lean_object* v_cmp_1224_, lean_object* v_m_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(v_00_u03b1_1223_, v_cmp_1224_, v_m_1225_, v_inst_1226_, v_inst_1227_, v_inst_1228_);
lean_dec_ref(v_cmp_1224_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0(lean_object* v_p_1230_, lean_object* v___x_1231_, lean_object* v___x_1232_, lean_object* v_a_1233_, lean_object* v_b_1234_, lean_object* v_acc_1235_){
_start:
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = lean_apply_1(v_p_1230_, v_a_1233_);
v___x_1237_ = lean_unbox(v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1231_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec_ref(v___x_1231_);
v___x_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1236_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___x_1232_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0___boxed(lean_object* v_p_1242_, lean_object* v___x_1243_, lean_object* v___x_1244_, lean_object* v_a_1245_, lean_object* v_b_1246_, lean_object* v_acc_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_ExtTreeSet_any___redArg___lam__0(v_p_1242_, v___x_1243_, v___x_1244_, v_a_1245_, v_b_1246_, v_acc_1247_);
lean_dec_ref(v_acc_1247_);
return v_res_1248_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_any___redArg(lean_object* v_t_1252_, lean_object* v_p_1253_){
_start:
{
lean_object* v___y_1255_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; lean_object* v_a_1265_; 
v___x_1260_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1261_ = lean_box(0);
v___x_1262_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1263_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1263_, 0, v_p_1253_);
lean_closure_set(v___f_1263_, 1, v___x_1262_);
lean_closure_set(v___f_1263_, 2, v___x_1261_);
v___x_1264_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1260_, v___f_1263_, v___x_1262_, v_t_1252_);
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___y_1255_ = v_a_1265_;
goto v___jp_1254_;
v___jp_1254_:
{
lean_object* v_fst_1256_; 
v_fst_1256_ = lean_ctor_get(v___y_1255_, 0);
lean_inc(v_fst_1256_);
lean_dec_ref(v___y_1255_);
if (lean_obj_tag(v_fst_1256_) == 0)
{
uint8_t v___x_1257_; 
v___x_1257_ = 0;
return v___x_1257_;
}
else
{
lean_object* v_val_1258_; uint8_t v___x_1259_; 
v_val_1258_ = lean_ctor_get(v_fst_1256_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v_fst_1256_, 1);
v___x_1259_ = lean_unbox(v_val_1258_);
lean_dec(v_val_1258_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___boxed(lean_object* v_t_1266_, lean_object* v_p_1267_){
_start:
{
uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l_Std_ExtTreeSet_any___redArg(v_t_1266_, v_p_1267_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_any(lean_object* v_00_u03b1_1270_, lean_object* v_cmp_1271_, lean_object* v_inst_1272_, lean_object* v_t_1273_, lean_object* v_p_1274_){
_start:
{
lean_object* v___y_1276_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___f_1284_; lean_object* v___x_1285_; lean_object* v_a_1286_; 
v___x_1281_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1282_ = lean_box(0);
v___x_1283_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1284_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1284_, 0, v_p_1274_);
lean_closure_set(v___f_1284_, 1, v___x_1283_);
lean_closure_set(v___f_1284_, 2, v___x_1282_);
v___x_1285_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1281_, v___f_1284_, v___x_1283_, v_t_1273_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___y_1276_ = v_a_1286_;
goto v___jp_1275_;
v___jp_1275_:
{
lean_object* v_fst_1277_; 
v_fst_1277_ = lean_ctor_get(v___y_1276_, 0);
lean_inc(v_fst_1277_);
lean_dec_ref(v___y_1276_);
if (lean_obj_tag(v_fst_1277_) == 0)
{
uint8_t v___x_1278_; 
v___x_1278_ = 0;
return v___x_1278_;
}
else
{
lean_object* v_val_1279_; uint8_t v___x_1280_; 
v_val_1279_ = lean_ctor_get(v_fst_1277_, 0);
lean_inc(v_val_1279_);
lean_dec_ref_known(v_fst_1277_, 1);
v___x_1280_ = lean_unbox(v_val_1279_);
lean_dec(v_val_1279_);
return v___x_1280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___boxed(lean_object* v_00_u03b1_1287_, lean_object* v_cmp_1288_, lean_object* v_inst_1289_, lean_object* v_t_1290_, lean_object* v_p_1291_){
_start:
{
uint8_t v_res_1292_; lean_object* v_r_1293_; 
v_res_1292_ = l_Std_ExtTreeSet_any(v_00_u03b1_1287_, v_cmp_1288_, v_inst_1289_, v_t_1290_, v_p_1291_);
lean_dec_ref(v_cmp_1288_);
v_r_1293_ = lean_box(v_res_1292_);
return v_r_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0(lean_object* v_p_1294_, lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v_a_1297_, lean_object* v_b_1298_, lean_object* v_acc_1299_){
_start:
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = lean_apply_1(v_p_1294_, v_a_1297_);
v___x_1301_ = lean_unbox(v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec_ref(v___x_1296_);
v___x_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v___x_1295_);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1296_);
return v___x_1305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0___boxed(lean_object* v_p_1306_, lean_object* v___x_1307_, lean_object* v___x_1308_, lean_object* v_a_1309_, lean_object* v_b_1310_, lean_object* v_acc_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Std_ExtTreeSet_all___redArg___lam__0(v_p_1306_, v___x_1307_, v___x_1308_, v_a_1309_, v_b_1310_, v_acc_1311_);
lean_dec_ref(v_acc_1311_);
return v_res_1312_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_all___redArg(lean_object* v_t_1313_, lean_object* v_p_1314_){
_start:
{
lean_object* v___y_1316_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___f_1324_; lean_object* v___x_1325_; lean_object* v_a_1326_; 
v___x_1321_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1322_ = lean_box(0);
v___x_1323_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1324_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1324_, 0, v_p_1314_);
lean_closure_set(v___f_1324_, 1, v___x_1322_);
lean_closure_set(v___f_1324_, 2, v___x_1323_);
v___x_1325_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1321_, v___f_1324_, v___x_1323_, v_t_1313_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___y_1316_ = v_a_1326_;
goto v___jp_1315_;
v___jp_1315_:
{
lean_object* v_fst_1317_; 
v_fst_1317_ = lean_ctor_get(v___y_1316_, 0);
lean_inc(v_fst_1317_);
lean_dec_ref(v___y_1316_);
if (lean_obj_tag(v_fst_1317_) == 0)
{
uint8_t v___x_1318_; 
v___x_1318_ = 1;
return v___x_1318_;
}
else
{
lean_object* v_val_1319_; uint8_t v___x_1320_; 
v_val_1319_ = lean_ctor_get(v_fst_1317_, 0);
lean_inc(v_val_1319_);
lean_dec_ref_known(v_fst_1317_, 1);
v___x_1320_ = lean_unbox(v_val_1319_);
lean_dec(v_val_1319_);
return v___x_1320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___boxed(lean_object* v_t_1327_, lean_object* v_p_1328_){
_start:
{
uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_res_1329_ = l_Std_ExtTreeSet_all___redArg(v_t_1327_, v_p_1328_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_all(lean_object* v_00_u03b1_1331_, lean_object* v_cmp_1332_, lean_object* v_inst_1333_, lean_object* v_t_1334_, lean_object* v_p_1335_){
_start:
{
lean_object* v___y_1337_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___f_1345_; lean_object* v___x_1346_; lean_object* v_a_1347_; 
v___x_1342_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1343_ = lean_box(0);
v___x_1344_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1345_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1345_, 0, v_p_1335_);
lean_closure_set(v___f_1345_, 1, v___x_1343_);
lean_closure_set(v___f_1345_, 2, v___x_1344_);
v___x_1346_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1342_, v___f_1345_, v___x_1344_, v_t_1334_);
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___y_1337_ = v_a_1347_;
goto v___jp_1336_;
v___jp_1336_:
{
lean_object* v_fst_1338_; 
v_fst_1338_ = lean_ctor_get(v___y_1337_, 0);
lean_inc(v_fst_1338_);
lean_dec_ref(v___y_1337_);
if (lean_obj_tag(v_fst_1338_) == 0)
{
uint8_t v___x_1339_; 
v___x_1339_ = 1;
return v___x_1339_;
}
else
{
lean_object* v_val_1340_; uint8_t v___x_1341_; 
v_val_1340_ = lean_ctor_get(v_fst_1338_, 0);
lean_inc(v_val_1340_);
lean_dec_ref_known(v_fst_1338_, 1);
v___x_1341_ = lean_unbox(v_val_1340_);
lean_dec(v_val_1340_);
return v___x_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___boxed(lean_object* v_00_u03b1_1348_, lean_object* v_cmp_1349_, lean_object* v_inst_1350_, lean_object* v_t_1351_, lean_object* v_p_1352_){
_start:
{
uint8_t v_res_1353_; lean_object* v_r_1354_; 
v_res_1353_ = l_Std_ExtTreeSet_all(v_00_u03b1_1348_, v_cmp_1349_, v_inst_1350_, v_t_1351_, v_p_1352_);
lean_dec_ref(v_cmp_1349_);
v_r_1354_ = lean_box(v_res_1353_);
return v_r_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg___lam__0(lean_object* v_x1_1355_, lean_object* v_x2_1356_, lean_object* v_x3_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1358_, 0, v_x1_1355_);
lean_ctor_set(v___x_1358_, 1, v_x3_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg(lean_object* v_t_1360_){
_start:
{
lean_object* v___f_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___f_1361_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___x_1362_ = lean_box(0);
v___x_1363_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1364_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1363_, v___f_1361_, v___x_1362_, v_t_1360_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList(lean_object* v_00_u03b1_1365_, lean_object* v_cmp_1366_, lean_object* v_inst_1367_, lean_object* v_t_1368_){
_start:
{
lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___f_1369_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___x_1370_ = lean_box(0);
v___x_1371_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1372_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1371_, v___f_1369_, v___x_1370_, v_t_1368_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___boxed(lean_object* v_00_u03b1_1373_, lean_object* v_cmp_1374_, lean_object* v_inst_1375_, lean_object* v_t_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Std_ExtTreeSet_toList(v_00_u03b1_1373_, v_cmp_1374_, v_inst_1375_, v_t_1376_);
lean_dec_ref(v_cmp_1374_);
return v_res_1377_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_ofList___auto__1(void){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__25, &l_Std_ExtTreeSet___auto__1___closed__25_once, _init_l_Std_ExtTreeSet___auto__1___closed__25);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(lean_object* v_cmp_1379_, lean_object* v_k_1380_, lean_object* v_v_1381_, lean_object* v_t_1382_){
_start:
{
if (lean_obj_tag(v_t_1382_) == 0)
{
lean_object* v_size_1383_; lean_object* v_k_1384_; lean_object* v_v_1385_; lean_object* v_l_1386_; lean_object* v_r_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1668_; 
v_size_1383_ = lean_ctor_get(v_t_1382_, 0);
v_k_1384_ = lean_ctor_get(v_t_1382_, 1);
v_v_1385_ = lean_ctor_get(v_t_1382_, 2);
v_l_1386_ = lean_ctor_get(v_t_1382_, 3);
v_r_1387_ = lean_ctor_get(v_t_1382_, 4);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_t_1382_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1389_ = v_t_1382_;
v_isShared_1390_ = v_isSharedCheck_1668_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_r_1387_);
lean_inc(v_l_1386_);
lean_inc(v_v_1385_);
lean_inc(v_k_1384_);
lean_inc(v_size_1383_);
lean_dec(v_t_1382_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1668_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
lean_inc_ref(v_cmp_1379_);
lean_inc(v_k_1384_);
lean_inc(v_k_1380_);
v___x_1391_ = lean_apply_2(v_cmp_1379_, v_k_1380_, v_k_1384_);
v___x_1392_ = lean_unbox(v___x_1391_);
switch(v___x_1392_)
{
case 0:
{
lean_object* v_impl_1393_; lean_object* v___x_1394_; 
lean_dec(v_size_1383_);
v_impl_1393_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1379_, v_k_1380_, v_v_1381_, v_l_1386_);
v___x_1394_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1387_) == 0)
{
lean_object* v_size_1395_; lean_object* v_size_1396_; lean_object* v_k_1397_; lean_object* v_v_1398_; lean_object* v_l_1399_; lean_object* v_r_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_size_1395_ = lean_ctor_get(v_r_1387_, 0);
v_size_1396_ = lean_ctor_get(v_impl_1393_, 0);
v_k_1397_ = lean_ctor_get(v_impl_1393_, 1);
v_v_1398_ = lean_ctor_get(v_impl_1393_, 2);
v_l_1399_ = lean_ctor_get(v_impl_1393_, 3);
v_r_1400_ = lean_ctor_get(v_impl_1393_, 4);
lean_inc(v_r_1400_);
v___x_1401_ = lean_unsigned_to_nat(3u);
v___x_1402_ = lean_nat_mul(v___x_1401_, v_size_1395_);
v___x_1403_ = lean_nat_dec_lt(v___x_1402_, v_size_1396_);
lean_dec(v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_dec(v_r_1400_);
v___x_1404_ = lean_nat_add(v___x_1394_, v_size_1396_);
v___x_1405_ = lean_nat_add(v___x_1404_, v_size_1395_);
lean_dec(v___x_1404_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 3, v_impl_1393_);
lean_ctor_set(v___x_1389_, 0, v___x_1405_);
v___x_1407_ = v___x_1389_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_impl_1393_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_r_1387_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1474_; 
lean_inc(v_l_1399_);
lean_inc(v_v_1398_);
lean_inc(v_k_1397_);
lean_inc(v_size_1396_);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_impl_1393_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; lean_object* v_unused_1479_; 
v_unused_1475_ = lean_ctor_get(v_impl_1393_, 4);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_impl_1393_, 3);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_impl_1393_, 2);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_impl_1393_, 1);
lean_dec(v_unused_1478_);
v_unused_1479_ = lean_ctor_get(v_impl_1393_, 0);
lean_dec(v_unused_1479_);
v___x_1410_ = v_impl_1393_;
v_isShared_1411_ = v_isSharedCheck_1474_;
goto v_resetjp_1409_;
}
else
{
lean_dec(v_impl_1393_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1474_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_size_1412_; lean_object* v_size_1413_; lean_object* v_k_1414_; lean_object* v_v_1415_; lean_object* v_l_1416_; lean_object* v_r_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v_size_1412_ = lean_ctor_get(v_l_1399_, 0);
v_size_1413_ = lean_ctor_get(v_r_1400_, 0);
v_k_1414_ = lean_ctor_get(v_r_1400_, 1);
v_v_1415_ = lean_ctor_get(v_r_1400_, 2);
v_l_1416_ = lean_ctor_get(v_r_1400_, 3);
v_r_1417_ = lean_ctor_get(v_r_1400_, 4);
v___x_1418_ = lean_unsigned_to_nat(2u);
v___x_1419_ = lean_nat_mul(v___x_1418_, v_size_1412_);
v___x_1420_ = lean_nat_dec_lt(v_size_1413_, v___x_1419_);
lean_dec(v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1449_; 
lean_inc(v_r_1417_);
lean_inc(v_l_1416_);
lean_inc(v_v_1415_);
lean_inc(v_k_1414_);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_r_1400_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; 
v_unused_1450_ = lean_ctor_get(v_r_1400_, 4);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_r_1400_, 3);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_r_1400_, 2);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_r_1400_, 1);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_r_1400_, 0);
lean_dec(v_unused_1454_);
v___x_1422_ = v_r_1400_;
v_isShared_1423_ = v_isSharedCheck_1449_;
goto v_resetjp_1421_;
}
else
{
lean_dec(v_r_1400_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1449_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___x_1437_; lean_object* v___y_1439_; 
v___x_1424_ = lean_nat_add(v___x_1394_, v_size_1396_);
lean_dec(v_size_1396_);
v___x_1425_ = lean_nat_add(v___x_1424_, v_size_1395_);
lean_dec(v___x_1424_);
v___x_1437_ = lean_nat_add(v___x_1394_, v_size_1412_);
if (lean_obj_tag(v_l_1416_) == 0)
{
lean_object* v_size_1447_; 
v_size_1447_ = lean_ctor_get(v_l_1416_, 0);
lean_inc(v_size_1447_);
v___y_1439_ = v_size_1447_;
goto v___jp_1438_;
}
else
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_unsigned_to_nat(0u);
v___y_1439_ = v___x_1448_;
goto v___jp_1438_;
}
v___jp_1426_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = lean_nat_add(v___y_1427_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec(v___y_1427_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_r_1387_);
lean_ctor_set(v___x_1422_, 3, v_r_1417_);
lean_ctor_set(v___x_1422_, 2, v_v_1385_);
lean_ctor_set(v___x_1422_, 1, v_k_1384_);
lean_ctor_set(v___x_1422_, 0, v___x_1430_);
v___x_1432_ = v___x_1422_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_r_1417_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v_r_1387_);
v___x_1432_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 4, v___x_1432_);
lean_ctor_set(v___x_1410_, 3, v___y_1428_);
lean_ctor_set(v___x_1410_, 2, v_v_1415_);
lean_ctor_set(v___x_1410_, 1, v_k_1414_);
lean_ctor_set(v___x_1410_, 0, v___x_1425_);
v___x_1434_ = v___x_1410_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_k_1414_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_v_1415_);
lean_ctor_set(v_reuseFailAlloc_1435_, 3, v___y_1428_);
lean_ctor_set(v_reuseFailAlloc_1435_, 4, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
v___jp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = lean_nat_add(v___x_1437_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec(v___x_1437_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_l_1416_);
lean_ctor_set(v___x_1389_, 3, v_l_1399_);
lean_ctor_set(v___x_1389_, 2, v_v_1398_);
lean_ctor_set(v___x_1389_, 1, v_k_1397_);
lean_ctor_set(v___x_1389_, 0, v___x_1440_);
v___x_1442_ = v___x_1389_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_k_1397_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_v_1398_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v_l_1399_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v_l_1416_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_nat_add(v___x_1394_, v_size_1395_);
if (lean_obj_tag(v_r_1417_) == 0)
{
lean_object* v_size_1444_; 
v_size_1444_ = lean_ctor_get(v_r_1417_, 0);
lean_inc(v_size_1444_);
v___y_1427_ = v___x_1443_;
v___y_1428_ = v___x_1442_;
v___y_1429_ = v_size_1444_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_unsigned_to_nat(0u);
v___y_1427_ = v___x_1443_;
v___y_1428_ = v___x_1442_;
v___y_1429_ = v___x_1445_;
goto v___jp_1426_;
}
}
}
}
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
lean_del_object(v___x_1389_);
v___x_1455_ = lean_nat_add(v___x_1394_, v_size_1396_);
lean_dec(v_size_1396_);
v___x_1456_ = lean_nat_add(v___x_1455_, v_size_1395_);
lean_dec(v___x_1455_);
v___x_1457_ = lean_nat_add(v___x_1394_, v_size_1395_);
v___x_1458_ = lean_nat_add(v___x_1457_, v_size_1413_);
lean_dec(v___x_1457_);
lean_inc_ref(v_r_1387_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 4, v_r_1387_);
lean_ctor_set(v___x_1410_, 3, v_r_1400_);
lean_ctor_set(v___x_1410_, 2, v_v_1385_);
lean_ctor_set(v___x_1410_, 1, v_k_1384_);
lean_ctor_set(v___x_1410_, 0, v___x_1458_);
v___x_1460_ = v___x_1410_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1473_, 3, v_r_1400_);
lean_ctor_set(v_reuseFailAlloc_1473_, 4, v_r_1387_);
v___x_1460_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
v_isSharedCheck_1467_ = !lean_is_exclusive(v_r_1387_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; 
v_unused_1468_ = lean_ctor_get(v_r_1387_, 4);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_r_1387_, 3);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_r_1387_, 2);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_r_1387_, 1);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_r_1387_, 0);
lean_dec(v_unused_1472_);
v___x_1462_ = v_r_1387_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_dec(v_r_1387_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 4, v___x_1460_);
lean_ctor_set(v___x_1462_, 3, v_l_1399_);
lean_ctor_set(v___x_1462_, 2, v_v_1398_);
lean_ctor_set(v___x_1462_, 1, v_k_1397_);
lean_ctor_set(v___x_1462_, 0, v___x_1456_);
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_k_1397_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v_v_1398_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v_l_1399_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v___x_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1480_; 
v_l_1480_ = lean_ctor_get(v_impl_1393_, 3);
if (lean_obj_tag(v_l_1480_) == 0)
{
lean_object* v_r_1481_; lean_object* v_k_1482_; lean_object* v_v_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1494_; 
lean_inc_ref(v_l_1480_);
v_r_1481_ = lean_ctor_get(v_impl_1393_, 4);
v_k_1482_ = lean_ctor_get(v_impl_1393_, 1);
v_v_1483_ = lean_ctor_get(v_impl_1393_, 2);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_impl_1393_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; lean_object* v_unused_1496_; 
v_unused_1495_ = lean_ctor_get(v_impl_1393_, 3);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_impl_1393_, 0);
lean_dec(v_unused_1496_);
v___x_1485_ = v_impl_1393_;
v_isShared_1486_ = v_isSharedCheck_1494_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_r_1481_);
lean_inc(v_v_1483_);
lean_inc(v_k_1482_);
lean_dec(v_impl_1393_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1494_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1487_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1481_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 3, v_r_1481_);
lean_ctor_set(v___x_1485_, 2, v_v_1385_);
lean_ctor_set(v___x_1485_, 1, v_k_1384_);
lean_ctor_set(v___x_1485_, 0, v___x_1394_);
v___x_1489_ = v___x_1485_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1493_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1493_, 3, v_r_1481_);
lean_ctor_set(v_reuseFailAlloc_1493_, 4, v_r_1481_);
v___x_1489_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v___x_1489_);
lean_ctor_set(v___x_1389_, 3, v_l_1480_);
lean_ctor_set(v___x_1389_, 2, v_v_1483_);
lean_ctor_set(v___x_1389_, 1, v_k_1482_);
lean_ctor_set(v___x_1389_, 0, v___x_1487_);
v___x_1491_ = v___x_1389_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_k_1482_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_v_1483_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_l_1480_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_object* v_r_1497_; 
v_r_1497_ = lean_ctor_get(v_impl_1393_, 4);
lean_inc(v_r_1497_);
if (lean_obj_tag(v_r_1497_) == 0)
{
lean_object* v_k_1498_; lean_object* v_v_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1522_; 
lean_inc(v_l_1480_);
v_k_1498_ = lean_ctor_get(v_impl_1393_, 1);
v_v_1499_ = lean_ctor_get(v_impl_1393_, 2);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_impl_1393_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; 
v_unused_1523_ = lean_ctor_get(v_impl_1393_, 4);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_impl_1393_, 3);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v_impl_1393_, 0);
lean_dec(v_unused_1525_);
v___x_1501_ = v_impl_1393_;
v_isShared_1502_ = v_isSharedCheck_1522_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_v_1499_);
lean_inc(v_k_1498_);
lean_dec(v_impl_1393_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1522_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_k_1503_; lean_object* v_v_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1518_; 
v_k_1503_ = lean_ctor_get(v_r_1497_, 1);
v_v_1504_ = lean_ctor_get(v_r_1497_, 2);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_r_1497_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; lean_object* v_unused_1520_; lean_object* v_unused_1521_; 
v_unused_1519_ = lean_ctor_get(v_r_1497_, 4);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_r_1497_, 3);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_r_1497_, 0);
lean_dec(v_unused_1521_);
v___x_1506_ = v_r_1497_;
v_isShared_1507_ = v_isSharedCheck_1518_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_v_1504_);
lean_inc(v_k_1503_);
lean_dec(v_r_1497_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1518_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1508_ = lean_unsigned_to_nat(3u);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 4, v_l_1480_);
lean_ctor_set(v___x_1506_, 3, v_l_1480_);
lean_ctor_set(v___x_1506_, 2, v_v_1499_);
lean_ctor_set(v___x_1506_, 1, v_k_1498_);
lean_ctor_set(v___x_1506_, 0, v___x_1394_);
v___x_1510_ = v___x_1506_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1498_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1499_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_l_1480_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_l_1480_);
v___x_1510_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 4, v_l_1480_);
lean_ctor_set(v___x_1501_, 2, v_v_1385_);
lean_ctor_set(v___x_1501_, 1, v_k_1384_);
lean_ctor_set(v___x_1501_, 0, v___x_1394_);
v___x_1512_ = v___x_1501_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_l_1480_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v_l_1480_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v___x_1512_);
lean_ctor_set(v___x_1389_, 3, v___x_1510_);
lean_ctor_set(v___x_1389_, 2, v_v_1504_);
lean_ctor_set(v___x_1389_, 1, v_k_1503_);
lean_ctor_set(v___x_1389_, 0, v___x_1508_);
v___x_1514_ = v___x_1389_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_k_1503_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_v_1504_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1526_ = lean_unsigned_to_nat(2u);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_r_1497_);
lean_ctor_set(v___x_1389_, 3, v_impl_1393_);
lean_ctor_set(v___x_1389_, 0, v___x_1526_);
v___x_1528_ = v___x_1389_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_impl_1393_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_r_1497_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1531_; 
lean_dec(v_v_1385_);
lean_dec(v_k_1384_);
lean_dec_ref(v_cmp_1379_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 2, v_v_1381_);
lean_ctor_set(v___x_1389_, 1, v_k_1380_);
v___x_1531_ = v___x_1389_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_size_1383_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_k_1380_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_v_1381_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_l_1386_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v_r_1387_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
default: 
{
lean_object* v_impl_1533_; lean_object* v___x_1534_; 
lean_dec(v_size_1383_);
v_impl_1533_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1379_, v_k_1380_, v_v_1381_, v_r_1387_);
v___x_1534_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1386_) == 0)
{
lean_object* v_size_1535_; lean_object* v_size_1536_; lean_object* v_k_1537_; lean_object* v_v_1538_; lean_object* v_l_1539_; lean_object* v_r_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_size_1535_ = lean_ctor_get(v_l_1386_, 0);
v_size_1536_ = lean_ctor_get(v_impl_1533_, 0);
v_k_1537_ = lean_ctor_get(v_impl_1533_, 1);
v_v_1538_ = lean_ctor_get(v_impl_1533_, 2);
v_l_1539_ = lean_ctor_get(v_impl_1533_, 3);
lean_inc(v_l_1539_);
v_r_1540_ = lean_ctor_get(v_impl_1533_, 4);
v___x_1541_ = lean_unsigned_to_nat(3u);
v___x_1542_ = lean_nat_mul(v___x_1541_, v_size_1535_);
v___x_1543_ = lean_nat_dec_lt(v___x_1542_, v_size_1536_);
lean_dec(v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
lean_dec(v_l_1539_);
v___x_1544_ = lean_nat_add(v___x_1534_, v_size_1535_);
v___x_1545_ = lean_nat_add(v___x_1544_, v_size_1536_);
lean_dec(v___x_1544_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_impl_1533_);
lean_ctor_set(v___x_1389_, 0, v___x_1545_);
v___x_1547_ = v___x_1389_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_l_1386_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_impl_1533_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
else
{
lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1612_; 
lean_inc(v_r_1540_);
lean_inc(v_v_1538_);
lean_inc(v_k_1537_);
lean_inc(v_size_1536_);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_impl_1533_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; lean_object* v_unused_1616_; lean_object* v_unused_1617_; 
v_unused_1613_ = lean_ctor_get(v_impl_1533_, 4);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_impl_1533_, 3);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_impl_1533_, 2);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_impl_1533_, 1);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_impl_1533_, 0);
lean_dec(v_unused_1617_);
v___x_1550_ = v_impl_1533_;
v_isShared_1551_ = v_isSharedCheck_1612_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v_impl_1533_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1612_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_size_1552_; lean_object* v_k_1553_; lean_object* v_v_1554_; lean_object* v_l_1555_; lean_object* v_r_1556_; lean_object* v_size_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_size_1552_ = lean_ctor_get(v_l_1539_, 0);
v_k_1553_ = lean_ctor_get(v_l_1539_, 1);
v_v_1554_ = lean_ctor_get(v_l_1539_, 2);
v_l_1555_ = lean_ctor_get(v_l_1539_, 3);
v_r_1556_ = lean_ctor_get(v_l_1539_, 4);
v_size_1557_ = lean_ctor_get(v_r_1540_, 0);
v___x_1558_ = lean_unsigned_to_nat(2u);
v___x_1559_ = lean_nat_mul(v___x_1558_, v_size_1557_);
v___x_1560_ = lean_nat_dec_lt(v_size_1552_, v___x_1559_);
lean_dec(v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1588_; 
lean_inc(v_r_1556_);
lean_inc(v_l_1555_);
lean_inc(v_v_1554_);
lean_inc(v_k_1553_);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_l_1539_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; 
v_unused_1589_ = lean_ctor_get(v_l_1539_, 4);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_l_1539_, 3);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_l_1539_, 2);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_l_1539_, 1);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_l_1539_, 0);
lean_dec(v_unused_1593_);
v___x_1562_ = v_l_1539_;
v_isShared_1563_ = v_isSharedCheck_1588_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v_l_1539_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1588_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1578_; 
v___x_1564_ = lean_nat_add(v___x_1534_, v_size_1535_);
v___x_1565_ = lean_nat_add(v___x_1564_, v_size_1536_);
lean_dec(v_size_1536_);
if (lean_obj_tag(v_l_1555_) == 0)
{
lean_object* v_size_1586_; 
v_size_1586_ = lean_ctor_get(v_l_1555_, 0);
lean_inc(v_size_1586_);
v___y_1578_ = v_size_1586_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_unsigned_to_nat(0u);
v___y_1578_ = v___x_1587_;
goto v___jp_1577_;
}
v___jp_1566_:
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1570_ = lean_nat_add(v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec(v___y_1568_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v_r_1540_);
lean_ctor_set(v___x_1562_, 3, v_r_1556_);
lean_ctor_set(v___x_1562_, 2, v_v_1538_);
lean_ctor_set(v___x_1562_, 1, v_k_1537_);
lean_ctor_set(v___x_1562_, 0, v___x_1570_);
v___x_1572_ = v___x_1562_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_k_1537_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v_v_1538_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v_r_1556_);
lean_ctor_set(v_reuseFailAlloc_1576_, 4, v_r_1540_);
v___x_1572_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1574_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v___x_1572_);
lean_ctor_set(v___x_1550_, 3, v___y_1567_);
lean_ctor_set(v___x_1550_, 2, v_v_1554_);
lean_ctor_set(v___x_1550_, 1, v_k_1553_);
lean_ctor_set(v___x_1550_, 0, v___x_1565_);
v___x_1574_ = v___x_1550_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_k_1553_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_v_1554_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v___y_1567_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
v___jp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_nat_add(v___x_1564_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec(v___x_1564_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_l_1555_);
lean_ctor_set(v___x_1389_, 0, v___x_1579_);
v___x_1581_ = v___x_1389_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_l_1386_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_l_1555_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_nat_add(v___x_1534_, v_size_1557_);
if (lean_obj_tag(v_r_1556_) == 0)
{
lean_object* v_size_1583_; 
v_size_1583_ = lean_ctor_get(v_r_1556_, 0);
lean_inc(v_size_1583_);
v___y_1567_ = v___x_1581_;
v___y_1568_ = v___x_1582_;
v___y_1569_ = v_size_1583_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_unsigned_to_nat(0u);
v___y_1567_ = v___x_1581_;
v___y_1568_ = v___x_1582_;
v___y_1569_ = v___x_1584_;
goto v___jp_1566_;
}
}
}
}
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_del_object(v___x_1389_);
v___x_1594_ = lean_nat_add(v___x_1534_, v_size_1535_);
v___x_1595_ = lean_nat_add(v___x_1594_, v_size_1536_);
lean_dec(v_size_1536_);
v___x_1596_ = lean_nat_add(v___x_1594_, v_size_1552_);
lean_dec(v___x_1594_);
lean_inc_ref(v_l_1386_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v_l_1539_);
lean_ctor_set(v___x_1550_, 3, v_l_1386_);
lean_ctor_set(v___x_1550_, 2, v_v_1385_);
lean_ctor_set(v___x_1550_, 1, v_k_1384_);
lean_ctor_set(v___x_1550_, 0, v___x_1596_);
v___x_1598_ = v___x_1550_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_l_1386_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_l_1539_);
v___x_1598_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_isSharedCheck_1605_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; lean_object* v_unused_1610_; 
v_unused_1606_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_l_1386_, 2);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_l_1386_, 1);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_l_1386_, 0);
lean_dec(v_unused_1610_);
v___x_1600_ = v_l_1386_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_dec(v_l_1386_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 4, v_r_1540_);
lean_ctor_set(v___x_1600_, 3, v___x_1598_);
lean_ctor_set(v___x_1600_, 2, v_v_1538_);
lean_ctor_set(v___x_1600_, 1, v_k_1537_);
lean_ctor_set(v___x_1600_, 0, v___x_1595_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1537_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1538_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v_r_1540_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1618_; 
v_l_1618_ = lean_ctor_get(v_impl_1533_, 3);
lean_inc(v_l_1618_);
if (lean_obj_tag(v_l_1618_) == 0)
{
lean_object* v_r_1619_; lean_object* v_k_1620_; lean_object* v_v_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1644_; 
v_r_1619_ = lean_ctor_get(v_impl_1533_, 4);
v_k_1620_ = lean_ctor_get(v_impl_1533_, 1);
v_v_1621_ = lean_ctor_get(v_impl_1533_, 2);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_impl_1533_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; lean_object* v_unused_1646_; 
v_unused_1645_ = lean_ctor_get(v_impl_1533_, 3);
lean_dec(v_unused_1645_);
v_unused_1646_ = lean_ctor_get(v_impl_1533_, 0);
lean_dec(v_unused_1646_);
v___x_1623_ = v_impl_1533_;
v_isShared_1624_ = v_isSharedCheck_1644_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_r_1619_);
lean_inc(v_v_1621_);
lean_inc(v_k_1620_);
lean_dec(v_impl_1533_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1644_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v_k_1625_; lean_object* v_v_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1640_; 
v_k_1625_ = lean_ctor_get(v_l_1618_, 1);
v_v_1626_ = lean_ctor_get(v_l_1618_, 2);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_l_1618_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; lean_object* v_unused_1643_; 
v_unused_1641_ = lean_ctor_get(v_l_1618_, 4);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_l_1618_, 3);
lean_dec(v_unused_1642_);
v_unused_1643_ = lean_ctor_get(v_l_1618_, 0);
lean_dec(v_unused_1643_);
v___x_1628_ = v_l_1618_;
v_isShared_1629_ = v_isSharedCheck_1640_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_v_1626_);
lean_inc(v_k_1625_);
lean_dec(v_l_1618_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1640_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1630_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1619_, 2);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 4, v_r_1619_);
lean_ctor_set(v___x_1628_, 3, v_r_1619_);
lean_ctor_set(v___x_1628_, 2, v_v_1385_);
lean_ctor_set(v___x_1628_, 1, v_k_1384_);
lean_ctor_set(v___x_1628_, 0, v___x_1534_);
v___x_1632_ = v___x_1628_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_r_1619_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v_r_1619_);
v___x_1632_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1634_; 
lean_inc(v_r_1619_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 3, v_r_1619_);
lean_ctor_set(v___x_1623_, 0, v___x_1534_);
v___x_1634_ = v___x_1623_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_k_1620_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_v_1621_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v_r_1619_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v_r_1619_);
v___x_1634_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v___x_1634_);
lean_ctor_set(v___x_1389_, 3, v___x_1632_);
lean_ctor_set(v___x_1389_, 2, v_v_1626_);
lean_ctor_set(v___x_1389_, 1, v_k_1625_);
lean_ctor_set(v___x_1389_, 0, v___x_1630_);
v___x_1636_ = v___x_1389_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_k_1625_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_v_1626_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
}
else
{
lean_object* v_r_1647_; 
v_r_1647_ = lean_ctor_get(v_impl_1533_, 4);
lean_inc(v_r_1647_);
if (lean_obj_tag(v_r_1647_) == 0)
{
lean_object* v_k_1648_; lean_object* v_v_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1660_; 
v_k_1648_ = lean_ctor_get(v_impl_1533_, 1);
v_v_1649_ = lean_ctor_get(v_impl_1533_, 2);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_impl_1533_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; 
v_unused_1661_ = lean_ctor_get(v_impl_1533_, 4);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_impl_1533_, 3);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_impl_1533_, 0);
lean_dec(v_unused_1663_);
v___x_1651_ = v_impl_1533_;
v_isShared_1652_ = v_isSharedCheck_1660_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_v_1649_);
lean_inc(v_k_1648_);
lean_dec(v_impl_1533_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1660_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1653_ = lean_unsigned_to_nat(3u);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 4, v_l_1618_);
lean_ctor_set(v___x_1651_, 2, v_v_1385_);
lean_ctor_set(v___x_1651_, 1, v_k_1384_);
lean_ctor_set(v___x_1651_, 0, v___x_1534_);
v___x_1655_ = v___x_1651_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1659_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1659_, 3, v_l_1618_);
lean_ctor_set(v_reuseFailAlloc_1659_, 4, v_l_1618_);
v___x_1655_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1657_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_r_1647_);
lean_ctor_set(v___x_1389_, 3, v___x_1655_);
lean_ctor_set(v___x_1389_, 2, v_v_1649_);
lean_ctor_set(v___x_1389_, 1, v_k_1648_);
lean_ctor_set(v___x_1389_, 0, v___x_1653_);
v___x_1657_ = v___x_1389_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_k_1648_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_v_1649_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1658_, 4, v_r_1647_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = lean_unsigned_to_nat(2u);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v_impl_1533_);
lean_ctor_set(v___x_1389_, 3, v_r_1647_);
lean_ctor_set(v___x_1389_, 0, v___x_1664_);
v___x_1666_ = v___x_1389_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_r_1647_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_impl_1533_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec_ref(v_cmp_1379_);
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v_k_1380_);
lean_ctor_set(v___x_1670_, 2, v_v_1381_);
lean_ctor_set(v___x_1670_, 3, v_t_1382_);
lean_ctor_set(v___x_1670_, 4, v_t_1382_);
return v___x_1670_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(lean_object* v_cmp_1671_, lean_object* v_k_1672_, lean_object* v_t_1673_){
_start:
{
if (lean_obj_tag(v_t_1673_) == 0)
{
lean_object* v_k_1674_; lean_object* v_l_1675_; lean_object* v_r_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v_k_1674_ = lean_ctor_get(v_t_1673_, 1);
lean_inc(v_k_1674_);
v_l_1675_ = lean_ctor_get(v_t_1673_, 3);
lean_inc(v_l_1675_);
v_r_1676_ = lean_ctor_get(v_t_1673_, 4);
lean_inc(v_r_1676_);
lean_dec_ref_known(v_t_1673_, 5);
lean_inc_ref(v_cmp_1671_);
lean_inc(v_k_1672_);
v___x_1677_ = lean_apply_2(v_cmp_1671_, v_k_1672_, v_k_1674_);
v___x_1678_ = lean_unbox(v___x_1677_);
switch(v___x_1678_)
{
case 0:
{
lean_dec(v_r_1676_);
v_t_1673_ = v_l_1675_;
goto _start;
}
case 1:
{
uint8_t v___x_1680_; 
lean_dec(v_r_1676_);
lean_dec(v_l_1675_);
lean_dec(v_k_1672_);
lean_dec_ref(v_cmp_1671_);
v___x_1680_ = 1;
return v___x_1680_;
}
default: 
{
lean_dec(v_l_1675_);
v_t_1673_ = v_r_1676_;
goto _start;
}
}
}
else
{
uint8_t v___x_1682_; 
lean_dec(v_k_1672_);
lean_dec_ref(v_cmp_1671_);
v___x_1682_ = 0;
return v___x_1682_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg___boxed(lean_object* v_cmp_1683_, lean_object* v_k_1684_, lean_object* v_t_1685_){
_start:
{
uint8_t v_res_1686_; lean_object* v_r_1687_; 
v_res_1686_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1683_, v_k_1684_, v_t_1685_);
v_r_1687_ = lean_box(v_res_1686_);
return v_r_1687_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(lean_object* v_cmp_1688_, lean_object* v_as_x27_1689_, lean_object* v_b_1690_){
_start:
{
if (lean_obj_tag(v_as_x27_1689_) == 0)
{
lean_dec_ref(v_cmp_1688_);
return v_b_1690_;
}
else
{
lean_object* v_head_1691_; lean_object* v_tail_1692_; uint8_t v___x_1693_; 
v_head_1691_ = lean_ctor_get(v_as_x27_1689_, 0);
v_tail_1692_ = lean_ctor_get(v_as_x27_1689_, 1);
lean_inc(v_b_1690_);
lean_inc(v_head_1691_);
lean_inc_ref(v_cmp_1688_);
v___x_1693_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1688_, v_head_1691_, v_b_1690_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_box(0);
lean_inc(v_head_1691_);
lean_inc_ref(v_cmp_1688_);
v___x_1695_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1688_, v_head_1691_, v___x_1694_, v_b_1690_);
v_as_x27_1689_ = v_tail_1692_;
v_b_1690_ = v___x_1695_;
goto _start;
}
else
{
v_as_x27_1689_ = v_tail_1692_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg___boxed(lean_object* v_cmp_1698_, lean_object* v_as_x27_1699_, lean_object* v_b_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1698_, v_as_x27_1699_, v_b_1700_);
lean_dec(v_as_x27_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___redArg(lean_object* v_l_1702_, lean_object* v_cmp_1703_){
_start:
{
lean_object* v_r_1704_; lean_object* v___x_1705_; 
v_r_1704_ = lean_box(1);
v___x_1705_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1703_, v_l_1702_, v_r_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___redArg___boxed(lean_object* v_l_1706_, lean_object* v_cmp_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Std_ExtTreeSet_ofList___redArg(v_l_1706_, v_cmp_1707_);
lean_dec(v_l_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList(lean_object* v_00_u03b1_1709_, lean_object* v_l_1710_, lean_object* v_cmp_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Std_ExtTreeSet_ofList___redArg(v_l_1710_, v_cmp_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_l_1714_, lean_object* v_cmp_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Std_ExtTreeSet_ofList(v_00_u03b1_1713_, v_l_1714_, v_cmp_1715_);
lean_dec(v_l_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(lean_object* v_00_u03b1_1717_, lean_object* v_cmp_1718_, lean_object* v_00_u03b2_1719_, lean_object* v_k_1720_, lean_object* v_t_1721_){
_start:
{
uint8_t v___x_1722_; 
v___x_1722_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1718_, v_k_1720_, v_t_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___boxed(lean_object* v_00_u03b1_1723_, lean_object* v_cmp_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_k_1726_, lean_object* v_t_1727_){
_start:
{
uint8_t v_res_1728_; lean_object* v_r_1729_; 
v_res_1728_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(v_00_u03b1_1723_, v_cmp_1724_, v_00_u03b2_1725_, v_k_1726_, v_t_1727_);
v_r_1729_ = lean_box(v_res_1728_);
return v_r_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1(lean_object* v_00_u03b1_1730_, lean_object* v_cmp_1731_, lean_object* v_00_u03b2_1732_, lean_object* v_k_1733_, lean_object* v_v_1734_, lean_object* v_t_1735_, lean_object* v_hl_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1731_, v_k_1733_, v_v_1734_, v_t_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(lean_object* v_00_u03b1_1738_, lean_object* v_cmp_1739_, lean_object* v_as_1740_, lean_object* v_as_x27_1741_, lean_object* v_b_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1739_, v_as_x27_1741_, v_b_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_cmp_1746_, lean_object* v_as_1747_, lean_object* v_as_x27_1748_, lean_object* v_b_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(v_00_u03b1_1745_, v_cmp_1746_, v_as_1747_, v_as_x27_1748_, v_b_1749_, v_a_1750_);
lean_dec(v_as_x27_1748_);
lean_dec(v_as_1747_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg___lam__0(lean_object* v_l_1752_, lean_object* v_k_1753_, lean_object* v_x_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_array_push(v_l_1752_, v_k_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg(lean_object* v_t_1757_){
_start:
{
lean_object* v___f_1758_; lean_object* v___y_1760_; 
v___f_1758_ = ((lean_object*)(l_Std_ExtTreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1757_) == 0)
{
lean_object* v_size_1763_; 
v_size_1763_ = lean_ctor_get(v_t_1757_, 0);
lean_inc(v_size_1763_);
v___y_1760_ = v_size_1763_;
goto v___jp_1759_;
}
else
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_unsigned_to_nat(0u);
v___y_1760_ = v___x_1764_;
goto v___jp_1759_;
}
v___jp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_mk_empty_array_with_capacity(v___y_1760_);
lean_dec(v___y_1760_);
v___x_1762_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1758_, v___x_1761_, v_t_1757_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray(lean_object* v_00_u03b1_1765_, lean_object* v_cmp_1766_, lean_object* v_inst_1767_, lean_object* v_t_1768_){
_start:
{
lean_object* v___f_1769_; lean_object* v___y_1771_; 
v___f_1769_ = ((lean_object*)(l_Std_ExtTreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1768_) == 0)
{
lean_object* v_size_1774_; 
v_size_1774_ = lean_ctor_get(v_t_1768_, 0);
lean_inc(v_size_1774_);
v___y_1771_ = v_size_1774_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_unsigned_to_nat(0u);
v___y_1771_ = v___x_1775_;
goto v___jp_1770_;
}
v___jp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_mk_empty_array_with_capacity(v___y_1771_);
lean_dec(v___y_1771_);
v___x_1773_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1769_, v___x_1772_, v_t_1768_);
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___boxed(lean_object* v_00_u03b1_1776_, lean_object* v_cmp_1777_, lean_object* v_inst_1778_, lean_object* v_t_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Std_ExtTreeSet_toArray(v_00_u03b1_1776_, v_cmp_1777_, v_inst_1778_, v_t_1779_);
lean_dec_ref(v_cmp_1777_);
return v_res_1780_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__25, &l_Std_ExtTreeSet___auto__1___closed__25_once, _init_l_Std_ExtTreeSet___auto__1___closed__25);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(lean_object* v_cmp_1782_, lean_object* v_as_1783_, size_t v_sz_1784_, size_t v_i_1785_, lean_object* v_b_1786_){
_start:
{
lean_object* v___y_1788_; uint8_t v___x_1792_; 
v___x_1792_ = lean_usize_dec_lt(v_i_1785_, v_sz_1784_);
if (v___x_1792_ == 0)
{
lean_dec_ref(v_cmp_1782_);
return v_b_1786_;
}
else
{
lean_object* v_a_1793_; uint8_t v___x_1794_; 
v_a_1793_ = lean_array_uget_borrowed(v_as_1783_, v_i_1785_);
lean_inc(v_b_1786_);
lean_inc(v_a_1793_);
lean_inc_ref(v_cmp_1782_);
v___x_1794_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1782_, v_a_1793_, v_b_1786_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_box(0);
lean_inc(v_a_1793_);
lean_inc_ref(v_cmp_1782_);
v___x_1796_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1782_, v_a_1793_, v___x_1795_, v_b_1786_);
v___y_1788_ = v___x_1796_;
goto v___jp_1787_;
}
else
{
v___y_1788_ = v_b_1786_;
goto v___jp_1787_;
}
}
v___jp_1787_:
{
size_t v___x_1789_; size_t v___x_1790_; 
v___x_1789_ = ((size_t)1ULL);
v___x_1790_ = lean_usize_add(v_i_1785_, v___x_1789_);
v_i_1785_ = v___x_1790_;
v_b_1786_ = v___y_1788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg___boxed(lean_object* v_cmp_1797_, lean_object* v_as_1798_, lean_object* v_sz_1799_, lean_object* v_i_1800_, lean_object* v_b_1801_){
_start:
{
size_t v_sz_boxed_1802_; size_t v_i_boxed_1803_; lean_object* v_res_1804_; 
v_sz_boxed_1802_ = lean_unbox_usize(v_sz_1799_);
lean_dec(v_sz_1799_);
v_i_boxed_1803_ = lean_unbox_usize(v_i_1800_);
lean_dec(v_i_1800_);
v_res_1804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1797_, v_as_1798_, v_sz_boxed_1802_, v_i_boxed_1803_, v_b_1801_);
lean_dec_ref(v_as_1798_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg(lean_object* v_a_1805_, lean_object* v_cmp_1806_){
_start:
{
lean_object* v_r_1807_; size_t v_sz_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v_r_1807_ = lean_box(1);
v_sz_1808_ = lean_array_size(v_a_1805_);
v___x_1809_ = ((size_t)0ULL);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1806_, v_a_1805_, v_sz_1808_, v___x_1809_, v_r_1807_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg___boxed(lean_object* v_a_1811_, lean_object* v_cmp_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_1811_, v_cmp_1812_);
lean_dec_ref(v_a_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray(lean_object* v_00_u03b1_1814_, lean_object* v_a_1815_, lean_object* v_cmp_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_1815_, v_cmp_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___boxed(lean_object* v_00_u03b1_1818_, lean_object* v_a_1819_, lean_object* v_cmp_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Std_ExtTreeSet_ofArray(v_00_u03b1_1818_, v_a_1819_, v_cmp_1820_);
lean_dec_ref(v_a_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(lean_object* v_00_u03b1_1822_, lean_object* v_cmp_1823_, lean_object* v_as_1824_, size_t v_sz_1825_, size_t v_i_1826_, lean_object* v_b_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1823_, v_as_1824_, v_sz_1825_, v_i_1826_, v_b_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___boxed(lean_object* v_00_u03b1_1829_, lean_object* v_cmp_1830_, lean_object* v_as_1831_, lean_object* v_sz_1832_, lean_object* v_i_1833_, lean_object* v_b_1834_){
_start:
{
size_t v_sz_boxed_1835_; size_t v_i_boxed_1836_; lean_object* v_res_1837_; 
v_sz_boxed_1835_ = lean_unbox_usize(v_sz_1832_);
lean_dec(v_sz_1832_);
v_i_boxed_1836_ = lean_unbox_usize(v_i_1833_);
lean_dec(v_i_1833_);
v_res_1837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(v_00_u03b1_1829_, v_cmp_1830_, v_as_1831_, v_sz_boxed_1835_, v_i_boxed_1836_, v_b_1834_);
lean_dec_ref(v_as_1831_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0(lean_object* v_b_u2082_1840_, lean_object* v_x_1841_){
_start:
{
if (lean_obj_tag(v_x_1841_) == 0)
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_b_u2082_1840_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; 
v___x_1843_ = ((lean_object*)(l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0));
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1844_, lean_object* v_x_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Std_ExtTreeSet_merge___redArg___lam__0(v_b_u2082_1844_, v_x_1845_);
lean_dec(v_x_1845_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__1(lean_object* v_cmp_1847_, lean_object* v_t_1848_, lean_object* v_a_1849_, lean_object* v_b_u2082_1850_){
_start:
{
lean_object* v___f_1851_; lean_object* v___x_1852_; 
v___f_1851_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1851_, 0, v_b_u2082_1850_);
v___x_1852_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_1847_, v_a_1849_, v___f_1851_, v_t_1848_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg(lean_object* v_cmp_1853_, lean_object* v_t_u2081_1854_, lean_object* v_t_u2082_1855_){
_start:
{
lean_object* v___f_1856_; lean_object* v___x_1857_; 
v___f_1856_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1856_, 0, v_cmp_1853_);
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1856_, v_t_u2081_1854_, v_t_u2082_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge(lean_object* v_00_u03b1_1858_, lean_object* v_cmp_1859_, lean_object* v_inst_1860_, lean_object* v_t_u2081_1861_, lean_object* v_t_u2082_1862_){
_start:
{
lean_object* v___f_1863_; lean_object* v___x_1864_; 
v___f_1863_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1863_, 0, v_cmp_1859_);
v___x_1864_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1863_, v_t_u2081_1861_, v_t_u2082_1862_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg___lam__0(lean_object* v_cmp_1865_, lean_object* v_a_1866_, lean_object* v_____s_1867_){
_start:
{
uint8_t v___x_1868_; 
lean_inc(v_____s_1867_);
lean_inc(v_a_1866_);
lean_inc_ref(v_cmp_1865_);
v___x_1868_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1865_, v_a_1866_, v_____s_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_box(0);
v___x_1870_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1865_, v_a_1866_, v___x_1869_, v_____s_1867_);
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
else
{
lean_object* v___x_1872_; 
lean_dec(v_a_1866_);
lean_dec_ref(v_cmp_1865_);
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_____s_1867_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg(lean_object* v_cmp_1873_, lean_object* v_inst_1874_, lean_object* v_t_1875_, lean_object* v_l_1876_){
_start:
{
lean_object* v___f_1877_; lean_object* v___x_1878_; 
v___f_1877_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1877_, 0, v_cmp_1873_);
v___x_1878_ = lean_apply_4(v_inst_1874_, lean_box(0), v_l_1876_, v_t_1875_, v___f_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany(lean_object* v_00_u03b1_1879_, lean_object* v_cmp_1880_, lean_object* v_inst_1881_, lean_object* v_00_u03c1_1882_, lean_object* v_inst_1883_, lean_object* v_t_1884_, lean_object* v_l_1885_){
_start:
{
lean_object* v___f_1886_; lean_object* v___x_1887_; 
v___f_1886_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1886_, 0, v_cmp_1880_);
v___x_1887_ = lean_apply_4(v_inst_1883_, lean_box(0), v_l_1885_, v_t_1884_, v___f_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union___redArg(lean_object* v_cmp_1888_, lean_object* v_t_u2081_1889_, lean_object* v_t_u2082_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1888_, v_t_u2081_1889_, v_t_u2082_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union(lean_object* v_00_u03b1_1892_, lean_object* v_cmp_1893_, lean_object* v_inst_1894_, lean_object* v_t_u2081_1895_, lean_object* v_t_u2082_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1893_, v_t_u2081_1895_, v_t_u2082_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp___redArg(lean_object* v_cmp_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_union), 5, 3);
lean_closure_set(v___x_1899_, 0, lean_box(0));
lean_closure_set(v___x_1899_, 1, v_cmp_1898_);
lean_closure_set(v___x_1899_, 2, lean_box(0));
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp(lean_object* v_00_u03b1_1900_, lean_object* v_cmp_1901_, lean_object* v_inst_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_union), 5, 3);
lean_closure_set(v___x_1903_, 0, lean_box(0));
lean_closure_set(v___x_1903_, 1, v_cmp_1901_);
lean_closure_set(v___x_1903_, 2, lean_box(0));
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter___redArg(lean_object* v_cmp_1904_, lean_object* v_t_u2081_1905_, lean_object* v_t_u2082_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1904_, v_t_u2081_1905_, v_t_u2082_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter(lean_object* v_00_u03b1_1908_, lean_object* v_cmp_1909_, lean_object* v_inst_1910_, lean_object* v_t_u2081_1911_, lean_object* v_t_u2082_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1909_, v_t_u2081_1911_, v_t_u2082_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp___redArg(lean_object* v_cmp_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_inter), 5, 3);
lean_closure_set(v___x_1915_, 0, lean_box(0));
lean_closure_set(v___x_1915_, 1, v_cmp_1914_);
lean_closure_set(v___x_1915_, 2, lean_box(0));
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp(lean_object* v_00_u03b1_1916_, lean_object* v_cmp_1917_, lean_object* v_inst_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_inter), 5, 3);
lean_closure_set(v___x_1919_, 0, lean_box(0));
lean_closure_set(v___x_1919_, 1, v_cmp_1917_);
lean_closure_set(v___x_1919_, 2, lean_box(0));
return v___x_1919_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___f_1921_; 
v___x_1920_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1921_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1921_, 0, v___x_1920_);
return v___f_1921_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(lean_object* v_cmp_1922_, lean_object* v_m_u2081_1923_, lean_object* v_m_u2082_1924_){
_start:
{
lean_object* v___f_1925_; uint8_t v___x_1926_; 
v___f_1925_ = lean_obj_once(&l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0, &l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once, _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0);
v___x_1926_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_1922_, v___f_1925_, v_m_u2081_1923_, v_m_u2082_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_1927_, lean_object* v_m_u2081_1928_, lean_object* v_m_u2082_1929_){
_start:
{
uint8_t v_res_1930_; lean_object* v_r_1931_; 
v_res_1930_ = l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(v_cmp_1927_, v_m_u2081_1928_, v_m_u2082_1929_);
v_r_1931_ = lean_box(v_res_1930_);
return v_r_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg(lean_object* v_cmp_1932_){
_start:
{
lean_object* v___f_1933_; 
v___f_1933_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1933_, 0, v_cmp_1932_);
return v___f_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp(lean_object* v_00_u03b1_1934_, lean_object* v_cmp_1935_, lean_object* v_inst_1936_){
_start:
{
lean_object* v___f_1937_; 
v___f_1937_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1937_, 0, v_cmp_1935_);
return v___f_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff___redArg(lean_object* v_cmp_1938_, lean_object* v_t_u2081_1939_, lean_object* v_t_u2082_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1938_, v_t_u2081_1939_, v_t_u2082_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff(lean_object* v_00_u03b1_1942_, lean_object* v_cmp_1943_, lean_object* v_inst_1944_, lean_object* v_t_u2081_1945_, lean_object* v_t_u2082_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1943_, v_t_u2081_1945_, v_t_u2082_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp___redArg(lean_object* v_cmp_1948_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_diff), 5, 3);
lean_closure_set(v___x_1949_, 0, lean_box(0));
lean_closure_set(v___x_1949_, 1, v_cmp_1948_);
lean_closure_set(v___x_1949_, 2, lean_box(0));
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp(lean_object* v_00_u03b1_1950_, lean_object* v_cmp_1951_, lean_object* v_inst_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_diff), 5, 3);
lean_closure_set(v___x_1953_, 0, lean_box(0));
lean_closure_set(v___x_1953_, 1, v_cmp_1951_);
lean_closure_set(v___x_1953_, 2, lean_box(0));
return v___x_1953_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(lean_object* v_cmp_1954_, lean_object* v_x_1955_, lean_object* v_x_1956_){
_start:
{
lean_object* v___f_1957_; uint8_t v___x_1958_; 
v___f_1957_ = lean_obj_once(&l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0, &l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once, _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0);
v___x_1958_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_1954_, v___f_1957_, v_x_1955_, v_x_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg___boxed(lean_object* v_cmp_1959_, lean_object* v_x_1960_, lean_object* v_x_1961_){
_start:
{
uint8_t v_res_1962_; lean_object* v_r_1963_; 
v_res_1962_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_1959_, v_x_1960_, v_x_1961_);
v_r_1963_ = lean_box(v_res_1962_);
return v_r_1963_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(lean_object* v_00_u03b1_1964_, lean_object* v_cmp_1965_, lean_object* v_inst_1966_, lean_object* v_inst_1967_, lean_object* v_x_1968_, lean_object* v_x_1969_){
_start:
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_1965_, v_x_1968_, v_x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___boxed(lean_object* v_00_u03b1_1971_, lean_object* v_cmp_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_){
_start:
{
uint8_t v_res_1977_; lean_object* v_r_1978_; 
v_res_1977_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(v_00_u03b1_1971_, v_cmp_1972_, v_inst_1973_, v_inst_1974_, v_x_1975_, v_x_1976_);
v_r_1978_ = lean_box(v_res_1977_);
return v_r_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg___lam__0(lean_object* v_cmp_1979_, lean_object* v_a_1980_, lean_object* v_____s_1981_){
_start:
{
lean_object* v_acc_1982_; lean_object* v___x_1983_; 
v_acc_1982_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_1979_, v_a_1980_, v_____s_1981_);
v___x_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_acc_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg(lean_object* v_cmp_1984_, lean_object* v_inst_1985_, lean_object* v_t_1986_, lean_object* v_l_1987_){
_start:
{
lean_object* v___f_1988_; lean_object* v___x_1989_; 
v___f_1988_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1988_, 0, v_cmp_1984_);
v___x_1989_ = lean_apply_4(v_inst_1985_, lean_box(0), v_l_1987_, v_t_1986_, v___f_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany(lean_object* v_00_u03b1_1990_, lean_object* v_cmp_1991_, lean_object* v_inst_1992_, lean_object* v_00_u03c1_1993_, lean_object* v_inst_1994_, lean_object* v_t_1995_, lean_object* v_l_1996_){
_start:
{
lean_object* v___f_1997_; lean_object* v___x_1998_; 
v___f_1997_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1997_, 0, v_cmp_1991_);
v___x_1998_ = lean_apply_4(v_inst_1994_, lean_box(0), v_l_1996_, v_t_1995_, v___f_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_2002_, lean_object* v_inst_2003_, lean_object* v_m_2004_, lean_object* v_prec_2005_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2006_ = ((lean_object*)(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_2007_ = lean_box(0);
v___x_2008_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_2009_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2008_, v___f_2002_, v___x_2007_, v_m_2004_);
v___x_2010_ = l_List_repr___redArg(v_inst_2003_, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2006_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = l_Repr_addAppParen(v___x_2011_, v_prec_2005_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_2013_, lean_object* v_inst_2014_, lean_object* v_m_2015_, lean_object* v_prec_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(v___f_2013_, v_inst_2014_, v_m_2015_, v_prec_2016_);
lean_dec(v_prec_2016_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg(lean_object* v_inst_2018_){
_start:
{
lean_object* v___f_2019_; lean_object* v___f_2020_; 
v___f_2019_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___f_2020_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2020_, 0, v___f_2019_);
lean_closure_set(v___f_2020_, 1, v_inst_2018_);
return v___f_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp(lean_object* v_00_u03b1_2021_, lean_object* v_cmp_2022_, lean_object* v_inst_2023_, lean_object* v_inst_2024_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg(v_inst_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_2026_, lean_object* v_cmp_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Std_ExtTreeSet_instReprOfTransCmp(v_00_u03b1_2026_, v_cmp_2027_, v_inst_2028_, v_inst_2029_);
lean_dec_ref(v_cmp_2027_);
return v_res_2030_;
}
}
lean_object* runtime_initialize_Std_Data_ExtTreeMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtTreeSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_ExtTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_ExtTreeSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_ExtTreeSet___auto__1 = _init_l_Std_ExtTreeSet___auto__1();
lean_mark_persistent(l_Std_ExtTreeSet___auto__1);
l_Std_ExtTreeSet_ofList___auto__1 = _init_l_Std_ExtTreeSet_ofList___auto__1();
lean_mark_persistent(l_Std_ExtTreeSet_ofList___auto__1);
l_Std_ExtTreeSet_ofArray___auto__1 = _init_l_Std_ExtTreeSet_ofArray___auto__1();
lean_mark_persistent(l_Std_ExtTreeSet_ofArray___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_ExtTreeMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_ExtTreeSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_ExtTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_ExtTreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_ExtTreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_ExtTreeSet_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
