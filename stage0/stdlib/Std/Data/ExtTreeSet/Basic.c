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
lean_object* l_Std_ExtTreeSet_empty___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(1);
return v___x_74_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_75_;
v_res_75_ = l_Std_ExtTreeSet_empty___redArg();
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___redArg___boxed(lean_object* v___dummy_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_ExtTreeSet_empty___redArg();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty(lean_object* v_00_u03b1_78_, lean_object* v_cmp_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(1);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___boxed(lean_object* v_00_u03b1_81_, lean_object* v_cmp_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_ExtTreeSet_empty(v_00_u03b1_81_, v_cmp_82_);
lean_dec_ref(v_cmp_82_);
return v_res_83_;
}
}
lean_object* l_Std_ExtTreeSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_box(1);
return v___x_85_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_86_;
v_res_86_ = l_Std_ExtTreeSet_instEmptyCollection___redArg();
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_ExtTreeSet_instEmptyCollection___redArg();
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection(lean_object* v_00_u03b1_89_, lean_object* v_cmp_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(1);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_92_, lean_object* v_cmp_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_ExtTreeSet_instEmptyCollection(v_00_u03b1_92_, v_cmp_93_);
lean_dec_ref(v_cmp_93_);
return v_res_94_;
}
}
lean_object* l_Std_ExtTreeSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_97_;
v_res_97_ = l_Std_ExtTreeSet_instInhabited___redArg();
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___redArg___boxed(lean_object* v___dummy_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_ExtTreeSet_instInhabited___redArg();
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited(lean_object* v_00_u03b1_100_, lean_object* v_cmp_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(1);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___boxed(lean_object* v_00_u03b1_103_, lean_object* v_cmp_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_ExtTreeSet_instInhabited(v_00_u03b1_103_, v_cmp_104_);
lean_dec_ref(v_cmp_104_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insert___redArg(lean_object* v_cmp_106_, lean_object* v_l_107_, lean_object* v_a_108_){
_start:
{
uint8_t v___x_109_; 
lean_inc(v_l_107_);
lean_inc(v_a_108_);
lean_inc_ref(v_cmp_106_);
v___x_109_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_106_, v_a_108_, v_l_107_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_box(0);
v___x_111_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_106_, v_a_108_, v___x_110_, v_l_107_);
return v___x_111_;
}
else
{
lean_dec(v_a_108_);
lean_dec_ref(v_cmp_106_);
return v_l_107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insert(lean_object* v_00_u03b1_112_, lean_object* v_cmp_113_, lean_object* v_inst_114_, lean_object* v_l_115_, lean_object* v_a_116_){
_start:
{
uint8_t v___x_117_; 
lean_inc(v_l_115_);
lean_inc(v_a_116_);
lean_inc_ref(v_cmp_113_);
v___x_117_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_113_, v_a_116_, v_l_115_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_box(0);
v___x_119_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_113_, v_a_116_, v___x_118_, v_l_115_);
return v___x_119_;
}
else
{
lean_dec(v_a_116_);
lean_dec_ref(v_cmp_113_);
return v_l_115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0(lean_object* v_cmp_120_, lean_object* v_e_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_box(1);
lean_inc(v_e_121_);
lean_inc_ref(v_cmp_120_);
v___x_123_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_120_, v_e_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_box(0);
v___x_125_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_120_, v_e_121_, v___x_124_, v___x_122_);
return v___x_125_;
}
else
{
lean_dec(v_e_121_);
lean_dec_ref(v_cmp_120_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg(lean_object* v_cmp_126_){
_start:
{
lean_object* v___f_127_; 
v___f_127_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_127_, 0, v_cmp_126_);
return v___f_127_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp(lean_object* v_00_u03b1_128_, lean_object* v_cmp_129_, lean_object* v_inst_130_){
_start:
{
lean_object* v___f_131_; 
v___f_131_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_131_, 0, v_cmp_129_);
return v___f_131_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0(lean_object* v_cmp_132_, lean_object* v_e_133_, lean_object* v_s_134_){
_start:
{
uint8_t v___x_135_; 
lean_inc(v_s_134_);
lean_inc(v_e_133_);
lean_inc_ref(v_cmp_132_);
v___x_135_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_132_, v_e_133_, v_s_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_box(0);
v___x_137_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_132_, v_e_133_, v___x_136_, v_s_134_);
return v___x_137_;
}
else
{
lean_dec(v_e_133_);
lean_dec_ref(v_cmp_132_);
return v_s_134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp___redArg(lean_object* v_cmp_138_){
_start:
{
lean_object* v___f_139_; 
v___f_139_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_139_, 0, v_cmp_138_);
return v___f_139_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp(lean_object* v_00_u03b1_140_, lean_object* v_cmp_141_, lean_object* v_inst_142_){
_start:
{
lean_object* v___f_143_; 
v___f_143_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_143_, 0, v_cmp_141_);
return v___f_143_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_containsThenInsert___redArg(lean_object* v_cmp_144_, lean_object* v_t_145_, lean_object* v_a_146_){
_start:
{
uint8_t v___x_147_; 
lean_inc(v_t_145_);
lean_inc(v_a_146_);
lean_inc_ref(v_cmp_144_);
v___x_147_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_144_, v_a_146_, v_t_145_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_148_ = lean_box(0);
v___x_149_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_144_, v_a_146_, v___x_148_, v_t_145_);
v___x_150_ = lean_box(v___x_147_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_a_146_);
lean_dec_ref(v_cmp_144_);
v___x_152_ = lean_box(v___x_147_);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v_t_145_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_containsThenInsert(lean_object* v_00_u03b1_154_, lean_object* v_cmp_155_, lean_object* v_inst_156_, lean_object* v_t_157_, lean_object* v_a_158_){
_start:
{
uint8_t v___x_159_; 
lean_inc(v_t_157_);
lean_inc(v_a_158_);
lean_inc_ref(v_cmp_155_);
v___x_159_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_155_, v_a_158_, v_t_157_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = lean_box(0);
v___x_161_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_155_, v_a_158_, v___x_160_, v_t_157_);
v___x_162_ = lean_box(v___x_159_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_a_158_);
lean_dec_ref(v_cmp_155_);
v___x_164_ = lean_box(v___x_159_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_t_157_);
return v___x_165_;
}
}
}
uint8_t l_Std_ExtTreeSet_contains___redArg(lean_object* v_cmp_166_, lean_object* v_l_167_, lean_object* v_a_168_){
_start:
{
uint8_t v___x_169_; 
v___x_169_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_166_, v_a_168_, v_l_167_);
return v___x_169_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_166_ = stack[0].m_obj;
lean_object* v_l_167_ = stack[1].m_obj;
lean_object* v_a_168_ = stack[2].m_obj;
uint8_t v_res_170_;
v_res_170_ = l_Std_ExtTreeSet_contains___redArg(v_cmp_166_, v_l_167_, v_a_168_);
stack->m_num = v_res_170_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_contains___redArg___boxed(lean_object* v_cmp_171_, lean_object* v_l_172_, lean_object* v_a_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Std_ExtTreeSet_contains___redArg(v_cmp_171_, v_l_172_, v_a_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
uint8_t l_Std_ExtTreeSet_contains(lean_object* v_00_u03b1_176_, lean_object* v_cmp_177_, lean_object* v_inst_178_, lean_object* v_l_179_, lean_object* v_a_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_177_, v_a_180_, v_l_179_);
return v___x_181_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_177_ = stack[1].m_obj;
lean_object* v_l_179_ = stack[3].m_obj;
lean_object* v_a_180_ = stack[4].m_obj;
uint8_t v_res_182_;
v_res_182_ = l_Std_ExtTreeSet_contains(lean_box(0), v_cmp_177_, lean_box(0), v_l_179_, v_a_180_);
stack->m_num = v_res_182_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_contains___boxed(lean_object* v_00_u03b1_183_, lean_object* v_cmp_184_, lean_object* v_inst_185_, lean_object* v_l_186_, lean_object* v_a_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = l_Std_ExtTreeSet_contains(v_00_u03b1_183_, v_cmp_184_, v_inst_185_, v_l_186_, v_a_187_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg(){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_192_;
v_res_192_ = l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg();
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg___boxed(lean_object* v___dummy_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg();
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp(lean_object* v_00_u03b1_195_, lean_object* v_cmp_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_box(0);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_199_, lean_object* v_cmp_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_ExtTreeSet_instMembershipOfTransCmp(v_00_u03b1_199_, v_cmp_200_, v_inst_201_);
lean_dec_ref(v_cmp_200_);
return v_res_202_;
}
}
uint8_t l_Std_ExtTreeSet_instDecidableMem___redArg(lean_object* v_cmp_203_, lean_object* v_m_204_, lean_object* v_a_205_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_203_, v_a_205_, v_m_204_);
return v___x_206_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_203_ = stack[0].m_obj;
lean_object* v_m_204_ = stack[1].m_obj;
lean_object* v_a_205_ = stack[2].m_obj;
uint8_t v_res_207_;
v_res_207_ = l_Std_ExtTreeSet_instDecidableMem___redArg(v_cmp_203_, v_m_204_, v_a_205_);
stack->m_num = v_res_207_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableMem___redArg___boxed(lean_object* v_cmp_208_, lean_object* v_m_209_, lean_object* v_a_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Std_ExtTreeSet_instDecidableMem___redArg(v_cmp_208_, v_m_209_, v_a_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
uint8_t l_Std_ExtTreeSet_instDecidableMem(lean_object* v_00_u03b1_213_, lean_object* v_cmp_214_, lean_object* v_inst_215_, lean_object* v_m_216_, lean_object* v_a_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_214_, v_a_217_, v_m_216_);
return v___x_218_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_214_ = stack[1].m_obj;
lean_object* v_m_216_ = stack[3].m_obj;
lean_object* v_a_217_ = stack[4].m_obj;
uint8_t v_res_219_;
v_res_219_ = l_Std_ExtTreeSet_instDecidableMem(lean_box(0), v_cmp_214_, lean_box(0), v_m_216_, v_a_217_);
stack->m_num = v_res_219_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableMem___boxed(lean_object* v_00_u03b1_220_, lean_object* v_cmp_221_, lean_object* v_inst_222_, lean_object* v_m_223_, lean_object* v_a_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Std_ExtTreeSet_instDecidableMem(v_00_u03b1_220_, v_cmp_221_, v_inst_222_, v_m_223_, v_a_224_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___redArg(lean_object* v_t_227_){
_start:
{
if (lean_obj_tag(v_t_227_) == 0)
{
lean_object* v_size_228_; 
v_size_228_ = lean_ctor_get(v_t_227_, 0);
lean_inc(v_size_228_);
return v_size_228_;
}
else
{
lean_object* v___x_229_; 
v___x_229_ = lean_unsigned_to_nat(0u);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___redArg___boxed(lean_object* v_t_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_ExtTreeSet_size___redArg(v_t_230_);
lean_dec(v_t_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size(lean_object* v_00_u03b1_232_, lean_object* v_cmp_233_, lean_object* v_t_234_){
_start:
{
if (lean_obj_tag(v_t_234_) == 0)
{
lean_object* v_size_235_; 
v_size_235_ = lean_ctor_get(v_t_234_, 0);
lean_inc(v_size_235_);
return v_size_235_;
}
else
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(0u);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___boxed(lean_object* v_00_u03b1_237_, lean_object* v_cmp_238_, lean_object* v_t_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_ExtTreeSet_size(v_00_u03b1_237_, v_cmp_238_, v_t_239_);
lean_dec(v_t_239_);
lean_dec_ref(v_cmp_238_);
return v_res_240_;
}
}
uint8_t l_Std_ExtTreeSet_isEmpty___redArg(lean_object* v_t_241_){
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
LEAN_EXPORT void l_Std_ExtTreeSet_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_241_ = stack[0].m_obj;
uint8_t v_res_244_;
v_res_244_ = l_Std_ExtTreeSet_isEmpty___redArg(v_t_241_);
stack->m_num = v_res_244_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_isEmpty___redArg___boxed(lean_object* v_t_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Std_ExtTreeSet_isEmpty___redArg(v_t_245_);
lean_dec(v_t_245_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
uint8_t l_Std_ExtTreeSet_isEmpty(lean_object* v_00_u03b1_248_, lean_object* v_cmp_249_, lean_object* v_t_250_){
_start:
{
if (lean_obj_tag(v_t_250_) == 0)
{
uint8_t v___x_251_; 
v___x_251_ = 0;
return v___x_251_;
}
else
{
uint8_t v___x_252_; 
v___x_252_ = 1;
return v___x_252_;
}
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_249_ = stack[1].m_obj;
lean_object* v_t_250_ = stack[2].m_obj;
uint8_t v_res_253_;
v_res_253_ = l_Std_ExtTreeSet_isEmpty(lean_box(0), v_cmp_249_, v_t_250_);
stack->m_num = v_res_253_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_isEmpty___boxed(lean_object* v_00_u03b1_254_, lean_object* v_cmp_255_, lean_object* v_t_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Std_ExtTreeSet_isEmpty(v_00_u03b1_254_, v_cmp_255_, v_t_256_);
lean_dec(v_t_256_);
lean_dec_ref(v_cmp_255_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_erase___redArg(lean_object* v_cmp_259_, lean_object* v_t_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_259_, v_a_261_, v_t_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_erase(lean_object* v_00_u03b1_263_, lean_object* v_cmp_264_, lean_object* v_inst_265_, lean_object* v_t_266_, lean_object* v_a_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_264_, v_a_267_, v_t_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x3f___redArg(lean_object* v_cmp_269_, lean_object* v_t_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_269_, v_t_270_, v_a_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x3f(lean_object* v_00_u03b1_273_, lean_object* v_cmp_274_, lean_object* v_inst_275_, lean_object* v_t_276_, lean_object* v_a_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_274_, v_t_276_, v_a_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get___redArg(lean_object* v_cmp_279_, lean_object* v_t_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_279_, v_t_280_, v_a_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get(lean_object* v_00_u03b1_283_, lean_object* v_cmp_284_, lean_object* v_inst_285_, lean_object* v_t_286_, lean_object* v_a_287_, lean_object* v_h_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_284_, v_t_286_, v_a_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___redArg(lean_object* v_cmp_290_, lean_object* v_inst_291_, lean_object* v_t_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_290_, v_t_292_, v_a_293_, v_inst_291_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___redArg___boxed(lean_object* v_cmp_295_, lean_object* v_inst_296_, lean_object* v_t_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Std_ExtTreeSet_get_x21___redArg(v_cmp_295_, v_inst_296_, v_t_297_, v_a_298_);
lean_dec(v_inst_296_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21(lean_object* v_00_u03b1_300_, lean_object* v_cmp_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_t_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_301_, v_t_304_, v_a_305_, v_inst_303_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___boxed(lean_object* v_00_u03b1_307_, lean_object* v_cmp_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_t_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_ExtTreeSet_get_x21(v_00_u03b1_307_, v_cmp_308_, v_inst_309_, v_inst_310_, v_t_311_, v_a_312_);
lean_dec(v_inst_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg(lean_object* v_cmp_314_, lean_object* v_t_315_, lean_object* v_a_316_, lean_object* v_fallback_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_314_, v_t_315_, v_a_316_, v_fallback_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg___boxed(lean_object* v_cmp_319_, lean_object* v_t_320_, lean_object* v_a_321_, lean_object* v_fallback_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_ExtTreeSet_getD___redArg(v_cmp_319_, v_t_320_, v_a_321_, v_fallback_322_);
lean_dec(v_fallback_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD(lean_object* v_00_u03b1_324_, lean_object* v_cmp_325_, lean_object* v_inst_326_, lean_object* v_t_327_, lean_object* v_a_328_, lean_object* v_fallback_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_325_, v_t_327_, v_a_328_, v_fallback_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___boxed(lean_object* v_00_u03b1_331_, lean_object* v_cmp_332_, lean_object* v_inst_333_, lean_object* v_t_334_, lean_object* v_a_335_, lean_object* v_fallback_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_ExtTreeSet_getD(v_00_u03b1_331_, v_cmp_332_, v_inst_333_, v_t_334_, v_a_335_, v_fallback_336_);
lean_dec(v_fallback_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg(lean_object* v_t_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg___boxed(lean_object* v_t_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_ExtTreeSet_min_x3f___redArg(v_t_340_);
lean_dec(v_t_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f(lean_object* v_00_u03b1_342_, lean_object* v_cmp_343_, lean_object* v_inst_344_, lean_object* v_t_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___boxed(lean_object* v_00_u03b1_347_, lean_object* v_cmp_348_, lean_object* v_inst_349_, lean_object* v_t_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Std_ExtTreeSet_min_x3f(v_00_u03b1_347_, v_cmp_348_, v_inst_349_, v_t_350_);
lean_dec(v_t_350_);
lean_dec_ref(v_cmp_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg(lean_object* v_t_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg___boxed(lean_object* v_t_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_ExtTreeSet_min___redArg(v_t_354_);
lean_dec(v_t_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min(lean_object* v_00_u03b1_356_, lean_object* v_cmp_357_, lean_object* v_inst_358_, lean_object* v_t_359_, lean_object* v_h_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___boxed(lean_object* v_00_u03b1_362_, lean_object* v_cmp_363_, lean_object* v_inst_364_, lean_object* v_t_365_, lean_object* v_h_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_ExtTreeSet_min(v_00_u03b1_362_, v_cmp_363_, v_inst_364_, v_t_365_, v_h_366_);
lean_dec(v_t_365_);
lean_dec_ref(v_cmp_363_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg(lean_object* v_inst_368_, lean_object* v_t_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_368_, v_t_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg___boxed(lean_object* v_inst_371_, lean_object* v_t_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_ExtTreeSet_min_x21___redArg(v_inst_371_, v_t_372_);
lean_dec(v_t_372_);
lean_dec(v_inst_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21(lean_object* v_00_u03b1_374_, lean_object* v_cmp_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_t_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_377_, v_t_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___boxed(lean_object* v_00_u03b1_380_, lean_object* v_cmp_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_t_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_ExtTreeSet_min_x21(v_00_u03b1_380_, v_cmp_381_, v_inst_382_, v_inst_383_, v_t_384_);
lean_dec(v_t_384_);
lean_dec(v_inst_383_);
lean_dec_ref(v_cmp_381_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg(lean_object* v_t_386_, lean_object* v_fallback_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_386_, v_fallback_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg___boxed(lean_object* v_t_389_, lean_object* v_fallback_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_ExtTreeSet_minD___redArg(v_t_389_, v_fallback_390_);
lean_dec(v_fallback_390_);
lean_dec(v_t_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD(lean_object* v_00_u03b1_392_, lean_object* v_cmp_393_, lean_object* v_inst_394_, lean_object* v_t_395_, lean_object* v_fallback_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_395_, v_fallback_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___boxed(lean_object* v_00_u03b1_398_, lean_object* v_cmp_399_, lean_object* v_inst_400_, lean_object* v_t_401_, lean_object* v_fallback_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_ExtTreeSet_minD(v_00_u03b1_398_, v_cmp_399_, v_inst_400_, v_t_401_, v_fallback_402_);
lean_dec(v_fallback_402_);
lean_dec(v_t_401_);
lean_dec_ref(v_cmp_399_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg(lean_object* v_t_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg___boxed(lean_object* v_t_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_ExtTreeSet_max_x3f___redArg(v_t_406_);
lean_dec(v_t_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f(lean_object* v_00_u03b1_408_, lean_object* v_cmp_409_, lean_object* v_inst_410_, lean_object* v_t_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___boxed(lean_object* v_00_u03b1_413_, lean_object* v_cmp_414_, lean_object* v_inst_415_, lean_object* v_t_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_ExtTreeSet_max_x3f(v_00_u03b1_413_, v_cmp_414_, v_inst_415_, v_t_416_);
lean_dec(v_t_416_);
lean_dec_ref(v_cmp_414_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg(lean_object* v_t_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg___boxed(lean_object* v_t_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_ExtTreeSet_max___redArg(v_t_420_);
lean_dec(v_t_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max(lean_object* v_00_u03b1_422_, lean_object* v_cmp_423_, lean_object* v_inst_424_, lean_object* v_t_425_, lean_object* v_h_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___boxed(lean_object* v_00_u03b1_428_, lean_object* v_cmp_429_, lean_object* v_inst_430_, lean_object* v_t_431_, lean_object* v_h_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_ExtTreeSet_max(v_00_u03b1_428_, v_cmp_429_, v_inst_430_, v_t_431_, v_h_432_);
lean_dec(v_t_431_);
lean_dec_ref(v_cmp_429_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg(lean_object* v_inst_434_, lean_object* v_t_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_434_, v_t_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg___boxed(lean_object* v_inst_437_, lean_object* v_t_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_ExtTreeSet_max_x21___redArg(v_inst_437_, v_t_438_);
lean_dec(v_t_438_);
lean_dec(v_inst_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21(lean_object* v_00_u03b1_440_, lean_object* v_cmp_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_t_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_443_, v_t_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___boxed(lean_object* v_00_u03b1_446_, lean_object* v_cmp_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_t_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_ExtTreeSet_max_x21(v_00_u03b1_446_, v_cmp_447_, v_inst_448_, v_inst_449_, v_t_450_);
lean_dec(v_t_450_);
lean_dec(v_inst_449_);
lean_dec_ref(v_cmp_447_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg(lean_object* v_t_452_, lean_object* v_fallback_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_452_, v_fallback_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg___boxed(lean_object* v_t_455_, lean_object* v_fallback_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_ExtTreeSet_maxD___redArg(v_t_455_, v_fallback_456_);
lean_dec(v_fallback_456_);
lean_dec(v_t_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD(lean_object* v_00_u03b1_458_, lean_object* v_cmp_459_, lean_object* v_inst_460_, lean_object* v_t_461_, lean_object* v_fallback_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_461_, v_fallback_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___boxed(lean_object* v_00_u03b1_464_, lean_object* v_cmp_465_, lean_object* v_inst_466_, lean_object* v_t_467_, lean_object* v_fallback_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_ExtTreeSet_maxD(v_00_u03b1_464_, v_cmp_465_, v_inst_466_, v_t_467_, v_fallback_468_);
lean_dec(v_fallback_468_);
lean_dec(v_t_467_);
lean_dec_ref(v_cmp_465_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg(lean_object* v_t_470_, lean_object* v_n_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_470_, v_n_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg___boxed(lean_object* v_t_473_, lean_object* v_n_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_ExtTreeSet_atIdx_x3f___redArg(v_t_473_, v_n_474_);
lean_dec(v_t_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f(lean_object* v_00_u03b1_476_, lean_object* v_cmp_477_, lean_object* v_inst_478_, lean_object* v_t_479_, lean_object* v_n_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_479_, v_n_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___boxed(lean_object* v_00_u03b1_482_, lean_object* v_cmp_483_, lean_object* v_inst_484_, lean_object* v_t_485_, lean_object* v_n_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_ExtTreeSet_atIdx_x3f(v_00_u03b1_482_, v_cmp_483_, v_inst_484_, v_t_485_, v_n_486_);
lean_dec(v_t_485_);
lean_dec_ref(v_cmp_483_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg(lean_object* v_t_488_, lean_object* v_n_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_488_, v_n_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg___boxed(lean_object* v_t_491_, lean_object* v_n_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_ExtTreeSet_atIdx___redArg(v_t_491_, v_n_492_);
lean_dec(v_t_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx(lean_object* v_00_u03b1_494_, lean_object* v_cmp_495_, lean_object* v_inst_496_, lean_object* v_t_497_, lean_object* v_n_498_, lean_object* v_h_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_497_, v_n_498_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___boxed(lean_object* v_00_u03b1_501_, lean_object* v_cmp_502_, lean_object* v_inst_503_, lean_object* v_t_504_, lean_object* v_n_505_, lean_object* v_h_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_ExtTreeSet_atIdx(v_00_u03b1_501_, v_cmp_502_, v_inst_503_, v_t_504_, v_n_505_, v_h_506_);
lean_dec(v_t_504_);
lean_dec_ref(v_cmp_502_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg(lean_object* v_inst_508_, lean_object* v_t_509_, lean_object* v_n_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_508_, v_t_509_, v_n_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg___boxed(lean_object* v_inst_512_, lean_object* v_t_513_, lean_object* v_n_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_ExtTreeSet_atIdx_x21___redArg(v_inst_512_, v_t_513_, v_n_514_);
lean_dec(v_t_513_);
lean_dec(v_inst_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21(lean_object* v_00_u03b1_516_, lean_object* v_cmp_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_t_520_, lean_object* v_n_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_519_, v_t_520_, v_n_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___boxed(lean_object* v_00_u03b1_523_, lean_object* v_cmp_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_t_527_, lean_object* v_n_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_ExtTreeSet_atIdx_x21(v_00_u03b1_523_, v_cmp_524_, v_inst_525_, v_inst_526_, v_t_527_, v_n_528_);
lean_dec(v_t_527_);
lean_dec(v_inst_526_);
lean_dec_ref(v_cmp_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg(lean_object* v_t_530_, lean_object* v_n_531_, lean_object* v_fallback_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_530_, v_n_531_, v_fallback_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg___boxed(lean_object* v_t_534_, lean_object* v_n_535_, lean_object* v_fallback_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_ExtTreeSet_atIdxD___redArg(v_t_534_, v_n_535_, v_fallback_536_);
lean_dec(v_fallback_536_);
lean_dec(v_t_534_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD(lean_object* v_00_u03b1_538_, lean_object* v_cmp_539_, lean_object* v_inst_540_, lean_object* v_t_541_, lean_object* v_n_542_, lean_object* v_fallback_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_541_, v_n_542_, v_fallback_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___boxed(lean_object* v_00_u03b1_545_, lean_object* v_cmp_546_, lean_object* v_inst_547_, lean_object* v_t_548_, lean_object* v_n_549_, lean_object* v_fallback_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_ExtTreeSet_atIdxD(v_00_u03b1_545_, v_cmp_546_, v_inst_547_, v_t_548_, v_n_549_, v_fallback_550_);
lean_dec(v_fallback_550_);
lean_dec(v_t_548_);
lean_dec_ref(v_cmp_546_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f___redArg(lean_object* v_cmp_552_, lean_object* v_t_553_, lean_object* v_k_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_box(0);
v___x_556_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_552_, v_k_554_, v___x_555_, v_t_553_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f(lean_object* v_00_u03b1_557_, lean_object* v_cmp_558_, lean_object* v_inst_559_, lean_object* v_t_560_, lean_object* v_k_561_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_box(0);
v___x_563_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_558_, v_k_561_, v___x_562_, v_t_560_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f___redArg(lean_object* v_cmp_564_, lean_object* v_t_565_, lean_object* v_k_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_box(0);
v___x_568_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_564_, v_k_566_, v___x_567_, v_t_565_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f(lean_object* v_00_u03b1_569_, lean_object* v_cmp_570_, lean_object* v_inst_571_, lean_object* v_t_572_, lean_object* v_k_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_box(0);
v___x_575_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_570_, v_k_573_, v___x_574_, v_t_572_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f___redArg(lean_object* v_cmp_576_, lean_object* v_t_577_, lean_object* v_k_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_box(0);
v___x_580_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_576_, v_k_578_, v___x_579_, v_t_577_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f(lean_object* v_00_u03b1_581_, lean_object* v_cmp_582_, lean_object* v_inst_583_, lean_object* v_t_584_, lean_object* v_k_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_box(0);
v___x_587_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_582_, v_k_585_, v___x_586_, v_t_584_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f___redArg(lean_object* v_cmp_588_, lean_object* v_t_589_, lean_object* v_k_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_box(0);
v___x_592_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_588_, v_k_590_, v___x_591_, v_t_589_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f(lean_object* v_00_u03b1_593_, lean_object* v_cmp_594_, lean_object* v_inst_595_, lean_object* v_t_596_, lean_object* v_k_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_box(0);
v___x_599_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_594_, v_k_597_, v___x_598_, v_t_596_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE___redArg(lean_object* v_cmp_600_, lean_object* v_t_601_, lean_object* v_k_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_600_, v_k_602_, v_t_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE(lean_object* v_00_u03b1_604_, lean_object* v_cmp_605_, lean_object* v_inst_606_, lean_object* v_t_607_, lean_object* v_k_608_, lean_object* v_h_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_605_, v_k_608_, v_t_607_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT___redArg(lean_object* v_cmp_611_, lean_object* v_t_612_, lean_object* v_k_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_611_, v_k_613_, v_t_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT(lean_object* v_00_u03b1_615_, lean_object* v_cmp_616_, lean_object* v_inst_617_, lean_object* v_t_618_, lean_object* v_k_619_, lean_object* v_h_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_616_, v_k_619_, v_t_618_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE___redArg(lean_object* v_cmp_622_, lean_object* v_t_623_, lean_object* v_k_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_622_, v_k_624_, v_t_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE(lean_object* v_00_u03b1_626_, lean_object* v_cmp_627_, lean_object* v_inst_628_, lean_object* v_t_629_, lean_object* v_k_630_, lean_object* v_h_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_627_, v_k_630_, v_t_629_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT___redArg(lean_object* v_cmp_633_, lean_object* v_t_634_, lean_object* v_k_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_633_, v_k_635_, v_t_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT(lean_object* v_00_u03b1_637_, lean_object* v_cmp_638_, lean_object* v_inst_639_, lean_object* v_t_640_, lean_object* v_k_641_, lean_object* v_h_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_638_, v_k_641_, v_t_640_);
return v___x_643_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_647_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__2));
v___x_648_ = lean_unsigned_to_nat(14u);
v___x_649_ = lean_unsigned_to_nat(22u);
v___x_650_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__1));
v___x_651_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__0));
v___x_652_ = l_mkPanicMessageWithDecl(v___x_651_, v___x_650_, v___x_649_, v___x_648_, v___x_647_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___redArg(lean_object* v_cmp_653_, lean_object* v_inst_654_, lean_object* v_t_655_, lean_object* v_k_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_box(0);
v___x_658_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_653_, v_k_656_, v___x_657_, v_t_655_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_660_ = l_panic___redArg(v_inst_654_, v___x_659_);
return v___x_660_;
}
else
{
lean_object* v_val_661_; 
v_val_661_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_val_661_);
lean_dec_ref_known(v___x_658_, 1);
return v_val_661_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___redArg___boxed(lean_object* v_cmp_662_, lean_object* v_inst_663_, lean_object* v_t_664_, lean_object* v_k_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_ExtTreeSet_getGE_x21___redArg(v_cmp_662_, v_inst_663_, v_t_664_, v_k_665_);
lean_dec(v_inst_663_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21(lean_object* v_00_u03b1_667_, lean_object* v_cmp_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_t_671_, lean_object* v_k_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_box(0);
v___x_674_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_668_, v_k_672_, v___x_673_, v_t_671_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_676_ = l_panic___redArg(v_inst_670_, v___x_675_);
return v___x_676_;
}
else
{
lean_object* v_val_677_; 
v_val_677_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v___x_674_, 1);
return v_val_677_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___boxed(lean_object* v_00_u03b1_678_, lean_object* v_cmp_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_t_682_, lean_object* v_k_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_ExtTreeSet_getGE_x21(v_00_u03b1_678_, v_cmp_679_, v_inst_680_, v_inst_681_, v_t_682_, v_k_683_);
lean_dec(v_inst_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg(lean_object* v_cmp_685_, lean_object* v_inst_686_, lean_object* v_t_687_, lean_object* v_k_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_box(0);
v___x_690_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_685_, v_k_688_, v___x_689_, v_t_687_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_692_ = l_panic___redArg(v_inst_686_, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v_val_693_; 
v_val_693_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_val_693_);
lean_dec_ref_known(v___x_690_, 1);
return v_val_693_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg___boxed(lean_object* v_cmp_694_, lean_object* v_inst_695_, lean_object* v_t_696_, lean_object* v_k_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_ExtTreeSet_getGT_x21___redArg(v_cmp_694_, v_inst_695_, v_t_696_, v_k_697_);
lean_dec(v_inst_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21(lean_object* v_00_u03b1_699_, lean_object* v_cmp_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_t_703_, lean_object* v_k_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_box(0);
v___x_706_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_700_, v_k_704_, v___x_705_, v_t_703_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_708_ = l_panic___redArg(v_inst_702_, v___x_707_);
return v___x_708_;
}
else
{
lean_object* v_val_709_; 
v_val_709_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v___x_706_, 1);
return v_val_709_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___boxed(lean_object* v_00_u03b1_710_, lean_object* v_cmp_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_t_714_, lean_object* v_k_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_ExtTreeSet_getGT_x21(v_00_u03b1_710_, v_cmp_711_, v_inst_712_, v_inst_713_, v_t_714_, v_k_715_);
lean_dec(v_inst_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg(lean_object* v_cmp_717_, lean_object* v_inst_718_, lean_object* v_t_719_, lean_object* v_k_720_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_box(0);
v___x_722_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_717_, v_k_720_, v___x_721_, v_t_719_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_724_ = l_panic___redArg(v_inst_718_, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v_val_725_; 
v_val_725_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_val_725_);
lean_dec_ref_known(v___x_722_, 1);
return v_val_725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg___boxed(lean_object* v_cmp_726_, lean_object* v_inst_727_, lean_object* v_t_728_, lean_object* v_k_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_ExtTreeSet_getLE_x21___redArg(v_cmp_726_, v_inst_727_, v_t_728_, v_k_729_);
lean_dec(v_inst_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21(lean_object* v_00_u03b1_731_, lean_object* v_cmp_732_, lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_t_735_, lean_object* v_k_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_box(0);
v___x_738_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_732_, v_k_736_, v___x_737_, v_t_735_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_740_ = l_panic___redArg(v_inst_734_, v___x_739_);
return v___x_740_;
}
else
{
lean_object* v_val_741_; 
v_val_741_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v___x_738_, 1);
return v_val_741_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___boxed(lean_object* v_00_u03b1_742_, lean_object* v_cmp_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_t_746_, lean_object* v_k_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_ExtTreeSet_getLE_x21(v_00_u03b1_742_, v_cmp_743_, v_inst_744_, v_inst_745_, v_t_746_, v_k_747_);
lean_dec(v_inst_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg(lean_object* v_cmp_749_, lean_object* v_inst_750_, lean_object* v_t_751_, lean_object* v_k_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_box(0);
v___x_754_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_749_, v_k_752_, v___x_753_, v_t_751_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_756_ = l_panic___redArg(v_inst_750_, v___x_755_);
return v___x_756_;
}
else
{
lean_object* v_val_757_; 
v_val_757_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_val_757_);
lean_dec_ref_known(v___x_754_, 1);
return v_val_757_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg___boxed(lean_object* v_cmp_758_, lean_object* v_inst_759_, lean_object* v_t_760_, lean_object* v_k_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_ExtTreeSet_getLT_x21___redArg(v_cmp_758_, v_inst_759_, v_t_760_, v_k_761_);
lean_dec(v_inst_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21(lean_object* v_00_u03b1_763_, lean_object* v_cmp_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_t_767_, lean_object* v_k_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_box(0);
v___x_770_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_764_, v_k_768_, v___x_769_, v_t_767_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_772_ = l_panic___redArg(v_inst_766_, v___x_771_);
return v___x_772_;
}
else
{
lean_object* v_val_773_; 
v_val_773_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v___x_770_, 1);
return v_val_773_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___boxed(lean_object* v_00_u03b1_774_, lean_object* v_cmp_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_t_778_, lean_object* v_k_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_ExtTreeSet_getLT_x21(v_00_u03b1_774_, v_cmp_775_, v_inst_776_, v_inst_777_, v_t_778_, v_k_779_);
lean_dec(v_inst_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg(lean_object* v_cmp_781_, lean_object* v_t_782_, lean_object* v_k_783_, lean_object* v_fallback_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_box(0);
v___x_786_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_781_, v_k_783_, v___x_785_, v_t_782_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_inc(v_fallback_784_);
return v_fallback_784_;
}
else
{
lean_object* v_val_787_; 
v_val_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v___x_786_, 1);
return v_val_787_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg___boxed(lean_object* v_cmp_788_, lean_object* v_t_789_, lean_object* v_k_790_, lean_object* v_fallback_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_ExtTreeSet_getGED___redArg(v_cmp_788_, v_t_789_, v_k_790_, v_fallback_791_);
lean_dec(v_fallback_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED(lean_object* v_00_u03b1_793_, lean_object* v_cmp_794_, lean_object* v_inst_795_, lean_object* v_t_796_, lean_object* v_k_797_, lean_object* v_fallback_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_box(0);
v___x_800_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_794_, v_k_797_, v___x_799_, v_t_796_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_inc(v_fallback_798_);
return v_fallback_798_;
}
else
{
lean_object* v_val_801_; 
v_val_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v___x_800_, 1);
return v_val_801_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___boxed(lean_object* v_00_u03b1_802_, lean_object* v_cmp_803_, lean_object* v_inst_804_, lean_object* v_t_805_, lean_object* v_k_806_, lean_object* v_fallback_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_ExtTreeSet_getGED(v_00_u03b1_802_, v_cmp_803_, v_inst_804_, v_t_805_, v_k_806_, v_fallback_807_);
lean_dec(v_fallback_807_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg(lean_object* v_cmp_809_, lean_object* v_t_810_, lean_object* v_k_811_, lean_object* v_fallback_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_box(0);
v___x_814_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_809_, v_k_811_, v___x_813_, v_t_810_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_inc(v_fallback_812_);
return v_fallback_812_;
}
else
{
lean_object* v_val_815_; 
v_val_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_val_815_);
lean_dec_ref_known(v___x_814_, 1);
return v_val_815_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg___boxed(lean_object* v_cmp_816_, lean_object* v_t_817_, lean_object* v_k_818_, lean_object* v_fallback_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_ExtTreeSet_getGTD___redArg(v_cmp_816_, v_t_817_, v_k_818_, v_fallback_819_);
lean_dec(v_fallback_819_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD(lean_object* v_00_u03b1_821_, lean_object* v_cmp_822_, lean_object* v_inst_823_, lean_object* v_t_824_, lean_object* v_k_825_, lean_object* v_fallback_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_box(0);
v___x_828_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_822_, v_k_825_, v___x_827_, v_t_824_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_inc(v_fallback_826_);
return v_fallback_826_;
}
else
{
lean_object* v_val_829_; 
v_val_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v___x_828_, 1);
return v_val_829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___boxed(lean_object* v_00_u03b1_830_, lean_object* v_cmp_831_, lean_object* v_inst_832_, lean_object* v_t_833_, lean_object* v_k_834_, lean_object* v_fallback_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_ExtTreeSet_getGTD(v_00_u03b1_830_, v_cmp_831_, v_inst_832_, v_t_833_, v_k_834_, v_fallback_835_);
lean_dec(v_fallback_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg(lean_object* v_cmp_837_, lean_object* v_t_838_, lean_object* v_k_839_, lean_object* v_fallback_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_box(0);
v___x_842_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_837_, v_k_839_, v___x_841_, v_t_838_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_inc(v_fallback_840_);
return v_fallback_840_;
}
else
{
lean_object* v_val_843_; 
v_val_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v___x_842_, 1);
return v_val_843_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg___boxed(lean_object* v_cmp_844_, lean_object* v_t_845_, lean_object* v_k_846_, lean_object* v_fallback_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_ExtTreeSet_getLED___redArg(v_cmp_844_, v_t_845_, v_k_846_, v_fallback_847_);
lean_dec(v_fallback_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED(lean_object* v_00_u03b1_849_, lean_object* v_cmp_850_, lean_object* v_inst_851_, lean_object* v_t_852_, lean_object* v_k_853_, lean_object* v_fallback_854_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_box(0);
v___x_856_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_850_, v_k_853_, v___x_855_, v_t_852_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_inc(v_fallback_854_);
return v_fallback_854_;
}
else
{
lean_object* v_val_857_; 
v_val_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v___x_856_, 1);
return v_val_857_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___boxed(lean_object* v_00_u03b1_858_, lean_object* v_cmp_859_, lean_object* v_inst_860_, lean_object* v_t_861_, lean_object* v_k_862_, lean_object* v_fallback_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_ExtTreeSet_getLED(v_00_u03b1_858_, v_cmp_859_, v_inst_860_, v_t_861_, v_k_862_, v_fallback_863_);
lean_dec(v_fallback_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg(lean_object* v_cmp_865_, lean_object* v_t_866_, lean_object* v_k_867_, lean_object* v_fallback_868_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_box(0);
v___x_870_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_865_, v_k_867_, v___x_869_, v_t_866_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_inc(v_fallback_868_);
return v_fallback_868_;
}
else
{
lean_object* v_val_871_; 
v_val_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v___x_870_, 1);
return v_val_871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg___boxed(lean_object* v_cmp_872_, lean_object* v_t_873_, lean_object* v_k_874_, lean_object* v_fallback_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_ExtTreeSet_getLTD___redArg(v_cmp_872_, v_t_873_, v_k_874_, v_fallback_875_);
lean_dec(v_fallback_875_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD(lean_object* v_00_u03b1_877_, lean_object* v_cmp_878_, lean_object* v_inst_879_, lean_object* v_t_880_, lean_object* v_k_881_, lean_object* v_fallback_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_box(0);
v___x_884_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_878_, v_k_881_, v___x_883_, v_t_880_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_inc(v_fallback_882_);
return v_fallback_882_;
}
else
{
lean_object* v_val_885_; 
v_val_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v___x_884_, 1);
return v_val_885_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___boxed(lean_object* v_00_u03b1_886_, lean_object* v_cmp_887_, lean_object* v_inst_888_, lean_object* v_t_889_, lean_object* v_k_890_, lean_object* v_fallback_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_ExtTreeSet_getLTD(v_00_u03b1_886_, v_cmp_887_, v_inst_888_, v_t_889_, v_k_890_, v_fallback_891_);
lean_dec(v_fallback_891_);
return v_res_892_;
}
}
uint8_t l_Std_ExtTreeSet_filter___redArg___lam__0(lean_object* v_f_893_, lean_object* v_a_894_, lean_object* v_x_895_){
_start:
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = lean_apply_1(v_f_893_, v_a_894_);
v___x_897_ = lean_unbox(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_filter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_893_ = stack[0].m_obj;
lean_object* v_a_894_ = stack[1].m_obj;
lean_object* v_x_895_ = stack[2].m_obj;
uint8_t v_res_898_;
v_res_898_ = l_Std_ExtTreeSet_filter___redArg___lam__0(v_f_893_, v_a_894_, v_x_895_);
stack->m_num = v_res_898_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg___lam__0___boxed(lean_object* v_f_899_, lean_object* v_a_900_, lean_object* v_x_901_){
_start:
{
uint8_t v_res_902_; lean_object* v_r_903_; 
v_res_902_ = l_Std_ExtTreeSet_filter___redArg___lam__0(v_f_899_, v_a_900_, v_x_901_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg(lean_object* v_f_904_, lean_object* v_m_905_){
_start:
{
lean_object* v___f_906_; lean_object* v___x_907_; 
v___f_906_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_906_, 0, v_f_904_);
v___x_907_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_906_, v_m_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter(lean_object* v_00_u03b1_908_, lean_object* v_cmp_909_, lean_object* v_f_910_, lean_object* v_m_911_){
_start:
{
lean_object* v___f_912_; lean_object* v___x_913_; 
v___f_912_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_912_, 0, v_f_910_);
v___x_913_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_912_, v_m_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___boxed(lean_object* v_00_u03b1_914_, lean_object* v_cmp_915_, lean_object* v_f_916_, lean_object* v_m_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Std_ExtTreeSet_filter(v_00_u03b1_914_, v_cmp_915_, v_f_916_, v_m_917_);
lean_dec_ref(v_cmp_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg___lam__0(lean_object* v_f_919_, lean_object* v_c_920_, lean_object* v_a_921_, lean_object* v_x_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = lean_apply_2(v_f_919_, v_c_920_, v_a_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg(lean_object* v_inst_924_, lean_object* v_f_925_, lean_object* v_init_926_, lean_object* v_t_927_){
_start:
{
lean_object* v___f_928_; lean_object* v___x_929_; 
v___f_928_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_928_, 0, v_f_925_);
v___x_929_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_924_, v___f_928_, v_init_926_, v_t_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM(lean_object* v_00_u03b1_930_, lean_object* v_cmp_931_, lean_object* v_00_u03b4_932_, lean_object* v_m_933_, lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_f_937_, lean_object* v_init_938_, lean_object* v_t_939_){
_start:
{
lean_object* v___f_940_; lean_object* v___x_941_; 
v___f_940_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_940_, 0, v_f_937_);
v___x_941_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_934_, v___f_940_, v_init_938_, v_t_939_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___boxed(lean_object* v_00_u03b1_942_, lean_object* v_cmp_943_, lean_object* v_00_u03b4_944_, lean_object* v_m_945_, lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_inst_948_, lean_object* v_f_949_, lean_object* v_init_950_, lean_object* v_t_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_ExtTreeSet_foldlM(v_00_u03b1_942_, v_cmp_943_, v_00_u03b4_944_, v_m_945_, v_inst_946_, v_inst_947_, v_inst_948_, v_f_949_, v_init_950_, v_t_951_);
lean_dec_ref(v_cmp_943_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___redArg(lean_object* v_f_953_, lean_object* v_init_954_, lean_object* v_t_955_){
_start:
{
lean_object* v___f_956_; lean_object* v___x_957_; 
v___f_956_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_956_, 0, v_f_953_);
v___x_957_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_956_, v_init_954_, v_t_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl(lean_object* v_00_u03b1_958_, lean_object* v_cmp_959_, lean_object* v_00_u03b4_960_, lean_object* v_inst_961_, lean_object* v_f_962_, lean_object* v_init_963_, lean_object* v_t_964_){
_start:
{
lean_object* v___f_965_; lean_object* v___x_966_; 
v___f_965_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_965_, 0, v_f_962_);
v___x_966_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_965_, v_init_963_, v_t_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___boxed(lean_object* v_00_u03b1_967_, lean_object* v_cmp_968_, lean_object* v_00_u03b4_969_, lean_object* v_inst_970_, lean_object* v_f_971_, lean_object* v_init_972_, lean_object* v_t_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Std_ExtTreeSet_foldl(v_00_u03b1_967_, v_cmp_968_, v_00_u03b4_969_, v_inst_970_, v_f_971_, v_init_972_, v_t_973_);
lean_dec_ref(v_cmp_968_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg___lam__0(lean_object* v_f_975_, lean_object* v_a_976_, lean_object* v_x_977_, lean_object* v_acc_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = lean_apply_2(v_f_975_, v_a_976_, v_acc_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg(lean_object* v_inst_980_, lean_object* v_f_981_, lean_object* v_init_982_, lean_object* v_t_983_){
_start:
{
lean_object* v___f_984_; lean_object* v___x_985_; 
v___f_984_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_984_, 0, v_f_981_);
v___x_985_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_980_, v___f_984_, v_init_982_, v_t_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM(lean_object* v_00_u03b1_986_, lean_object* v_cmp_987_, lean_object* v_00_u03b4_988_, lean_object* v_m_989_, lean_object* v_inst_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_f_993_, lean_object* v_init_994_, lean_object* v_t_995_){
_start:
{
lean_object* v___f_996_; lean_object* v___x_997_; 
v___f_996_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_996_, 0, v_f_993_);
v___x_997_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_990_, v___f_996_, v_init_994_, v_t_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___boxed(lean_object* v_00_u03b1_998_, lean_object* v_cmp_999_, lean_object* v_00_u03b4_1000_, lean_object* v_m_1001_, lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_f_1005_, lean_object* v_init_1006_, lean_object* v_t_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Std_ExtTreeSet_foldrM(v_00_u03b1_998_, v_cmp_999_, v_00_u03b4_1000_, v_m_1001_, v_inst_1002_, v_inst_1003_, v_inst_1004_, v_f_1005_, v_init_1006_, v_t_1007_);
lean_dec_ref(v_cmp_999_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg___lam__0(lean_object* v_f_1009_, lean_object* v_x1_1010_, lean_object* v_x2_1011_, lean_object* v_x3_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_apply_2(v_f_1009_, v_x1_1010_, v_x3_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg(lean_object* v_f_1033_, lean_object* v_init_1034_, lean_object* v_t_1035_){
_start:
{
lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___f_1036_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1036_, 0, v_f_1033_);
v___x_1037_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1038_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1037_, v___f_1036_, v_init_1034_, v_t_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr(lean_object* v_00_u03b1_1039_, lean_object* v_cmp_1040_, lean_object* v_00_u03b4_1041_, lean_object* v_inst_1042_, lean_object* v_f_1043_, lean_object* v_init_1044_, lean_object* v_t_1045_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___f_1046_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1046_, 0, v_f_1043_);
v___x_1047_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1048_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1047_, v___f_1046_, v_init_1044_, v_t_1045_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___boxed(lean_object* v_00_u03b1_1049_, lean_object* v_cmp_1050_, lean_object* v_00_u03b4_1051_, lean_object* v_inst_1052_, lean_object* v_f_1053_, lean_object* v_init_1054_, lean_object* v_t_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_ExtTreeSet_foldr(v_00_u03b1_1049_, v_cmp_1050_, v_00_u03b4_1051_, v_inst_1052_, v_f_1053_, v_init_1054_, v_t_1055_);
lean_dec_ref(v_cmp_1050_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg___lam__0(lean_object* v_f_1057_, lean_object* v_cmp_1058_, lean_object* v_x_1059_, lean_object* v_a_1060_, lean_object* v_b_1061_){
_start:
{
lean_object* v_fst_1062_; lean_object* v_snd_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1077_; 
v_fst_1062_ = lean_ctor_get(v_x_1059_, 0);
v_snd_1063_ = lean_ctor_get(v_x_1059_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_x_1059_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1065_ = v_x_1059_;
v_isShared_1066_ = v_isSharedCheck_1077_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_snd_1063_);
lean_inc(v_fst_1062_);
lean_dec(v_x_1059_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1077_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
lean_inc(v_a_1060_);
v___x_1067_ = lean_apply_1(v_f_1057_, v_a_1060_);
v___x_1068_ = lean_unbox(v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1069_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1058_, v_a_1060_, v_b_1061_, v_snd_1063_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 1, v___x_1069_);
v___x_1071_ = v___x_1065_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_fst_1062_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1073_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1058_, v_a_1060_, v_b_1061_, v_fst_1062_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1073_);
v___x_1075_ = v___x_1065_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_snd_1063_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg(lean_object* v_cmp_1080_, lean_object* v_f_1081_, lean_object* v_t_1082_){
_start:
{
lean_object* v___f_1083_; lean_object* v___x_1084_; lean_object* v_p_1085_; lean_object* v_fst_1086_; lean_object* v_snd_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v___f_1083_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1083_, 0, v_f_1081_);
lean_closure_set(v___f_1083_, 1, v_cmp_1080_);
v___x_1084_ = ((lean_object*)(l_Std_ExtTreeSet_partition___redArg___closed__0));
v_p_1085_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1083_, v___x_1084_, v_t_1082_);
v_fst_1086_ = lean_ctor_get(v_p_1085_, 0);
v_snd_1087_ = lean_ctor_get(v_p_1085_, 1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_p_1085_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v_p_1085_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_snd_1087_);
lean_inc(v_fst_1086_);
lean_dec(v_p_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_fst_1086_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_snd_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition(lean_object* v_00_u03b1_1095_, lean_object* v_cmp_1096_, lean_object* v_inst_1097_, lean_object* v_f_1098_, lean_object* v_t_1099_){
_start:
{
lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v_p_1102_; lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v___f_1100_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1100_, 0, v_f_1098_);
lean_closure_set(v___f_1100_, 1, v_cmp_1096_);
v___x_1101_ = ((lean_object*)(l_Std_ExtTreeSet_partition___redArg___closed__0));
v_p_1102_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1100_, v___x_1101_, v_t_1099_);
v_fst_1103_ = lean_ctor_get(v_p_1102_, 0);
v_snd_1104_ = lean_ctor_get(v_p_1102_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_p_1102_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v_p_1102_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_snd_1104_);
lean_inc(v_fst_1103_);
lean_dec(v_p_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_fst_1103_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_snd_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg___lam__0(lean_object* v_f_1112_, lean_object* v_x_1113_, lean_object* v_k_1114_, lean_object* v_v_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_apply_1(v_f_1112_, v_k_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg(lean_object* v_inst_1117_, lean_object* v_f_1118_, lean_object* v_t_1119_){
_start:
{
lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___f_1120_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1120_, 0, v_f_1118_);
v___x_1121_ = lean_box(0);
v___x_1122_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1117_, v___f_1120_, v___x_1121_, v_t_1119_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM(lean_object* v_00_u03b1_1123_, lean_object* v_cmp_1124_, lean_object* v_m_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_f_1129_, lean_object* v_t_1130_){
_start:
{
lean_object* v___f_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___f_1131_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1131_, 0, v_f_1129_);
v___x_1132_ = lean_box(0);
v___x_1133_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1126_, v___f_1131_, v___x_1132_, v_t_1130_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_cmp_1135_, lean_object* v_m_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_f_1140_, lean_object* v_t_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_ExtTreeSet_forM(v_00_u03b1_1134_, v_cmp_1135_, v_m_1136_, v_inst_1137_, v_inst_1138_, v_inst_1139_, v_f_1140_, v_t_1141_);
lean_dec_ref(v_cmp_1135_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__0(lean_object* v_f_1143_, lean_object* v_a_1144_, lean_object* v_b_1145_, lean_object* v_c_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_apply_2(v_f_1143_, v_a_1144_, v_c_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__1(lean_object* v_toPure_1148_, lean_object* v_____do__lift_1149_){
_start:
{
lean_object* v_a_1150_; lean_object* v___x_1151_; 
v_a_1150_ = lean_ctor_get(v_____do__lift_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref(v_____do__lift_1149_);
v___x_1151_ = lean_apply_2(v_toPure_1148_, lean_box(0), v_a_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg(lean_object* v_inst_1152_, lean_object* v_f_1153_, lean_object* v_init_1154_, lean_object* v_t_1155_){
_start:
{
lean_object* v_toApplicative_1156_; lean_object* v_toBind_1157_; lean_object* v_toPure_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; lean_object* v___f_1161_; lean_object* v___x_1162_; 
v_toApplicative_1156_ = lean_ctor_get(v_inst_1152_, 0);
v_toBind_1157_ = lean_ctor_get(v_inst_1152_, 1);
lean_inc(v_toBind_1157_);
v_toPure_1158_ = lean_ctor_get(v_toApplicative_1156_, 1);
lean_inc(v_toPure_1158_);
v___f_1159_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1159_, 0, v_f_1153_);
v___x_1160_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1152_, v___f_1159_, v_init_1154_, v_t_1155_);
v___f_1161_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1161_, 0, v_toPure_1158_);
v___x_1162_ = lean_apply_4(v_toBind_1157_, lean_box(0), lean_box(0), v___x_1160_, v___f_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn(lean_object* v_00_u03b1_1163_, lean_object* v_cmp_1164_, lean_object* v_00_u03b4_1165_, lean_object* v_m_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_f_1170_, lean_object* v_init_1171_, lean_object* v_t_1172_){
_start:
{
lean_object* v_toApplicative_1173_; lean_object* v_toBind_1174_; lean_object* v_toPure_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; 
v_toApplicative_1173_ = lean_ctor_get(v_inst_1167_, 0);
v_toBind_1174_ = lean_ctor_get(v_inst_1167_, 1);
lean_inc(v_toBind_1174_);
v_toPure_1175_ = lean_ctor_get(v_toApplicative_1173_, 1);
lean_inc(v_toPure_1175_);
v___f_1176_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1176_, 0, v_f_1170_);
v___x_1177_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1167_, v___f_1176_, v_init_1171_, v_t_1172_);
v___f_1178_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1178_, 0, v_toPure_1175_);
v___x_1179_ = lean_apply_4(v_toBind_1174_, lean_box(0), lean_box(0), v___x_1177_, v___f_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___boxed(lean_object* v_00_u03b1_1180_, lean_object* v_cmp_1181_, lean_object* v_00_u03b4_1182_, lean_object* v_m_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_f_1187_, lean_object* v_init_1188_, lean_object* v_t_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Std_ExtTreeSet_forIn(v_00_u03b1_1180_, v_cmp_1181_, v_00_u03b4_1182_, v_m_1183_, v_inst_1184_, v_inst_1185_, v_inst_1186_, v_f_1187_, v_init_1188_, v_t_1189_);
lean_dec_ref(v_cmp_1181_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_1191_, lean_object* v_t_1192_, lean_object* v_f_1193_){
_start:
{
lean_object* v___f_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___f_1194_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1194_, 0, v_f_1193_);
v___x_1195_ = lean_box(0);
v___x_1196_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1191_, v___f_1194_, v___x_1195_, v_t_1192_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1197_){
_start:
{
lean_object* v___f_1198_; 
v___f_1198_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1198_, 0, v_inst_1197_);
return v___f_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1199_, lean_object* v_cmp_1200_, lean_object* v_m_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_){
_start:
{
lean_object* v___f_1205_; 
v___f_1205_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1205_, 0, v_inst_1203_);
return v___f_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1206_, lean_object* v_cmp_1207_, lean_object* v_m_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(v_00_u03b1_1206_, v_cmp_1207_, v_m_1208_, v_inst_1209_, v_inst_1210_, v_inst_1211_);
lean_dec_ref(v_cmp_1207_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_m_1215_, lean_object* v_init_1216_, lean_object* v_f_1217_){
_start:
{
lean_object* v_toApplicative_1218_; lean_object* v_toBind_1219_; lean_object* v_toPure_1220_; lean_object* v___f_1221_; lean_object* v___x_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; 
v_toApplicative_1218_ = lean_ctor_get(v_inst_1213_, 0);
v_toBind_1219_ = lean_ctor_get(v_inst_1213_, 1);
lean_inc(v_toBind_1219_);
v_toPure_1220_ = lean_ctor_get(v_toApplicative_1218_, 1);
lean_inc(v_toPure_1220_);
v___f_1221_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1221_, 0, v_f_1217_);
v___x_1222_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1213_, v___f_1221_, v_init_1216_, v_m_1215_);
v___f_1223_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1223_, 0, v_toPure_1220_);
v___x_1224_ = lean_apply_4(v_toBind_1219_, lean_box(0), lean_box(0), v___x_1222_, v___f_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1225_){
_start:
{
lean_object* v___f_1226_; 
v___f_1226_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1226_, 0, v_inst_1225_);
return v___f_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1227_, lean_object* v_cmp_1228_, lean_object* v_m_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_){
_start:
{
lean_object* v___f_1233_; 
v___f_1233_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1233_, 0, v_inst_1231_);
return v___f_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1234_, lean_object* v_cmp_1235_, lean_object* v_m_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(v_00_u03b1_1234_, v_cmp_1235_, v_m_1236_, v_inst_1237_, v_inst_1238_, v_inst_1239_);
lean_dec_ref(v_cmp_1235_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0(lean_object* v_p_1241_, lean_object* v___x_1242_, lean_object* v___x_1243_, lean_object* v_a_1244_, lean_object* v_b_1245_, lean_object* v_acc_1246_){
_start:
{
lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = lean_apply_1(v_p_1241_, v_a_1244_);
v___x_1248_ = lean_unbox(v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1242_);
return v___x_1249_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec_ref(v___x_1242_);
v___x_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1247_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v___x_1243_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0___boxed(lean_object* v_p_1253_, lean_object* v___x_1254_, lean_object* v___x_1255_, lean_object* v_a_1256_, lean_object* v_b_1257_, lean_object* v_acc_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Std_ExtTreeSet_any___redArg___lam__0(v_p_1253_, v___x_1254_, v___x_1255_, v_a_1256_, v_b_1257_, v_acc_1258_);
lean_dec_ref(v_acc_1258_);
return v_res_1259_;
}
}
uint8_t l_Std_ExtTreeSet_any___redArg(lean_object* v_t_1263_, lean_object* v_p_1264_){
_start:
{
lean_object* v___y_1266_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v_a_1276_; 
v___x_1271_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1272_ = lean_box(0);
v___x_1273_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1274_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1274_, 0, v_p_1264_);
lean_closure_set(v___f_1274_, 1, v___x_1273_);
lean_closure_set(v___f_1274_, 2, v___x_1272_);
v___x_1275_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1271_, v___f_1274_, v___x_1273_, v_t_1263_);
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___y_1266_ = v_a_1276_;
goto v___jp_1265_;
v___jp_1265_:
{
lean_object* v_fst_1267_; 
v_fst_1267_ = lean_ctor_get(v___y_1266_, 0);
lean_inc(v_fst_1267_);
lean_dec_ref(v___y_1266_);
if (lean_obj_tag(v_fst_1267_) == 0)
{
uint8_t v___x_1268_; 
v___x_1268_ = 0;
return v___x_1268_;
}
else
{
lean_object* v_val_1269_; uint8_t v___x_1270_; 
v_val_1269_ = lean_ctor_get(v_fst_1267_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v_fst_1267_, 1);
v___x_1270_ = lean_unbox(v_val_1269_);
lean_dec(v_val_1269_);
return v___x_1270_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1263_ = stack[0].m_obj;
lean_object* v_p_1264_ = stack[1].m_obj;
uint8_t v_res_1277_;
v_res_1277_ = l_Std_ExtTreeSet_any___redArg(v_t_1263_, v_p_1264_);
stack->m_num = v_res_1277_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___boxed(lean_object* v_t_1278_, lean_object* v_p_1279_){
_start:
{
uint8_t v_res_1280_; lean_object* v_r_1281_; 
v_res_1280_ = l_Std_ExtTreeSet_any___redArg(v_t_1278_, v_p_1279_);
v_r_1281_ = lean_box(v_res_1280_);
return v_r_1281_;
}
}
uint8_t l_Std_ExtTreeSet_any(lean_object* v_00_u03b1_1282_, lean_object* v_cmp_1283_, lean_object* v_inst_1284_, lean_object* v_t_1285_, lean_object* v_p_1286_){
_start:
{
lean_object* v___y_1288_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v_a_1298_; 
v___x_1293_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1294_ = lean_box(0);
v___x_1295_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1296_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1296_, 0, v_p_1286_);
lean_closure_set(v___f_1296_, 1, v___x_1295_);
lean_closure_set(v___f_1296_, 2, v___x_1294_);
v___x_1297_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1293_, v___f_1296_, v___x_1295_, v_t_1285_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___y_1288_ = v_a_1298_;
goto v___jp_1287_;
v___jp_1287_:
{
lean_object* v_fst_1289_; 
v_fst_1289_ = lean_ctor_get(v___y_1288_, 0);
lean_inc(v_fst_1289_);
lean_dec_ref(v___y_1288_);
if (lean_obj_tag(v_fst_1289_) == 0)
{
uint8_t v___x_1290_; 
v___x_1290_ = 0;
return v___x_1290_;
}
else
{
lean_object* v_val_1291_; uint8_t v___x_1292_; 
v_val_1291_ = lean_ctor_get(v_fst_1289_, 0);
lean_inc(v_val_1291_);
lean_dec_ref_known(v_fst_1289_, 1);
v___x_1292_ = lean_unbox(v_val_1291_);
lean_dec(v_val_1291_);
return v___x_1292_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1283_ = stack[1].m_obj;
lean_object* v_t_1285_ = stack[3].m_obj;
lean_object* v_p_1286_ = stack[4].m_obj;
uint8_t v_res_1299_;
v_res_1299_ = l_Std_ExtTreeSet_any(lean_box(0), v_cmp_1283_, lean_box(0), v_t_1285_, v_p_1286_);
stack->m_num = v_res_1299_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___boxed(lean_object* v_00_u03b1_1300_, lean_object* v_cmp_1301_, lean_object* v_inst_1302_, lean_object* v_t_1303_, lean_object* v_p_1304_){
_start:
{
uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_res_1305_ = l_Std_ExtTreeSet_any(v_00_u03b1_1300_, v_cmp_1301_, v_inst_1302_, v_t_1303_, v_p_1304_);
lean_dec_ref(v_cmp_1301_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0(lean_object* v_p_1307_, lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v_a_1310_, lean_object* v_b_1311_, lean_object* v_acc_1312_){
_start:
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = lean_apply_1(v_p_1307_, v_a_1310_);
v___x_1314_ = lean_unbox(v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec_ref(v___x_1309_);
v___x_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v___x_1308_);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1309_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0___boxed(lean_object* v_p_1319_, lean_object* v___x_1320_, lean_object* v___x_1321_, lean_object* v_a_1322_, lean_object* v_b_1323_, lean_object* v_acc_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_ExtTreeSet_all___redArg___lam__0(v_p_1319_, v___x_1320_, v___x_1321_, v_a_1322_, v_b_1323_, v_acc_1324_);
lean_dec_ref(v_acc_1324_);
return v_res_1325_;
}
}
uint8_t l_Std_ExtTreeSet_all___redArg(lean_object* v_t_1326_, lean_object* v_p_1327_){
_start:
{
lean_object* v___y_1329_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___f_1337_; lean_object* v___x_1338_; lean_object* v_a_1339_; 
v___x_1334_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1335_ = lean_box(0);
v___x_1336_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1337_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1337_, 0, v_p_1327_);
lean_closure_set(v___f_1337_, 1, v___x_1335_);
lean_closure_set(v___f_1337_, 2, v___x_1336_);
v___x_1338_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1334_, v___f_1337_, v___x_1336_, v_t_1326_);
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___y_1329_ = v_a_1339_;
goto v___jp_1328_;
v___jp_1328_:
{
lean_object* v_fst_1330_; 
v_fst_1330_ = lean_ctor_get(v___y_1329_, 0);
lean_inc(v_fst_1330_);
lean_dec_ref(v___y_1329_);
if (lean_obj_tag(v_fst_1330_) == 0)
{
uint8_t v___x_1331_; 
v___x_1331_ = 1;
return v___x_1331_;
}
else
{
lean_object* v_val_1332_; uint8_t v___x_1333_; 
v_val_1332_ = lean_ctor_get(v_fst_1330_, 0);
lean_inc(v_val_1332_);
lean_dec_ref_known(v_fst_1330_, 1);
v___x_1333_ = lean_unbox(v_val_1332_);
lean_dec(v_val_1332_);
return v___x_1333_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1326_ = stack[0].m_obj;
lean_object* v_p_1327_ = stack[1].m_obj;
uint8_t v_res_1340_;
v_res_1340_ = l_Std_ExtTreeSet_all___redArg(v_t_1326_, v_p_1327_);
stack->m_num = v_res_1340_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___boxed(lean_object* v_t_1341_, lean_object* v_p_1342_){
_start:
{
uint8_t v_res_1343_; lean_object* v_r_1344_; 
v_res_1343_ = l_Std_ExtTreeSet_all___redArg(v_t_1341_, v_p_1342_);
v_r_1344_ = lean_box(v_res_1343_);
return v_r_1344_;
}
}
uint8_t l_Std_ExtTreeSet_all(lean_object* v_00_u03b1_1345_, lean_object* v_cmp_1346_, lean_object* v_inst_1347_, lean_object* v_t_1348_, lean_object* v_p_1349_){
_start:
{
lean_object* v___y_1351_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___f_1359_; lean_object* v___x_1360_; lean_object* v_a_1361_; 
v___x_1356_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1357_ = lean_box(0);
v___x_1358_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1359_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1359_, 0, v_p_1349_);
lean_closure_set(v___f_1359_, 1, v___x_1357_);
lean_closure_set(v___f_1359_, 2, v___x_1358_);
v___x_1360_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1356_, v___f_1359_, v___x_1358_, v_t_1348_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___y_1351_ = v_a_1361_;
goto v___jp_1350_;
v___jp_1350_:
{
lean_object* v_fst_1352_; 
v_fst_1352_ = lean_ctor_get(v___y_1351_, 0);
lean_inc(v_fst_1352_);
lean_dec_ref(v___y_1351_);
if (lean_obj_tag(v_fst_1352_) == 0)
{
uint8_t v___x_1353_; 
v___x_1353_ = 1;
return v___x_1353_;
}
else
{
lean_object* v_val_1354_; uint8_t v___x_1355_; 
v_val_1354_ = lean_ctor_get(v_fst_1352_, 0);
lean_inc(v_val_1354_);
lean_dec_ref_known(v_fst_1352_, 1);
v___x_1355_ = lean_unbox(v_val_1354_);
lean_dec(v_val_1354_);
return v___x_1355_;
}
}
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1346_ = stack[1].m_obj;
lean_object* v_t_1348_ = stack[3].m_obj;
lean_object* v_p_1349_ = stack[4].m_obj;
uint8_t v_res_1362_;
v_res_1362_ = l_Std_ExtTreeSet_all(lean_box(0), v_cmp_1346_, lean_box(0), v_t_1348_, v_p_1349_);
stack->m_num = v_res_1362_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_cmp_1364_, lean_object* v_inst_1365_, lean_object* v_t_1366_, lean_object* v_p_1367_){
_start:
{
uint8_t v_res_1368_; lean_object* v_r_1369_; 
v_res_1368_ = l_Std_ExtTreeSet_all(v_00_u03b1_1363_, v_cmp_1364_, v_inst_1365_, v_t_1366_, v_p_1367_);
lean_dec_ref(v_cmp_1364_);
v_r_1369_ = lean_box(v_res_1368_);
return v_r_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg___lam__0(lean_object* v_x1_1370_, lean_object* v_x2_1371_, lean_object* v_x3_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_x1_1370_);
lean_ctor_set(v___x_1373_, 1, v_x3_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg(lean_object* v_t_1375_){
_start:
{
lean_object* v___f_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___f_1376_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___x_1377_ = lean_box(0);
v___x_1378_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1378_, v___f_1376_, v___x_1377_, v_t_1375_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList(lean_object* v_00_u03b1_1380_, lean_object* v_cmp_1381_, lean_object* v_inst_1382_, lean_object* v_t_1383_){
_start:
{
lean_object* v___f_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___f_1384_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___x_1385_ = lean_box(0);
v___x_1386_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1387_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1386_, v___f_1384_, v___x_1385_, v_t_1383_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___boxed(lean_object* v_00_u03b1_1388_, lean_object* v_cmp_1389_, lean_object* v_inst_1390_, lean_object* v_t_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Std_ExtTreeSet_toList(v_00_u03b1_1388_, v_cmp_1389_, v_inst_1390_, v_t_1391_);
lean_dec_ref(v_cmp_1389_);
return v_res_1392_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_ofList___auto__1(void){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__25, &l_Std_ExtTreeSet___auto__1___closed__25_once, _init_l_Std_ExtTreeSet___auto__1___closed__25);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(lean_object* v_cmp_1394_, lean_object* v_k_1395_, lean_object* v_v_1396_, lean_object* v_t_1397_){
_start:
{
if (lean_obj_tag(v_t_1397_) == 0)
{
lean_object* v_size_1398_; lean_object* v_k_1399_; lean_object* v_v_1400_; lean_object* v_l_1401_; lean_object* v_r_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1683_; 
v_size_1398_ = lean_ctor_get(v_t_1397_, 0);
v_k_1399_ = lean_ctor_get(v_t_1397_, 1);
v_v_1400_ = lean_ctor_get(v_t_1397_, 2);
v_l_1401_ = lean_ctor_get(v_t_1397_, 3);
v_r_1402_ = lean_ctor_get(v_t_1397_, 4);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_t_1397_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1404_ = v_t_1397_;
v_isShared_1405_ = v_isSharedCheck_1683_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_r_1402_);
lean_inc(v_l_1401_);
lean_inc(v_v_1400_);
lean_inc(v_k_1399_);
lean_inc(v_size_1398_);
lean_dec(v_t_1397_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1683_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; uint8_t v___x_1407_; 
lean_inc_ref(v_cmp_1394_);
lean_inc(v_k_1399_);
lean_inc(v_k_1395_);
v___x_1406_ = lean_apply_2(v_cmp_1394_, v_k_1395_, v_k_1399_);
v___x_1407_ = lean_unbox(v___x_1406_);
switch(v___x_1407_)
{
case 0:
{
lean_object* v_impl_1408_; lean_object* v___x_1409_; 
lean_dec(v_size_1398_);
v_impl_1408_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1394_, v_k_1395_, v_v_1396_, v_l_1401_);
v___x_1409_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1402_) == 0)
{
lean_object* v_size_1410_; lean_object* v_size_1411_; lean_object* v_k_1412_; lean_object* v_v_1413_; lean_object* v_l_1414_; lean_object* v_r_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_size_1410_ = lean_ctor_get(v_r_1402_, 0);
v_size_1411_ = lean_ctor_get(v_impl_1408_, 0);
v_k_1412_ = lean_ctor_get(v_impl_1408_, 1);
v_v_1413_ = lean_ctor_get(v_impl_1408_, 2);
v_l_1414_ = lean_ctor_get(v_impl_1408_, 3);
v_r_1415_ = lean_ctor_get(v_impl_1408_, 4);
lean_inc(v_r_1415_);
v___x_1416_ = lean_unsigned_to_nat(3u);
v___x_1417_ = lean_nat_mul(v___x_1416_, v_size_1410_);
v___x_1418_ = lean_nat_dec_lt(v___x_1417_, v_size_1411_);
lean_dec(v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
lean_dec(v_r_1415_);
v___x_1419_ = lean_nat_add(v___x_1409_, v_size_1411_);
v___x_1420_ = lean_nat_add(v___x_1419_, v_size_1410_);
lean_dec(v___x_1419_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 3, v_impl_1408_);
lean_ctor_set(v___x_1404_, 0, v___x_1420_);
v___x_1422_ = v___x_1404_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_impl_1408_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_r_1402_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
else
{
lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1489_; 
lean_inc(v_l_1414_);
lean_inc(v_v_1413_);
lean_inc(v_k_1412_);
lean_inc(v_size_1411_);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_impl_1408_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; lean_object* v_unused_1494_; 
v_unused_1490_ = lean_ctor_get(v_impl_1408_, 4);
lean_dec(v_unused_1490_);
v_unused_1491_ = lean_ctor_get(v_impl_1408_, 3);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_impl_1408_, 2);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_impl_1408_, 1);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_impl_1408_, 0);
lean_dec(v_unused_1494_);
v___x_1425_ = v_impl_1408_;
v_isShared_1426_ = v_isSharedCheck_1489_;
goto v_resetjp_1424_;
}
else
{
lean_dec(v_impl_1408_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1489_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v_size_1427_; lean_object* v_size_1428_; lean_object* v_k_1429_; lean_object* v_v_1430_; lean_object* v_l_1431_; lean_object* v_r_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_size_1427_ = lean_ctor_get(v_l_1414_, 0);
v_size_1428_ = lean_ctor_get(v_r_1415_, 0);
v_k_1429_ = lean_ctor_get(v_r_1415_, 1);
v_v_1430_ = lean_ctor_get(v_r_1415_, 2);
v_l_1431_ = lean_ctor_get(v_r_1415_, 3);
v_r_1432_ = lean_ctor_get(v_r_1415_, 4);
v___x_1433_ = lean_unsigned_to_nat(2u);
v___x_1434_ = lean_nat_mul(v___x_1433_, v_size_1427_);
v___x_1435_ = lean_nat_dec_lt(v_size_1428_, v___x_1434_);
lean_dec(v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1464_; 
lean_inc(v_r_1432_);
lean_inc(v_l_1431_);
lean_inc(v_v_1430_);
lean_inc(v_k_1429_);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_r_1415_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; 
v_unused_1465_ = lean_ctor_get(v_r_1415_, 4);
lean_dec(v_unused_1465_);
v_unused_1466_ = lean_ctor_get(v_r_1415_, 3);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_r_1415_, 2);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_r_1415_, 1);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_r_1415_, 0);
lean_dec(v_unused_1469_);
v___x_1437_ = v_r_1415_;
v_isShared_1438_ = v_isSharedCheck_1464_;
goto v_resetjp_1436_;
}
else
{
lean_dec(v_r_1415_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1464_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___x_1452_; lean_object* v___y_1454_; 
v___x_1439_ = lean_nat_add(v___x_1409_, v_size_1411_);
lean_dec(v_size_1411_);
v___x_1440_ = lean_nat_add(v___x_1439_, v_size_1410_);
lean_dec(v___x_1439_);
v___x_1452_ = lean_nat_add(v___x_1409_, v_size_1427_);
if (lean_obj_tag(v_l_1431_) == 0)
{
lean_object* v_size_1462_; 
v_size_1462_ = lean_ctor_get(v_l_1431_, 0);
lean_inc(v_size_1462_);
v___y_1454_ = v_size_1462_;
goto v___jp_1453_;
}
else
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_unsigned_to_nat(0u);
v___y_1454_ = v___x_1463_;
goto v___jp_1453_;
}
v___jp_1441_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = lean_nat_add(v___y_1442_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec(v___y_1442_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 4, v_r_1402_);
lean_ctor_set(v___x_1437_, 3, v_r_1432_);
lean_ctor_set(v___x_1437_, 2, v_v_1400_);
lean_ctor_set(v___x_1437_, 1, v_k_1399_);
lean_ctor_set(v___x_1437_, 0, v___x_1445_);
v___x_1447_ = v___x_1437_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v_r_1432_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v_r_1402_);
v___x_1447_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1449_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 4, v___x_1447_);
lean_ctor_set(v___x_1425_, 3, v___y_1443_);
lean_ctor_set(v___x_1425_, 2, v_v_1430_);
lean_ctor_set(v___x_1425_, 1, v_k_1429_);
lean_ctor_set(v___x_1425_, 0, v___x_1440_);
v___x_1449_ = v___x_1425_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_k_1429_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_v_1430_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v___y_1443_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
v___jp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_nat_add(v___x_1452_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec(v___x_1452_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_l_1431_);
lean_ctor_set(v___x_1404_, 3, v_l_1414_);
lean_ctor_set(v___x_1404_, 2, v_v_1413_);
lean_ctor_set(v___x_1404_, 1, v_k_1412_);
lean_ctor_set(v___x_1404_, 0, v___x_1455_);
v___x_1457_ = v___x_1404_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1412_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1413_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_l_1414_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_l_1431_);
v___x_1457_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_nat_add(v___x_1409_, v_size_1410_);
if (lean_obj_tag(v_r_1432_) == 0)
{
lean_object* v_size_1459_; 
v_size_1459_ = lean_ctor_get(v_r_1432_, 0);
lean_inc(v_size_1459_);
v___y_1442_ = v___x_1458_;
v___y_1443_ = v___x_1457_;
v___y_1444_ = v_size_1459_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_unsigned_to_nat(0u);
v___y_1442_ = v___x_1458_;
v___y_1443_ = v___x_1457_;
v___y_1444_ = v___x_1460_;
goto v___jp_1441_;
}
}
}
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; 
lean_del_object(v___x_1404_);
v___x_1470_ = lean_nat_add(v___x_1409_, v_size_1411_);
lean_dec(v_size_1411_);
v___x_1471_ = lean_nat_add(v___x_1470_, v_size_1410_);
lean_dec(v___x_1470_);
v___x_1472_ = lean_nat_add(v___x_1409_, v_size_1410_);
v___x_1473_ = lean_nat_add(v___x_1472_, v_size_1428_);
lean_dec(v___x_1472_);
lean_inc_ref(v_r_1402_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 4, v_r_1402_);
lean_ctor_set(v___x_1425_, 3, v_r_1415_);
lean_ctor_set(v___x_1425_, 2, v_v_1400_);
lean_ctor_set(v___x_1425_, 1, v_k_1399_);
lean_ctor_set(v___x_1425_, 0, v___x_1473_);
v___x_1475_ = v___x_1425_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v_r_1415_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v_r_1402_);
v___x_1475_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
v_isSharedCheck_1482_ = !lean_is_exclusive(v_r_1402_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; lean_object* v_unused_1487_; 
v_unused_1483_ = lean_ctor_get(v_r_1402_, 4);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_r_1402_, 3);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_r_1402_, 2);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_r_1402_, 1);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_r_1402_, 0);
lean_dec(v_unused_1487_);
v___x_1477_ = v_r_1402_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_dec(v_r_1402_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 4, v___x_1475_);
lean_ctor_set(v___x_1477_, 3, v_l_1414_);
lean_ctor_set(v___x_1477_, 2, v_v_1413_);
lean_ctor_set(v___x_1477_, 1, v_k_1412_);
lean_ctor_set(v___x_1477_, 0, v___x_1471_);
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1412_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1413_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_l_1414_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v___x_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1495_; 
v_l_1495_ = lean_ctor_get(v_impl_1408_, 3);
if (lean_obj_tag(v_l_1495_) == 0)
{
lean_object* v_r_1496_; lean_object* v_k_1497_; lean_object* v_v_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1509_; 
lean_inc_ref(v_l_1495_);
v_r_1496_ = lean_ctor_get(v_impl_1408_, 4);
v_k_1497_ = lean_ctor_get(v_impl_1408_, 1);
v_v_1498_ = lean_ctor_get(v_impl_1408_, 2);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_impl_1408_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; lean_object* v_unused_1511_; 
v_unused_1510_ = lean_ctor_get(v_impl_1408_, 3);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_impl_1408_, 0);
lean_dec(v_unused_1511_);
v___x_1500_ = v_impl_1408_;
v_isShared_1501_ = v_isSharedCheck_1509_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_r_1496_);
lean_inc(v_v_1498_);
lean_inc(v_k_1497_);
lean_dec(v_impl_1408_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1509_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1502_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1496_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 3, v_r_1496_);
lean_ctor_set(v___x_1500_, 2, v_v_1400_);
lean_ctor_set(v___x_1500_, 1, v_k_1399_);
lean_ctor_set(v___x_1500_, 0, v___x_1409_);
v___x_1504_ = v___x_1500_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_r_1496_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_r_1496_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v___x_1504_);
lean_ctor_set(v___x_1404_, 3, v_l_1495_);
lean_ctor_set(v___x_1404_, 2, v_v_1498_);
lean_ctor_set(v___x_1404_, 1, v_k_1497_);
lean_ctor_set(v___x_1404_, 0, v___x_1502_);
v___x_1506_ = v___x_1404_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_k_1497_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_v_1498_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_l_1495_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_r_1512_; 
v_r_1512_ = lean_ctor_get(v_impl_1408_, 4);
lean_inc(v_r_1512_);
if (lean_obj_tag(v_r_1512_) == 0)
{
lean_object* v_k_1513_; lean_object* v_v_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1537_; 
lean_inc(v_l_1495_);
v_k_1513_ = lean_ctor_get(v_impl_1408_, 1);
v_v_1514_ = lean_ctor_get(v_impl_1408_, 2);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_impl_1408_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; 
v_unused_1538_ = lean_ctor_get(v_impl_1408_, 4);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_impl_1408_, 3);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_impl_1408_, 0);
lean_dec(v_unused_1540_);
v___x_1516_ = v_impl_1408_;
v_isShared_1517_ = v_isSharedCheck_1537_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_v_1514_);
lean_inc(v_k_1513_);
lean_dec(v_impl_1408_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1537_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v_k_1518_; lean_object* v_v_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1533_; 
v_k_1518_ = lean_ctor_get(v_r_1512_, 1);
v_v_1519_ = lean_ctor_get(v_r_1512_, 2);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_r_1512_);
if (v_isSharedCheck_1533_ == 0)
{
lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; 
v_unused_1534_ = lean_ctor_get(v_r_1512_, 4);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_r_1512_, 3);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_r_1512_, 0);
lean_dec(v_unused_1536_);
v___x_1521_ = v_r_1512_;
v_isShared_1522_ = v_isSharedCheck_1533_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_v_1519_);
lean_inc(v_k_1518_);
lean_dec(v_r_1512_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1533_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_unsigned_to_nat(3u);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v_l_1495_);
lean_ctor_set(v___x_1521_, 3, v_l_1495_);
lean_ctor_set(v___x_1521_, 2, v_v_1514_);
lean_ctor_set(v___x_1521_, 1, v_k_1513_);
lean_ctor_set(v___x_1521_, 0, v___x_1409_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_k_1513_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_v_1514_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_l_1495_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v_l_1495_);
v___x_1525_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 4, v_l_1495_);
lean_ctor_set(v___x_1516_, 2, v_v_1400_);
lean_ctor_set(v___x_1516_, 1, v_k_1399_);
lean_ctor_set(v___x_1516_, 0, v___x_1409_);
v___x_1527_ = v___x_1516_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_l_1495_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_l_1495_);
v___x_1527_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1529_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v___x_1527_);
lean_ctor_set(v___x_1404_, 3, v___x_1525_);
lean_ctor_set(v___x_1404_, 2, v_v_1519_);
lean_ctor_set(v___x_1404_, 1, v_k_1518_);
lean_ctor_set(v___x_1404_, 0, v___x_1523_);
v___x_1529_ = v___x_1404_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1518_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1519_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = lean_unsigned_to_nat(2u);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_r_1512_);
lean_ctor_set(v___x_1404_, 3, v_impl_1408_);
lean_ctor_set(v___x_1404_, 0, v___x_1541_);
v___x_1543_ = v___x_1404_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_impl_1408_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_r_1512_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1546_; 
lean_dec(v_v_1400_);
lean_dec(v_k_1399_);
lean_dec_ref(v_cmp_1394_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 2, v_v_1396_);
lean_ctor_set(v___x_1404_, 1, v_k_1395_);
v___x_1546_ = v___x_1404_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_size_1398_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_k_1395_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_v_1396_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_l_1401_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_r_1402_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
default: 
{
lean_object* v_impl_1548_; lean_object* v___x_1549_; 
lean_dec(v_size_1398_);
v_impl_1548_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1394_, v_k_1395_, v_v_1396_, v_r_1402_);
v___x_1549_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1401_) == 0)
{
lean_object* v_size_1550_; lean_object* v_size_1551_; lean_object* v_k_1552_; lean_object* v_v_1553_; lean_object* v_l_1554_; lean_object* v_r_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_size_1550_ = lean_ctor_get(v_l_1401_, 0);
v_size_1551_ = lean_ctor_get(v_impl_1548_, 0);
v_k_1552_ = lean_ctor_get(v_impl_1548_, 1);
v_v_1553_ = lean_ctor_get(v_impl_1548_, 2);
v_l_1554_ = lean_ctor_get(v_impl_1548_, 3);
lean_inc(v_l_1554_);
v_r_1555_ = lean_ctor_get(v_impl_1548_, 4);
v___x_1556_ = lean_unsigned_to_nat(3u);
v___x_1557_ = lean_nat_mul(v___x_1556_, v_size_1550_);
v___x_1558_ = lean_nat_dec_lt(v___x_1557_, v_size_1551_);
lean_dec(v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
lean_dec(v_l_1554_);
v___x_1559_ = lean_nat_add(v___x_1549_, v_size_1550_);
v___x_1560_ = lean_nat_add(v___x_1559_, v_size_1551_);
lean_dec(v___x_1559_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_impl_1548_);
lean_ctor_set(v___x_1404_, 0, v___x_1560_);
v___x_1562_ = v___x_1404_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v_l_1401_);
lean_ctor_set(v_reuseFailAlloc_1563_, 4, v_impl_1548_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
else
{
lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1627_; 
lean_inc(v_r_1555_);
lean_inc(v_v_1553_);
lean_inc(v_k_1552_);
lean_inc(v_size_1551_);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_impl_1548_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; lean_object* v_unused_1629_; lean_object* v_unused_1630_; lean_object* v_unused_1631_; lean_object* v_unused_1632_; 
v_unused_1628_ = lean_ctor_get(v_impl_1548_, 4);
lean_dec(v_unused_1628_);
v_unused_1629_ = lean_ctor_get(v_impl_1548_, 3);
lean_dec(v_unused_1629_);
v_unused_1630_ = lean_ctor_get(v_impl_1548_, 2);
lean_dec(v_unused_1630_);
v_unused_1631_ = lean_ctor_get(v_impl_1548_, 1);
lean_dec(v_unused_1631_);
v_unused_1632_ = lean_ctor_get(v_impl_1548_, 0);
lean_dec(v_unused_1632_);
v___x_1565_ = v_impl_1548_;
v_isShared_1566_ = v_isSharedCheck_1627_;
goto v_resetjp_1564_;
}
else
{
lean_dec(v_impl_1548_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1627_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v_size_1567_; lean_object* v_k_1568_; lean_object* v_v_1569_; lean_object* v_l_1570_; lean_object* v_r_1571_; lean_object* v_size_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_size_1567_ = lean_ctor_get(v_l_1554_, 0);
v_k_1568_ = lean_ctor_get(v_l_1554_, 1);
v_v_1569_ = lean_ctor_get(v_l_1554_, 2);
v_l_1570_ = lean_ctor_get(v_l_1554_, 3);
v_r_1571_ = lean_ctor_get(v_l_1554_, 4);
v_size_1572_ = lean_ctor_get(v_r_1555_, 0);
v___x_1573_ = lean_unsigned_to_nat(2u);
v___x_1574_ = lean_nat_mul(v___x_1573_, v_size_1572_);
v___x_1575_ = lean_nat_dec_lt(v_size_1567_, v___x_1574_);
lean_dec(v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1603_; 
lean_inc(v_r_1571_);
lean_inc(v_l_1570_);
lean_inc(v_v_1569_);
lean_inc(v_k_1568_);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_l_1554_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; 
v_unused_1604_ = lean_ctor_get(v_l_1554_, 4);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_l_1554_, 3);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_l_1554_, 2);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_l_1554_, 1);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_l_1554_, 0);
lean_dec(v_unused_1608_);
v___x_1577_ = v_l_1554_;
v_isShared_1578_ = v_isSharedCheck_1603_;
goto v_resetjp_1576_;
}
else
{
lean_dec(v_l_1554_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1603_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1593_; 
v___x_1579_ = lean_nat_add(v___x_1549_, v_size_1550_);
v___x_1580_ = lean_nat_add(v___x_1579_, v_size_1551_);
lean_dec(v_size_1551_);
if (lean_obj_tag(v_l_1570_) == 0)
{
lean_object* v_size_1601_; 
v_size_1601_ = lean_ctor_get(v_l_1570_, 0);
lean_inc(v_size_1601_);
v___y_1593_ = v_size_1601_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_unsigned_to_nat(0u);
v___y_1593_ = v___x_1602_;
goto v___jp_1592_;
}
v___jp_1581_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1585_ = lean_nat_add(v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec(v___y_1583_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 4, v_r_1555_);
lean_ctor_set(v___x_1577_, 3, v_r_1571_);
lean_ctor_set(v___x_1577_, 2, v_v_1553_);
lean_ctor_set(v___x_1577_, 1, v_k_1552_);
lean_ctor_set(v___x_1577_, 0, v___x_1585_);
v___x_1587_ = v___x_1577_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_k_1552_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_v_1553_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_r_1571_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_r_1555_);
v___x_1587_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1589_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 4, v___x_1587_);
lean_ctor_set(v___x_1565_, 3, v___y_1582_);
lean_ctor_set(v___x_1565_, 2, v_v_1569_);
lean_ctor_set(v___x_1565_, 1, v_k_1568_);
lean_ctor_set(v___x_1565_, 0, v___x_1580_);
v___x_1589_ = v___x_1565_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_k_1568_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_v_1569_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v___y_1582_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
v___jp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1594_ = lean_nat_add(v___x_1579_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec(v___x_1579_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_l_1570_);
lean_ctor_set(v___x_1404_, 0, v___x_1594_);
v___x_1596_ = v___x_1404_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_l_1401_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_l_1570_);
v___x_1596_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_nat_add(v___x_1549_, v_size_1572_);
if (lean_obj_tag(v_r_1571_) == 0)
{
lean_object* v_size_1598_; 
v_size_1598_ = lean_ctor_get(v_r_1571_, 0);
lean_inc(v_size_1598_);
v___y_1582_ = v___x_1596_;
v___y_1583_ = v___x_1597_;
v___y_1584_ = v_size_1598_;
goto v___jp_1581_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_unsigned_to_nat(0u);
v___y_1582_ = v___x_1596_;
v___y_1583_ = v___x_1597_;
v___y_1584_ = v___x_1599_;
goto v___jp_1581_;
}
}
}
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
lean_del_object(v___x_1404_);
v___x_1609_ = lean_nat_add(v___x_1549_, v_size_1550_);
v___x_1610_ = lean_nat_add(v___x_1609_, v_size_1551_);
lean_dec(v_size_1551_);
v___x_1611_ = lean_nat_add(v___x_1609_, v_size_1567_);
lean_dec(v___x_1609_);
lean_inc_ref(v_l_1401_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 4, v_l_1554_);
lean_ctor_set(v___x_1565_, 3, v_l_1401_);
lean_ctor_set(v___x_1565_, 2, v_v_1400_);
lean_ctor_set(v___x_1565_, 1, v_k_1399_);
lean_ctor_set(v___x_1565_, 0, v___x_1611_);
v___x_1613_ = v___x_1565_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1626_, 3, v_l_1401_);
lean_ctor_set(v_reuseFailAlloc_1626_, 4, v_l_1554_);
v___x_1613_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_isSharedCheck_1620_ = !lean_is_exclusive(v_l_1401_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; lean_object* v_unused_1622_; lean_object* v_unused_1623_; lean_object* v_unused_1624_; lean_object* v_unused_1625_; 
v_unused_1621_ = lean_ctor_get(v_l_1401_, 4);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_l_1401_, 3);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_l_1401_, 2);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_l_1401_, 1);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_l_1401_, 0);
lean_dec(v_unused_1625_);
v___x_1615_ = v_l_1401_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_dec(v_l_1401_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 4, v_r_1555_);
lean_ctor_set(v___x_1615_, 3, v___x_1613_);
lean_ctor_set(v___x_1615_, 2, v_v_1553_);
lean_ctor_set(v___x_1615_, 1, v_k_1552_);
lean_ctor_set(v___x_1615_, 0, v___x_1610_);
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_k_1552_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_v_1553_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_r_1555_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1633_; 
v_l_1633_ = lean_ctor_get(v_impl_1548_, 3);
lean_inc(v_l_1633_);
if (lean_obj_tag(v_l_1633_) == 0)
{
lean_object* v_r_1634_; lean_object* v_k_1635_; lean_object* v_v_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1659_; 
v_r_1634_ = lean_ctor_get(v_impl_1548_, 4);
v_k_1635_ = lean_ctor_get(v_impl_1548_, 1);
v_v_1636_ = lean_ctor_get(v_impl_1548_, 2);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_impl_1548_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; lean_object* v_unused_1661_; 
v_unused_1660_ = lean_ctor_get(v_impl_1548_, 3);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v_impl_1548_, 0);
lean_dec(v_unused_1661_);
v___x_1638_ = v_impl_1548_;
v_isShared_1639_ = v_isSharedCheck_1659_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_r_1634_);
lean_inc(v_v_1636_);
lean_inc(v_k_1635_);
lean_dec(v_impl_1548_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1659_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v_k_1640_; lean_object* v_v_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1655_; 
v_k_1640_ = lean_ctor_get(v_l_1633_, 1);
v_v_1641_ = lean_ctor_get(v_l_1633_, 2);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_l_1633_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; lean_object* v_unused_1657_; lean_object* v_unused_1658_; 
v_unused_1656_ = lean_ctor_get(v_l_1633_, 4);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_l_1633_, 3);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_l_1633_, 0);
lean_dec(v_unused_1658_);
v___x_1643_ = v_l_1633_;
v_isShared_1644_ = v_isSharedCheck_1655_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_v_1641_);
lean_inc(v_k_1640_);
lean_dec(v_l_1633_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1655_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1634_, 2);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 4, v_r_1634_);
lean_ctor_set(v___x_1643_, 3, v_r_1634_);
lean_ctor_set(v___x_1643_, 2, v_v_1400_);
lean_ctor_set(v___x_1643_, 1, v_k_1399_);
lean_ctor_set(v___x_1643_, 0, v___x_1549_);
v___x_1647_ = v___x_1643_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v_r_1634_);
lean_ctor_set(v_reuseFailAlloc_1654_, 4, v_r_1634_);
v___x_1647_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
lean_inc(v_r_1634_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 3, v_r_1634_);
lean_ctor_set(v___x_1638_, 0, v___x_1549_);
v___x_1649_ = v___x_1638_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_k_1635_);
lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_v_1636_);
lean_ctor_set(v_reuseFailAlloc_1653_, 3, v_r_1634_);
lean_ctor_set(v_reuseFailAlloc_1653_, 4, v_r_1634_);
v___x_1649_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v___x_1649_);
lean_ctor_set(v___x_1404_, 3, v___x_1647_);
lean_ctor_set(v___x_1404_, 2, v_v_1641_);
lean_ctor_set(v___x_1404_, 1, v_k_1640_);
lean_ctor_set(v___x_1404_, 0, v___x_1645_);
v___x_1651_ = v___x_1404_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_k_1640_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_v_1641_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
}
else
{
lean_object* v_r_1662_; 
v_r_1662_ = lean_ctor_get(v_impl_1548_, 4);
lean_inc(v_r_1662_);
if (lean_obj_tag(v_r_1662_) == 0)
{
lean_object* v_k_1663_; lean_object* v_v_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1675_; 
v_k_1663_ = lean_ctor_get(v_impl_1548_, 1);
v_v_1664_ = lean_ctor_get(v_impl_1548_, 2);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_impl_1548_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; lean_object* v_unused_1677_; lean_object* v_unused_1678_; 
v_unused_1676_ = lean_ctor_get(v_impl_1548_, 4);
lean_dec(v_unused_1676_);
v_unused_1677_ = lean_ctor_get(v_impl_1548_, 3);
lean_dec(v_unused_1677_);
v_unused_1678_ = lean_ctor_get(v_impl_1548_, 0);
lean_dec(v_unused_1678_);
v___x_1666_ = v_impl_1548_;
v_isShared_1667_ = v_isSharedCheck_1675_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_v_1664_);
lean_inc(v_k_1663_);
lean_dec(v_impl_1548_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1675_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = lean_unsigned_to_nat(3u);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 4, v_l_1633_);
lean_ctor_set(v___x_1666_, 2, v_v_1400_);
lean_ctor_set(v___x_1666_, 1, v_k_1399_);
lean_ctor_set(v___x_1666_, 0, v___x_1549_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_l_1633_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v_l_1633_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_r_1662_);
lean_ctor_set(v___x_1404_, 3, v___x_1670_);
lean_ctor_set(v___x_1404_, 2, v_v_1664_);
lean_ctor_set(v___x_1404_, 1, v_k_1663_);
lean_ctor_set(v___x_1404_, 0, v___x_1668_);
v___x_1672_ = v___x_1404_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_k_1663_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_v_1664_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v_r_1662_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_unsigned_to_nat(2u);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_impl_1548_);
lean_ctor_set(v___x_1404_, 3, v_r_1662_);
lean_ctor_set(v___x_1404_, 0, v___x_1679_);
v___x_1681_ = v___x_1404_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v_r_1662_);
lean_ctor_set(v_reuseFailAlloc_1682_, 4, v_impl_1548_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
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
lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec_ref(v_cmp_1394_);
v___x_1684_ = lean_unsigned_to_nat(1u);
v___x_1685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v_k_1395_);
lean_ctor_set(v___x_1685_, 2, v_v_1396_);
lean_ctor_set(v___x_1685_, 3, v_t_1397_);
lean_ctor_set(v___x_1685_, 4, v_t_1397_);
return v___x_1685_;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(lean_object* v_cmp_1686_, lean_object* v_k_1687_, lean_object* v_t_1688_){
_start:
{
if (lean_obj_tag(v_t_1688_) == 0)
{
lean_object* v_k_1689_; lean_object* v_l_1690_; lean_object* v_r_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v_k_1689_ = lean_ctor_get(v_t_1688_, 1);
lean_inc(v_k_1689_);
v_l_1690_ = lean_ctor_get(v_t_1688_, 3);
lean_inc(v_l_1690_);
v_r_1691_ = lean_ctor_get(v_t_1688_, 4);
lean_inc(v_r_1691_);
lean_dec_ref_known(v_t_1688_, 5);
lean_inc_ref(v_cmp_1686_);
lean_inc(v_k_1687_);
v___x_1692_ = lean_apply_2(v_cmp_1686_, v_k_1687_, v_k_1689_);
v___x_1693_ = lean_unbox(v___x_1692_);
switch(v___x_1693_)
{
case 0:
{
lean_dec(v_r_1691_);
v_t_1688_ = v_l_1690_;
goto _start;
}
case 1:
{
uint8_t v___x_1695_; 
lean_dec(v_r_1691_);
lean_dec(v_l_1690_);
lean_dec(v_k_1687_);
lean_dec_ref(v_cmp_1686_);
v___x_1695_ = 1;
return v___x_1695_;
}
default: 
{
lean_dec(v_l_1690_);
v_t_1688_ = v_r_1691_;
goto _start;
}
}
}
else
{
uint8_t v___x_1697_; 
lean_dec(v_k_1687_);
lean_dec_ref(v_cmp_1686_);
v___x_1697_ = 0;
return v___x_1697_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1686_ = stack[0].m_obj;
lean_object* v_k_1687_ = stack[1].m_obj;
lean_object* v_t_1688_ = stack[2].m_obj;
uint8_t v_res_1698_;
v_res_1698_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1686_, v_k_1687_, v_t_1688_);
stack->m_num = v_res_1698_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg___boxed(lean_object* v_cmp_1699_, lean_object* v_k_1700_, lean_object* v_t_1701_){
_start:
{
uint8_t v_res_1702_; lean_object* v_r_1703_; 
v_res_1702_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1699_, v_k_1700_, v_t_1701_);
v_r_1703_ = lean_box(v_res_1702_);
return v_r_1703_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(lean_object* v_cmp_1704_, lean_object* v_as_x27_1705_, lean_object* v_b_1706_){
_start:
{
if (lean_obj_tag(v_as_x27_1705_) == 0)
{
lean_dec_ref(v_cmp_1704_);
return v_b_1706_;
}
else
{
lean_object* v_head_1707_; lean_object* v_tail_1708_; uint8_t v___x_1709_; 
v_head_1707_ = lean_ctor_get(v_as_x27_1705_, 0);
v_tail_1708_ = lean_ctor_get(v_as_x27_1705_, 1);
lean_inc(v_b_1706_);
lean_inc(v_head_1707_);
lean_inc_ref(v_cmp_1704_);
v___x_1709_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1704_, v_head_1707_, v_b_1706_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_box(0);
lean_inc(v_head_1707_);
lean_inc_ref(v_cmp_1704_);
v___x_1711_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1704_, v_head_1707_, v___x_1710_, v_b_1706_);
v_as_x27_1705_ = v_tail_1708_;
v_b_1706_ = v___x_1711_;
goto _start;
}
else
{
v_as_x27_1705_ = v_tail_1708_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg___boxed(lean_object* v_cmp_1714_, lean_object* v_as_x27_1715_, lean_object* v_b_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1714_, v_as_x27_1715_, v_b_1716_);
lean_dec(v_as_x27_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___redArg(lean_object* v_l_1718_, lean_object* v_cmp_1719_){
_start:
{
lean_object* v_r_1720_; lean_object* v___x_1721_; 
v_r_1720_ = lean_box(1);
v___x_1721_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1719_, v_l_1718_, v_r_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___redArg___boxed(lean_object* v_l_1722_, lean_object* v_cmp_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_ExtTreeSet_ofList___redArg(v_l_1722_, v_cmp_1723_);
lean_dec(v_l_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList(lean_object* v_00_u03b1_1725_, lean_object* v_l_1726_, lean_object* v_cmp_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_ExtTreeSet_ofList___redArg(v_l_1726_, v_cmp_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_l_1730_, lean_object* v_cmp_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Std_ExtTreeSet_ofList(v_00_u03b1_1729_, v_l_1730_, v_cmp_1731_);
lean_dec(v_l_1730_);
return v_res_1732_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(lean_object* v_00_u03b1_1733_, lean_object* v_cmp_1734_, lean_object* v_00_u03b2_1735_, lean_object* v_k_1736_, lean_object* v_t_1737_){
_start:
{
uint8_t v___x_1738_; 
v___x_1738_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1734_, v_k_1736_, v_t_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1734_ = stack[1].m_obj;
lean_object* v_k_1736_ = stack[3].m_obj;
lean_object* v_t_1737_ = stack[4].m_obj;
uint8_t v_res_1739_;
v_res_1739_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(lean_box(0), v_cmp_1734_, lean_box(0), v_k_1736_, v_t_1737_);
stack->m_num = v_res_1739_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___boxed(lean_object* v_00_u03b1_1740_, lean_object* v_cmp_1741_, lean_object* v_00_u03b2_1742_, lean_object* v_k_1743_, lean_object* v_t_1744_){
_start:
{
uint8_t v_res_1745_; lean_object* v_r_1746_; 
v_res_1745_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(v_00_u03b1_1740_, v_cmp_1741_, v_00_u03b2_1742_, v_k_1743_, v_t_1744_);
v_r_1746_ = lean_box(v_res_1745_);
return v_r_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1(lean_object* v_00_u03b1_1747_, lean_object* v_cmp_1748_, lean_object* v_00_u03b2_1749_, lean_object* v_k_1750_, lean_object* v_v_1751_, lean_object* v_t_1752_, lean_object* v_hl_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1748_, v_k_1750_, v_v_1751_, v_t_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(lean_object* v_00_u03b1_1755_, lean_object* v_cmp_1756_, lean_object* v_as_1757_, lean_object* v_as_x27_1758_, lean_object* v_b_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1756_, v_as_x27_1758_, v_b_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___boxed(lean_object* v_00_u03b1_1762_, lean_object* v_cmp_1763_, lean_object* v_as_1764_, lean_object* v_as_x27_1765_, lean_object* v_b_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(v_00_u03b1_1762_, v_cmp_1763_, v_as_1764_, v_as_x27_1765_, v_b_1766_, v_a_1767_);
lean_dec(v_as_x27_1765_);
lean_dec(v_as_1764_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg___lam__0(lean_object* v_l_1769_, lean_object* v_k_1770_, lean_object* v_x_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_array_push(v_l_1769_, v_k_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg(lean_object* v_t_1774_){
_start:
{
lean_object* v___f_1775_; lean_object* v___y_1777_; 
v___f_1775_ = ((lean_object*)(l_Std_ExtTreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1774_) == 0)
{
lean_object* v_size_1780_; 
v_size_1780_ = lean_ctor_get(v_t_1774_, 0);
lean_inc(v_size_1780_);
v___y_1777_ = v_size_1780_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_unsigned_to_nat(0u);
v___y_1777_ = v___x_1781_;
goto v___jp_1776_;
}
v___jp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_mk_empty_array_with_capacity(v___y_1777_);
lean_dec(v___y_1777_);
v___x_1779_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1775_, v___x_1778_, v_t_1774_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray(lean_object* v_00_u03b1_1782_, lean_object* v_cmp_1783_, lean_object* v_inst_1784_, lean_object* v_t_1785_){
_start:
{
lean_object* v___f_1786_; lean_object* v___y_1788_; 
v___f_1786_ = ((lean_object*)(l_Std_ExtTreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1785_) == 0)
{
lean_object* v_size_1791_; 
v_size_1791_ = lean_ctor_get(v_t_1785_, 0);
lean_inc(v_size_1791_);
v___y_1788_ = v_size_1791_;
goto v___jp_1787_;
}
else
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_unsigned_to_nat(0u);
v___y_1788_ = v___x_1792_;
goto v___jp_1787_;
}
v___jp_1787_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_mk_empty_array_with_capacity(v___y_1788_);
lean_dec(v___y_1788_);
v___x_1790_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1786_, v___x_1789_, v_t_1785_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___boxed(lean_object* v_00_u03b1_1793_, lean_object* v_cmp_1794_, lean_object* v_inst_1795_, lean_object* v_t_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Std_ExtTreeSet_toArray(v_00_u03b1_1793_, v_cmp_1794_, v_inst_1795_, v_t_1796_);
lean_dec_ref(v_cmp_1794_);
return v_res_1797_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__25, &l_Std_ExtTreeSet___auto__1___closed__25_once, _init_l_Std_ExtTreeSet___auto__1___closed__25);
return v___x_1798_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(lean_object* v_cmp_1799_, lean_object* v_as_1800_, size_t v_sz_1801_, size_t v_i_1802_, lean_object* v_b_1803_){
_start:
{
lean_object* v___y_1805_; uint8_t v___x_1809_; 
v___x_1809_ = lean_usize_dec_lt(v_i_1802_, v_sz_1801_);
if (v___x_1809_ == 0)
{
lean_dec_ref(v_cmp_1799_);
return v_b_1803_;
}
else
{
lean_object* v_a_1810_; uint8_t v___x_1811_; 
v_a_1810_ = lean_array_uget_borrowed(v_as_1800_, v_i_1802_);
lean_inc(v_b_1803_);
lean_inc(v_a_1810_);
lean_inc_ref(v_cmp_1799_);
v___x_1811_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1799_, v_a_1810_, v_b_1803_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_box(0);
lean_inc(v_a_1810_);
lean_inc_ref(v_cmp_1799_);
v___x_1813_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1799_, v_a_1810_, v___x_1812_, v_b_1803_);
v___y_1805_ = v___x_1813_;
goto v___jp_1804_;
}
else
{
v___y_1805_ = v_b_1803_;
goto v___jp_1804_;
}
}
v___jp_1804_:
{
size_t v___x_1806_; size_t v___x_1807_; 
v___x_1806_ = ((size_t)1ULL);
v___x_1807_ = lean_usize_add(v_i_1802_, v___x_1806_);
v_i_1802_ = v___x_1807_;
v_b_1803_ = v___y_1805_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1799_ = stack[0].m_obj;
lean_object* v_as_1800_ = stack[1].m_obj;
size_t v_sz_1801_ = stack[2].m_num;
size_t v_i_1802_ = stack[3].m_num;
lean_object* v_b_1803_ = stack[4].m_obj;
lean_object* v_res_1814_;
v_res_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1799_, v_as_1800_, v_sz_1801_, v_i_1802_, v_b_1803_);
stack->m_obj
 = v_res_1814_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg___boxed(lean_object* v_cmp_1815_, lean_object* v_as_1816_, lean_object* v_sz_1817_, lean_object* v_i_1818_, lean_object* v_b_1819_){
_start:
{
size_t v_sz_boxed_1820_; size_t v_i_boxed_1821_; lean_object* v_res_1822_; 
v_sz_boxed_1820_ = lean_unbox_usize(v_sz_1817_);
lean_dec(v_sz_1817_);
v_i_boxed_1821_ = lean_unbox_usize(v_i_1818_);
lean_dec(v_i_1818_);
v_res_1822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1815_, v_as_1816_, v_sz_boxed_1820_, v_i_boxed_1821_, v_b_1819_);
lean_dec_ref(v_as_1816_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg(lean_object* v_a_1823_, lean_object* v_cmp_1824_){
_start:
{
lean_object* v_r_1825_; size_t v_sz_1826_; size_t v___x_1827_; lean_object* v___x_1828_; 
v_r_1825_ = lean_box(1);
v_sz_1826_ = lean_array_size(v_a_1823_);
v___x_1827_ = ((size_t)0ULL);
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1824_, v_a_1823_, v_sz_1826_, v___x_1827_, v_r_1825_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg___boxed(lean_object* v_a_1829_, lean_object* v_cmp_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_1829_, v_cmp_1830_);
lean_dec_ref(v_a_1829_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray(lean_object* v_00_u03b1_1832_, lean_object* v_a_1833_, lean_object* v_cmp_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_1833_, v_cmp_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___boxed(lean_object* v_00_u03b1_1836_, lean_object* v_a_1837_, lean_object* v_cmp_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Std_ExtTreeSet_ofArray(v_00_u03b1_1836_, v_a_1837_, v_cmp_1838_);
lean_dec_ref(v_a_1837_);
return v_res_1839_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(lean_object* v_00_u03b1_1840_, lean_object* v_cmp_1841_, lean_object* v_as_1842_, size_t v_sz_1843_, size_t v_i_1844_, lean_object* v_b_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1841_, v_as_1842_, v_sz_1843_, v_i_1844_, v_b_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1841_ = stack[1].m_obj;
lean_object* v_as_1842_ = stack[2].m_obj;
size_t v_sz_1843_ = stack[3].m_num;
size_t v_i_1844_ = stack[4].m_num;
lean_object* v_b_1845_ = stack[5].m_obj;
lean_object* v_res_1847_;
v_res_1847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(lean_box(0), v_cmp_1841_, v_as_1842_, v_sz_1843_, v_i_1844_, v_b_1845_);
stack->m_obj
 = v_res_1847_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_cmp_1849_, lean_object* v_as_1850_, lean_object* v_sz_1851_, lean_object* v_i_1852_, lean_object* v_b_1853_){
_start:
{
size_t v_sz_boxed_1854_; size_t v_i_boxed_1855_; lean_object* v_res_1856_; 
v_sz_boxed_1854_ = lean_unbox_usize(v_sz_1851_);
lean_dec(v_sz_1851_);
v_i_boxed_1855_ = lean_unbox_usize(v_i_1852_);
lean_dec(v_i_1852_);
v_res_1856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(v_00_u03b1_1848_, v_cmp_1849_, v_as_1850_, v_sz_boxed_1854_, v_i_boxed_1855_, v_b_1853_);
lean_dec_ref(v_as_1850_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0(lean_object* v_b_u2082_1859_, lean_object* v_x_1860_){
_start:
{
if (lean_obj_tag(v_x_1860_) == 0)
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_b_u2082_1859_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; 
v___x_1862_ = ((lean_object*)(l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0));
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1863_, lean_object* v_x_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Std_ExtTreeSet_merge___redArg___lam__0(v_b_u2082_1863_, v_x_1864_);
lean_dec(v_x_1864_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__1(lean_object* v_cmp_1866_, lean_object* v_t_1867_, lean_object* v_a_1868_, lean_object* v_b_u2082_1869_){
_start:
{
lean_object* v___f_1870_; lean_object* v___x_1871_; 
v___f_1870_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1870_, 0, v_b_u2082_1869_);
v___x_1871_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_1866_, v_a_1868_, v___f_1870_, v_t_1867_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg(lean_object* v_cmp_1872_, lean_object* v_t_u2081_1873_, lean_object* v_t_u2082_1874_){
_start:
{
lean_object* v___f_1875_; lean_object* v___x_1876_; 
v___f_1875_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1875_, 0, v_cmp_1872_);
v___x_1876_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1875_, v_t_u2081_1873_, v_t_u2082_1874_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge(lean_object* v_00_u03b1_1877_, lean_object* v_cmp_1878_, lean_object* v_inst_1879_, lean_object* v_t_u2081_1880_, lean_object* v_t_u2082_1881_){
_start:
{
lean_object* v___f_1882_; lean_object* v___x_1883_; 
v___f_1882_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1882_, 0, v_cmp_1878_);
v___x_1883_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1882_, v_t_u2081_1880_, v_t_u2082_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg___lam__0(lean_object* v_cmp_1884_, lean_object* v_a_1885_, lean_object* v_____s_1886_){
_start:
{
uint8_t v___x_1887_; 
lean_inc(v_____s_1886_);
lean_inc(v_a_1885_);
lean_inc_ref(v_cmp_1884_);
v___x_1887_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1884_, v_a_1885_, v_____s_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = lean_box(0);
v___x_1889_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1884_, v_a_1885_, v___x_1888_, v_____s_1886_);
v___x_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
else
{
lean_object* v___x_1891_; 
lean_dec(v_a_1885_);
lean_dec_ref(v_cmp_1884_);
v___x_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_____s_1886_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg(lean_object* v_cmp_1892_, lean_object* v_inst_1893_, lean_object* v_t_1894_, lean_object* v_l_1895_){
_start:
{
lean_object* v___f_1896_; lean_object* v___x_1897_; 
v___f_1896_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1896_, 0, v_cmp_1892_);
v___x_1897_ = lean_apply_4(v_inst_1893_, lean_box(0), v_l_1895_, v_t_1894_, v___f_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany(lean_object* v_00_u03b1_1898_, lean_object* v_cmp_1899_, lean_object* v_inst_1900_, lean_object* v_00_u03c1_1901_, lean_object* v_inst_1902_, lean_object* v_t_1903_, lean_object* v_l_1904_){
_start:
{
lean_object* v___f_1905_; lean_object* v___x_1906_; 
v___f_1905_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1905_, 0, v_cmp_1899_);
v___x_1906_ = lean_apply_4(v_inst_1902_, lean_box(0), v_l_1904_, v_t_1903_, v___f_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union___redArg(lean_object* v_cmp_1907_, lean_object* v_t_u2081_1908_, lean_object* v_t_u2082_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1907_, v_t_u2081_1908_, v_t_u2082_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union(lean_object* v_00_u03b1_1911_, lean_object* v_cmp_1912_, lean_object* v_inst_1913_, lean_object* v_t_u2081_1914_, lean_object* v_t_u2082_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1912_, v_t_u2081_1914_, v_t_u2082_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp___redArg(lean_object* v_cmp_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_union), 5, 3);
lean_closure_set(v___x_1918_, 0, lean_box(0));
lean_closure_set(v___x_1918_, 1, v_cmp_1917_);
lean_closure_set(v___x_1918_, 2, lean_box(0));
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp(lean_object* v_00_u03b1_1919_, lean_object* v_cmp_1920_, lean_object* v_inst_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_union), 5, 3);
lean_closure_set(v___x_1922_, 0, lean_box(0));
lean_closure_set(v___x_1922_, 1, v_cmp_1920_);
lean_closure_set(v___x_1922_, 2, lean_box(0));
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter___redArg(lean_object* v_cmp_1923_, lean_object* v_t_u2081_1924_, lean_object* v_t_u2082_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1923_, v_t_u2081_1924_, v_t_u2082_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter(lean_object* v_00_u03b1_1927_, lean_object* v_cmp_1928_, lean_object* v_inst_1929_, lean_object* v_t_u2081_1930_, lean_object* v_t_u2082_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1928_, v_t_u2081_1930_, v_t_u2082_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp___redArg(lean_object* v_cmp_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_inter), 5, 3);
lean_closure_set(v___x_1934_, 0, lean_box(0));
lean_closure_set(v___x_1934_, 1, v_cmp_1933_);
lean_closure_set(v___x_1934_, 2, lean_box(0));
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp(lean_object* v_00_u03b1_1935_, lean_object* v_cmp_1936_, lean_object* v_inst_1937_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_inter), 5, 3);
lean_closure_set(v___x_1938_, 0, lean_box(0));
lean_closure_set(v___x_1938_, 1, v_cmp_1936_);
lean_closure_set(v___x_1938_, 2, lean_box(0));
return v___x_1938_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___f_1940_; 
v___x_1939_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1940_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1940_, 0, v___x_1939_);
return v___f_1940_;
}
}
uint8_t l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(lean_object* v_cmp_1941_, lean_object* v_m_u2081_1942_, lean_object* v_m_u2082_1943_){
_start:
{
lean_object* v___f_1944_; uint8_t v___x_1945_; 
v___f_1944_ = lean_obj_once(&l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0, &l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once, _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0);
v___x_1945_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_1941_, v___f_1944_, v_m_u2081_1942_, v_m_u2082_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1941_ = stack[0].m_obj;
lean_object* v_m_u2081_1942_ = stack[1].m_obj;
lean_object* v_m_u2082_1943_ = stack[2].m_obj;
uint8_t v_res_1946_;
v_res_1946_ = l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(v_cmp_1941_, v_m_u2081_1942_, v_m_u2082_1943_);
stack->m_num = v_res_1946_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_1947_, lean_object* v_m_u2081_1948_, lean_object* v_m_u2082_1949_){
_start:
{
uint8_t v_res_1950_; lean_object* v_r_1951_; 
v_res_1950_ = l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(v_cmp_1947_, v_m_u2081_1948_, v_m_u2082_1949_);
v_r_1951_ = lean_box(v_res_1950_);
return v_r_1951_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg(lean_object* v_cmp_1952_){
_start:
{
lean_object* v___f_1953_; 
v___f_1953_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1953_, 0, v_cmp_1952_);
return v___f_1953_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp(lean_object* v_00_u03b1_1954_, lean_object* v_cmp_1955_, lean_object* v_inst_1956_){
_start:
{
lean_object* v___f_1957_; 
v___f_1957_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1957_, 0, v_cmp_1955_);
return v___f_1957_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff___redArg(lean_object* v_cmp_1958_, lean_object* v_t_u2081_1959_, lean_object* v_t_u2082_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1958_, v_t_u2081_1959_, v_t_u2082_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff(lean_object* v_00_u03b1_1962_, lean_object* v_cmp_1963_, lean_object* v_inst_1964_, lean_object* v_t_u2081_1965_, lean_object* v_t_u2082_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1963_, v_t_u2081_1965_, v_t_u2082_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp___redArg(lean_object* v_cmp_1968_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_diff), 5, 3);
lean_closure_set(v___x_1969_, 0, lean_box(0));
lean_closure_set(v___x_1969_, 1, v_cmp_1968_);
lean_closure_set(v___x_1969_, 2, lean_box(0));
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp(lean_object* v_00_u03b1_1970_, lean_object* v_cmp_1971_, lean_object* v_inst_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_diff), 5, 3);
lean_closure_set(v___x_1973_, 0, lean_box(0));
lean_closure_set(v___x_1973_, 1, v_cmp_1971_);
lean_closure_set(v___x_1973_, 2, lean_box(0));
return v___x_1973_;
}
}
uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(lean_object* v_cmp_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_){
_start:
{
lean_object* v___f_1977_; uint8_t v___x_1978_; 
v___f_1977_ = lean_obj_once(&l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0, &l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once, _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0);
v___x_1978_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_1974_, v___f_1977_, v_x_1975_, v_x_1976_);
return v___x_1978_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1974_ = stack[0].m_obj;
lean_object* v_x_1975_ = stack[1].m_obj;
lean_object* v_x_1976_ = stack[2].m_obj;
uint8_t v_res_1979_;
v_res_1979_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_1974_, v_x_1975_, v_x_1976_);
stack->m_num = v_res_1979_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg___boxed(lean_object* v_cmp_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_){
_start:
{
uint8_t v_res_1983_; lean_object* v_r_1984_; 
v_res_1983_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_1980_, v_x_1981_, v_x_1982_);
v_r_1984_ = lean_box(v_res_1983_);
return v_r_1984_;
}
}
uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(lean_object* v_00_u03b1_1985_, lean_object* v_cmp_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
uint8_t v___x_1991_; 
v___x_1991_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_1986_, v_x_1989_, v_x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT void l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1986_ = stack[1].m_obj;
lean_object* v_x_1989_ = stack[4].m_obj;
lean_object* v_x_1990_ = stack[5].m_obj;
uint8_t v_res_1992_;
v_res_1992_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(lean_box(0), v_cmp_1986_, lean_box(0), lean_box(0), v_x_1989_, v_x_1990_);
stack->m_num = v_res_1992_;
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___boxed(lean_object* v_00_u03b1_1993_, lean_object* v_cmp_1994_, lean_object* v_inst_1995_, lean_object* v_inst_1996_, lean_object* v_x_1997_, lean_object* v_x_1998_){
_start:
{
uint8_t v_res_1999_; lean_object* v_r_2000_; 
v_res_1999_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(v_00_u03b1_1993_, v_cmp_1994_, v_inst_1995_, v_inst_1996_, v_x_1997_, v_x_1998_);
v_r_2000_ = lean_box(v_res_1999_);
return v_r_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg___lam__0(lean_object* v_cmp_2001_, lean_object* v_a_2002_, lean_object* v_____s_2003_){
_start:
{
lean_object* v_acc_2004_; lean_object* v___x_2005_; 
v_acc_2004_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2001_, v_a_2002_, v_____s_2003_);
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_acc_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg(lean_object* v_cmp_2006_, lean_object* v_inst_2007_, lean_object* v_t_2008_, lean_object* v_l_2009_){
_start:
{
lean_object* v___f_2010_; lean_object* v___x_2011_; 
v___f_2010_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2010_, 0, v_cmp_2006_);
v___x_2011_ = lean_apply_4(v_inst_2007_, lean_box(0), v_l_2009_, v_t_2008_, v___f_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany(lean_object* v_00_u03b1_2012_, lean_object* v_cmp_2013_, lean_object* v_inst_2014_, lean_object* v_00_u03c1_2015_, lean_object* v_inst_2016_, lean_object* v_t_2017_, lean_object* v_l_2018_){
_start:
{
lean_object* v___f_2019_; lean_object* v___x_2020_; 
v___f_2019_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2019_, 0, v_cmp_2013_);
v___x_2020_ = lean_apply_4(v_inst_2016_, lean_box(0), v_l_2018_, v_t_2017_, v___f_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_2024_, lean_object* v_inst_2025_, lean_object* v_m_2026_, lean_object* v_prec_2027_){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2028_ = ((lean_object*)(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_2029_ = lean_box(0);
v___x_2030_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_2031_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2030_, v___f_2024_, v___x_2029_, v_m_2026_);
v___x_2032_ = l_List_repr___redArg(v_inst_2025_, v___x_2031_);
v___x_2033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2028_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = l_Repr_addAppParen(v___x_2033_, v_prec_2027_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_2035_, lean_object* v_inst_2036_, lean_object* v_m_2037_, lean_object* v_prec_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(v___f_2035_, v_inst_2036_, v_m_2037_, v_prec_2038_);
lean_dec(v_prec_2038_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg(lean_object* v_inst_2040_){
_start:
{
lean_object* v___f_2041_; lean_object* v___f_2042_; 
v___f_2041_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___f_2042_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2042_, 0, v___f_2041_);
lean_closure_set(v___f_2042_, 1, v_inst_2040_);
return v___f_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp(lean_object* v_00_u03b1_2043_, lean_object* v_cmp_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg(v_inst_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_2048_, lean_object* v_cmp_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Std_ExtTreeSet_instReprOfTransCmp(v_00_u03b1_2048_, v_cmp_2049_, v_inst_2050_, v_inst_2051_);
lean_dec_ref(v_cmp_2049_);
return v_res_2052_;
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
