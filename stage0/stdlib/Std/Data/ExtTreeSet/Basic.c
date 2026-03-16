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
lean_object* lean_string_utf8_byte_size(lean_object*);
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
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__15;
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__16;
static const lean_ctor_object l_Std_ExtTreeSet___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeSet___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
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
static lean_once_cell_t l_Std_ExtTreeSet___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeSet___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_ExtTreeSet___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__14));
v___x_34_ = lean_string_utf8_byte_size(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__16(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__15, &l_Std_ExtTreeSet___auto__1___closed__15_once, _init_l_Std_ExtTreeSet___auto__1___closed__15);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__14));
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_box(0);
v___x_42_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__17));
v___x_43_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__16, &l_Std_ExtTreeSet___auto__1___closed__16_once, _init_l_Std_ExtTreeSet___auto__1___closed__16);
v___x_44_ = lean_box(2);
v___x_45_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
lean_ctor_set(v___x_45_, 2, v___x_42_);
lean_ctor_set(v___x_45_, 3, v___x_41_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__18, &l_Std_ExtTreeSet___auto__1___closed__18_once, _init_l_Std_ExtTreeSet___auto__1___closed__18);
v___x_47_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__13, &l_Std_ExtTreeSet___auto__1___closed__13_once, _init_l_Std_ExtTreeSet___auto__1___closed__13);
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__19, &l_Std_ExtTreeSet___auto__1___closed__19_once, _init_l_Std_ExtTreeSet___auto__1___closed__19);
v___x_50_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__11));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__21(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__20, &l_Std_ExtTreeSet___auto__1___closed__20_once, _init_l_Std_ExtTreeSet___auto__1___closed__20);
v___x_54_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__5));
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__22(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__21, &l_Std_ExtTreeSet___auto__1___closed__21_once, _init_l_Std_ExtTreeSet___auto__1___closed__21);
v___x_57_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__9));
v___x_58_ = lean_box(2);
v___x_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__23(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__22, &l_Std_ExtTreeSet___auto__1___closed__22_once, _init_l_Std_ExtTreeSet___auto__1___closed__22);
v___x_61_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__24(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__23, &l_Std_ExtTreeSet___auto__1___closed__23_once, _init_l_Std_ExtTreeSet___auto__1___closed__23);
v___x_64_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__7));
v___x_65_ = lean_box(2);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__25(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__24, &l_Std_ExtTreeSet___auto__1___closed__24_once, _init_l_Std_ExtTreeSet___auto__1___closed__24);
v___x_68_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__5));
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1___closed__26(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__25, &l_Std_ExtTreeSet___auto__1___closed__25_once, _init_l_Std_ExtTreeSet___auto__1___closed__25);
v___x_71_ = ((lean_object*)(l_Std_ExtTreeSet___auto__1___closed__4));
v___x_72_ = lean_box(2);
v___x_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_ExtTreeSet___auto__1(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__26, &l_Std_ExtTreeSet___auto__1___closed__26_once, _init_l_Std_ExtTreeSet___auto__1___closed__26);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty(lean_object* v_00_u03b1_75_, lean_object* v_cmp_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(1);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___boxed(lean_object* v_00_u03b1_78_, lean_object* v_cmp_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_ExtTreeSet_empty(v_00_u03b1_78_, v_cmp_79_);
lean_dec_ref(v_cmp_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection(lean_object* v_00_u03b1_81_, lean_object* v_cmp_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_box(1);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_84_, lean_object* v_cmp_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_ExtTreeSet_instEmptyCollection(v_00_u03b1_84_, v_cmp_85_);
lean_dec_ref(v_cmp_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited(lean_object* v_00_u03b1_87_, lean_object* v_cmp_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(1);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___boxed(lean_object* v_00_u03b1_90_, lean_object* v_cmp_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_ExtTreeSet_instInhabited(v_00_u03b1_90_, v_cmp_91_);
lean_dec_ref(v_cmp_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insert___redArg(lean_object* v_cmp_93_, lean_object* v_l_94_, lean_object* v_a_95_){
_start:
{
uint8_t v___x_96_; 
lean_inc(v_l_94_);
lean_inc(v_a_95_);
lean_inc_ref(v_cmp_93_);
v___x_96_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_93_, v_a_95_, v_l_94_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_box(0);
v___x_98_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_93_, v_a_95_, v___x_97_, v_l_94_);
return v___x_98_;
}
else
{
lean_dec(v_a_95_);
lean_dec_ref(v_cmp_93_);
return v_l_94_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insert(lean_object* v_00_u03b1_99_, lean_object* v_cmp_100_, lean_object* v_inst_101_, lean_object* v_l_102_, lean_object* v_a_103_){
_start:
{
uint8_t v___x_104_; 
lean_inc(v_l_102_);
lean_inc(v_a_103_);
lean_inc_ref(v_cmp_100_);
v___x_104_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_100_, v_a_103_, v_l_102_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_box(0);
v___x_106_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_100_, v_a_103_, v___x_105_, v_l_102_);
return v___x_106_;
}
else
{
lean_dec(v_a_103_);
lean_dec_ref(v_cmp_100_);
return v_l_102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0(lean_object* v_cmp_107_, lean_object* v_e_108_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_box(1);
lean_inc(v_e_108_);
lean_inc_ref(v_cmp_107_);
v___x_110_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_107_, v_e_108_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_box(0);
v___x_112_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_107_, v_e_108_, v___x_111_, v___x_109_);
return v___x_112_;
}
else
{
lean_dec(v_e_108_);
lean_dec_ref(v_cmp_107_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg(lean_object* v_cmp_113_){
_start:
{
lean_object* v___f_114_; 
v___f_114_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_114_, 0, v_cmp_113_);
return v___f_114_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp(lean_object* v_00_u03b1_115_, lean_object* v_cmp_116_, lean_object* v_inst_117_){
_start:
{
lean_object* v___f_118_; 
v___f_118_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_118_, 0, v_cmp_116_);
return v___f_118_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0(lean_object* v_cmp_119_, lean_object* v_e_120_, lean_object* v_s_121_){
_start:
{
uint8_t v___x_122_; 
lean_inc(v_s_121_);
lean_inc(v_e_120_);
lean_inc_ref(v_cmp_119_);
v___x_122_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_119_, v_e_120_, v_s_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_box(0);
v___x_124_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_119_, v_e_120_, v___x_123_, v_s_121_);
return v___x_124_;
}
else
{
lean_dec(v_e_120_);
lean_dec_ref(v_cmp_119_);
return v_s_121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp___redArg(lean_object* v_cmp_125_){
_start:
{
lean_object* v___f_126_; 
v___f_126_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_126_, 0, v_cmp_125_);
return v___f_126_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp(lean_object* v_00_u03b1_127_, lean_object* v_cmp_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v___f_130_; 
v___f_130_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_130_, 0, v_cmp_128_);
return v___f_130_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_containsThenInsert___redArg(lean_object* v_cmp_131_, lean_object* v_t_132_, lean_object* v_a_133_){
_start:
{
uint8_t v___x_134_; 
lean_inc(v_t_132_);
lean_inc(v_a_133_);
lean_inc_ref(v_cmp_131_);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_131_, v_a_133_, v_t_132_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_135_ = lean_box(0);
v___x_136_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_131_, v_a_133_, v___x_135_, v_t_132_);
v___x_137_ = lean_box(v___x_134_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec(v_a_133_);
lean_dec_ref(v_cmp_131_);
v___x_139_ = lean_box(v___x_134_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v_t_132_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_containsThenInsert(lean_object* v_00_u03b1_141_, lean_object* v_cmp_142_, lean_object* v_inst_143_, lean_object* v_t_144_, lean_object* v_a_145_){
_start:
{
uint8_t v___x_146_; 
lean_inc(v_t_144_);
lean_inc(v_a_145_);
lean_inc_ref(v_cmp_142_);
v___x_146_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_142_, v_a_145_, v_t_144_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_box(0);
v___x_148_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_142_, v_a_145_, v___x_147_, v_t_144_);
v___x_149_ = lean_box(v___x_146_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v_a_145_);
lean_dec_ref(v_cmp_142_);
v___x_151_ = lean_box(v___x_146_);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_t_144_);
return v___x_152_;
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_contains___redArg(lean_object* v_cmp_153_, lean_object* v_l_154_, lean_object* v_a_155_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_153_, v_a_155_, v_l_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_contains___redArg___boxed(lean_object* v_cmp_157_, lean_object* v_l_158_, lean_object* v_a_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Std_ExtTreeSet_contains___redArg(v_cmp_157_, v_l_158_, v_a_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_contains(lean_object* v_00_u03b1_162_, lean_object* v_cmp_163_, lean_object* v_inst_164_, lean_object* v_l_165_, lean_object* v_a_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_163_, v_a_166_, v_l_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_contains___boxed(lean_object* v_00_u03b1_168_, lean_object* v_cmp_169_, lean_object* v_inst_170_, lean_object* v_l_171_, lean_object* v_a_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Std_ExtTreeSet_contains(v_00_u03b1_168_, v_cmp_169_, v_inst_170_, v_l_171_, v_a_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp(lean_object* v_00_u03b1_175_, lean_object* v_cmp_176_, lean_object* v_inst_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_box(0);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_179_, lean_object* v_cmp_180_, lean_object* v_inst_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_ExtTreeSet_instMembershipOfTransCmp(v_00_u03b1_179_, v_cmp_180_, v_inst_181_);
lean_dec_ref(v_cmp_180_);
return v_res_182_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableMem___redArg(lean_object* v_cmp_183_, lean_object* v_m_184_, lean_object* v_a_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_183_, v_a_185_, v_m_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableMem___redArg___boxed(lean_object* v_cmp_187_, lean_object* v_m_188_, lean_object* v_a_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Std_ExtTreeSet_instDecidableMem___redArg(v_cmp_187_, v_m_188_, v_a_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableMem(lean_object* v_00_u03b1_192_, lean_object* v_cmp_193_, lean_object* v_inst_194_, lean_object* v_m_195_, lean_object* v_a_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_193_, v_a_196_, v_m_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableMem___boxed(lean_object* v_00_u03b1_198_, lean_object* v_cmp_199_, lean_object* v_inst_200_, lean_object* v_m_201_, lean_object* v_a_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Std_ExtTreeSet_instDecidableMem(v_00_u03b1_198_, v_cmp_199_, v_inst_200_, v_m_201_, v_a_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___redArg(lean_object* v_t_205_){
_start:
{
if (lean_obj_tag(v_t_205_) == 0)
{
lean_object* v_size_206_; 
v_size_206_ = lean_ctor_get(v_t_205_, 0);
lean_inc(v_size_206_);
return v_size_206_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_unsigned_to_nat(0u);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___redArg___boxed(lean_object* v_t_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Std_ExtTreeSet_size___redArg(v_t_208_);
lean_dec(v_t_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size(lean_object* v_00_u03b1_210_, lean_object* v_cmp_211_, lean_object* v_t_212_){
_start:
{
if (lean_obj_tag(v_t_212_) == 0)
{
lean_object* v_size_213_; 
v_size_213_ = lean_ctor_get(v_t_212_, 0);
lean_inc(v_size_213_);
return v_size_213_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_unsigned_to_nat(0u);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___boxed(lean_object* v_00_u03b1_215_, lean_object* v_cmp_216_, lean_object* v_t_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_ExtTreeSet_size(v_00_u03b1_215_, v_cmp_216_, v_t_217_);
lean_dec(v_t_217_);
lean_dec_ref(v_cmp_216_);
return v_res_218_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_isEmpty___redArg(lean_object* v_t_219_){
_start:
{
if (lean_obj_tag(v_t_219_) == 0)
{
uint8_t v___x_220_; 
v___x_220_ = 0;
return v___x_220_;
}
else
{
uint8_t v___x_221_; 
v___x_221_ = 1;
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_isEmpty___redArg___boxed(lean_object* v_t_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Std_ExtTreeSet_isEmpty___redArg(v_t_222_);
lean_dec(v_t_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_isEmpty(lean_object* v_00_u03b1_225_, lean_object* v_cmp_226_, lean_object* v_t_227_){
_start:
{
if (lean_obj_tag(v_t_227_) == 0)
{
uint8_t v___x_228_; 
v___x_228_ = 0;
return v___x_228_;
}
else
{
uint8_t v___x_229_; 
v___x_229_ = 1;
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_isEmpty___boxed(lean_object* v_00_u03b1_230_, lean_object* v_cmp_231_, lean_object* v_t_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Std_ExtTreeSet_isEmpty(v_00_u03b1_230_, v_cmp_231_, v_t_232_);
lean_dec(v_t_232_);
lean_dec_ref(v_cmp_231_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_erase___redArg(lean_object* v_cmp_235_, lean_object* v_t_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_235_, v_a_237_, v_t_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_erase(lean_object* v_00_u03b1_239_, lean_object* v_cmp_240_, lean_object* v_inst_241_, lean_object* v_t_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_240_, v_a_243_, v_t_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x3f___redArg(lean_object* v_cmp_245_, lean_object* v_t_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_245_, v_t_246_, v_a_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x3f(lean_object* v_00_u03b1_249_, lean_object* v_cmp_250_, lean_object* v_inst_251_, lean_object* v_t_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_250_, v_t_252_, v_a_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get___redArg(lean_object* v_cmp_255_, lean_object* v_t_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_255_, v_t_256_, v_a_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get(lean_object* v_00_u03b1_259_, lean_object* v_cmp_260_, lean_object* v_inst_261_, lean_object* v_t_262_, lean_object* v_a_263_, lean_object* v_h_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_260_, v_t_262_, v_a_263_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___redArg(lean_object* v_cmp_266_, lean_object* v_inst_267_, lean_object* v_t_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_266_, v_t_268_, v_a_269_, v_inst_267_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21(lean_object* v_00_u03b1_271_, lean_object* v_cmp_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_t_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_272_, v_t_275_, v_a_276_, v_inst_274_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg(lean_object* v_cmp_278_, lean_object* v_t_279_, lean_object* v_a_280_, lean_object* v_fallback_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_278_, v_t_279_, v_a_280_, v_fallback_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg___boxed(lean_object* v_cmp_283_, lean_object* v_t_284_, lean_object* v_a_285_, lean_object* v_fallback_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_ExtTreeSet_getD___redArg(v_cmp_283_, v_t_284_, v_a_285_, v_fallback_286_);
lean_dec(v_fallback_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD(lean_object* v_00_u03b1_288_, lean_object* v_cmp_289_, lean_object* v_inst_290_, lean_object* v_t_291_, lean_object* v_a_292_, lean_object* v_fallback_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_289_, v_t_291_, v_a_292_, v_fallback_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___boxed(lean_object* v_00_u03b1_295_, lean_object* v_cmp_296_, lean_object* v_inst_297_, lean_object* v_t_298_, lean_object* v_a_299_, lean_object* v_fallback_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_ExtTreeSet_getD(v_00_u03b1_295_, v_cmp_296_, v_inst_297_, v_t_298_, v_a_299_, v_fallback_300_);
lean_dec(v_fallback_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg(lean_object* v_t_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg___boxed(lean_object* v_t_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_ExtTreeSet_min_x3f___redArg(v_t_304_);
lean_dec(v_t_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f(lean_object* v_00_u03b1_306_, lean_object* v_cmp_307_, lean_object* v_inst_308_, lean_object* v_t_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___boxed(lean_object* v_00_u03b1_311_, lean_object* v_cmp_312_, lean_object* v_inst_313_, lean_object* v_t_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_ExtTreeSet_min_x3f(v_00_u03b1_311_, v_cmp_312_, v_inst_313_, v_t_314_);
lean_dec(v_t_314_);
lean_dec_ref(v_cmp_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg(lean_object* v_t_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg___boxed(lean_object* v_t_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_ExtTreeSet_min___redArg(v_t_318_);
lean_dec(v_t_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min(lean_object* v_00_u03b1_320_, lean_object* v_cmp_321_, lean_object* v_inst_322_, lean_object* v_t_323_, lean_object* v_h_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___boxed(lean_object* v_00_u03b1_326_, lean_object* v_cmp_327_, lean_object* v_inst_328_, lean_object* v_t_329_, lean_object* v_h_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_ExtTreeSet_min(v_00_u03b1_326_, v_cmp_327_, v_inst_328_, v_t_329_, v_h_330_);
lean_dec(v_t_329_);
lean_dec_ref(v_cmp_327_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg(lean_object* v_inst_332_, lean_object* v_t_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_332_, v_t_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg___boxed(lean_object* v_inst_335_, lean_object* v_t_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_ExtTreeSet_min_x21___redArg(v_inst_335_, v_t_336_);
lean_dec(v_t_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21(lean_object* v_00_u03b1_338_, lean_object* v_cmp_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_t_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_341_, v_t_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___boxed(lean_object* v_00_u03b1_344_, lean_object* v_cmp_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_t_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_ExtTreeSet_min_x21(v_00_u03b1_344_, v_cmp_345_, v_inst_346_, v_inst_347_, v_t_348_);
lean_dec(v_t_348_);
lean_dec_ref(v_cmp_345_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg(lean_object* v_t_350_, lean_object* v_fallback_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_350_, v_fallback_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg___boxed(lean_object* v_t_353_, lean_object* v_fallback_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_ExtTreeSet_minD___redArg(v_t_353_, v_fallback_354_);
lean_dec(v_fallback_354_);
lean_dec(v_t_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD(lean_object* v_00_u03b1_356_, lean_object* v_cmp_357_, lean_object* v_inst_358_, lean_object* v_t_359_, lean_object* v_fallback_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_359_, v_fallback_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___boxed(lean_object* v_00_u03b1_362_, lean_object* v_cmp_363_, lean_object* v_inst_364_, lean_object* v_t_365_, lean_object* v_fallback_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_ExtTreeSet_minD(v_00_u03b1_362_, v_cmp_363_, v_inst_364_, v_t_365_, v_fallback_366_);
lean_dec(v_fallback_366_);
lean_dec(v_t_365_);
lean_dec_ref(v_cmp_363_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg(lean_object* v_t_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg___boxed(lean_object* v_t_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_ExtTreeSet_max_x3f___redArg(v_t_370_);
lean_dec(v_t_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f(lean_object* v_00_u03b1_372_, lean_object* v_cmp_373_, lean_object* v_inst_374_, lean_object* v_t_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___boxed(lean_object* v_00_u03b1_377_, lean_object* v_cmp_378_, lean_object* v_inst_379_, lean_object* v_t_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_ExtTreeSet_max_x3f(v_00_u03b1_377_, v_cmp_378_, v_inst_379_, v_t_380_);
lean_dec(v_t_380_);
lean_dec_ref(v_cmp_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg(lean_object* v_t_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg___boxed(lean_object* v_t_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_ExtTreeSet_max___redArg(v_t_384_);
lean_dec(v_t_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max(lean_object* v_00_u03b1_386_, lean_object* v_cmp_387_, lean_object* v_inst_388_, lean_object* v_t_389_, lean_object* v_h_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___boxed(lean_object* v_00_u03b1_392_, lean_object* v_cmp_393_, lean_object* v_inst_394_, lean_object* v_t_395_, lean_object* v_h_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_ExtTreeSet_max(v_00_u03b1_392_, v_cmp_393_, v_inst_394_, v_t_395_, v_h_396_);
lean_dec(v_t_395_);
lean_dec_ref(v_cmp_393_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg(lean_object* v_inst_398_, lean_object* v_t_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_398_, v_t_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg___boxed(lean_object* v_inst_401_, lean_object* v_t_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_ExtTreeSet_max_x21___redArg(v_inst_401_, v_t_402_);
lean_dec(v_t_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21(lean_object* v_00_u03b1_404_, lean_object* v_cmp_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_t_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_407_, v_t_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___boxed(lean_object* v_00_u03b1_410_, lean_object* v_cmp_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_t_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_ExtTreeSet_max_x21(v_00_u03b1_410_, v_cmp_411_, v_inst_412_, v_inst_413_, v_t_414_);
lean_dec(v_t_414_);
lean_dec_ref(v_cmp_411_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg(lean_object* v_t_416_, lean_object* v_fallback_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_416_, v_fallback_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg___boxed(lean_object* v_t_419_, lean_object* v_fallback_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_ExtTreeSet_maxD___redArg(v_t_419_, v_fallback_420_);
lean_dec(v_fallback_420_);
lean_dec(v_t_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD(lean_object* v_00_u03b1_422_, lean_object* v_cmp_423_, lean_object* v_inst_424_, lean_object* v_t_425_, lean_object* v_fallback_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_425_, v_fallback_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___boxed(lean_object* v_00_u03b1_428_, lean_object* v_cmp_429_, lean_object* v_inst_430_, lean_object* v_t_431_, lean_object* v_fallback_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_ExtTreeSet_maxD(v_00_u03b1_428_, v_cmp_429_, v_inst_430_, v_t_431_, v_fallback_432_);
lean_dec(v_fallback_432_);
lean_dec(v_t_431_);
lean_dec_ref(v_cmp_429_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg(lean_object* v_t_434_, lean_object* v_n_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_434_, v_n_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg___boxed(lean_object* v_t_437_, lean_object* v_n_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_ExtTreeSet_atIdx_x3f___redArg(v_t_437_, v_n_438_);
lean_dec(v_t_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f(lean_object* v_00_u03b1_440_, lean_object* v_cmp_441_, lean_object* v_inst_442_, lean_object* v_t_443_, lean_object* v_n_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_443_, v_n_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___boxed(lean_object* v_00_u03b1_446_, lean_object* v_cmp_447_, lean_object* v_inst_448_, lean_object* v_t_449_, lean_object* v_n_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_ExtTreeSet_atIdx_x3f(v_00_u03b1_446_, v_cmp_447_, v_inst_448_, v_t_449_, v_n_450_);
lean_dec(v_t_449_);
lean_dec_ref(v_cmp_447_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg(lean_object* v_t_452_, lean_object* v_n_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_452_, v_n_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg___boxed(lean_object* v_t_455_, lean_object* v_n_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_ExtTreeSet_atIdx___redArg(v_t_455_, v_n_456_);
lean_dec(v_t_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx(lean_object* v_00_u03b1_458_, lean_object* v_cmp_459_, lean_object* v_inst_460_, lean_object* v_t_461_, lean_object* v_n_462_, lean_object* v_h_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_461_, v_n_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___boxed(lean_object* v_00_u03b1_465_, lean_object* v_cmp_466_, lean_object* v_inst_467_, lean_object* v_t_468_, lean_object* v_n_469_, lean_object* v_h_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Std_ExtTreeSet_atIdx(v_00_u03b1_465_, v_cmp_466_, v_inst_467_, v_t_468_, v_n_469_, v_h_470_);
lean_dec(v_t_468_);
lean_dec_ref(v_cmp_466_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg(lean_object* v_inst_472_, lean_object* v_t_473_, lean_object* v_n_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_472_, v_t_473_, v_n_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg___boxed(lean_object* v_inst_476_, lean_object* v_t_477_, lean_object* v_n_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_ExtTreeSet_atIdx_x21___redArg(v_inst_476_, v_t_477_, v_n_478_);
lean_dec(v_t_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21(lean_object* v_00_u03b1_480_, lean_object* v_cmp_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_t_484_, lean_object* v_n_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_483_, v_t_484_, v_n_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___boxed(lean_object* v_00_u03b1_487_, lean_object* v_cmp_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_t_491_, lean_object* v_n_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_ExtTreeSet_atIdx_x21(v_00_u03b1_487_, v_cmp_488_, v_inst_489_, v_inst_490_, v_t_491_, v_n_492_);
lean_dec(v_t_491_);
lean_dec_ref(v_cmp_488_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg(lean_object* v_t_494_, lean_object* v_n_495_, lean_object* v_fallback_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_494_, v_n_495_, v_fallback_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg___boxed(lean_object* v_t_498_, lean_object* v_n_499_, lean_object* v_fallback_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_ExtTreeSet_atIdxD___redArg(v_t_498_, v_n_499_, v_fallback_500_);
lean_dec(v_fallback_500_);
lean_dec(v_t_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD(lean_object* v_00_u03b1_502_, lean_object* v_cmp_503_, lean_object* v_inst_504_, lean_object* v_t_505_, lean_object* v_n_506_, lean_object* v_fallback_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_505_, v_n_506_, v_fallback_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___boxed(lean_object* v_00_u03b1_509_, lean_object* v_cmp_510_, lean_object* v_inst_511_, lean_object* v_t_512_, lean_object* v_n_513_, lean_object* v_fallback_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_ExtTreeSet_atIdxD(v_00_u03b1_509_, v_cmp_510_, v_inst_511_, v_t_512_, v_n_513_, v_fallback_514_);
lean_dec(v_fallback_514_);
lean_dec(v_t_512_);
lean_dec_ref(v_cmp_510_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f___redArg(lean_object* v_cmp_516_, lean_object* v_t_517_, lean_object* v_k_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_box(0);
v___x_520_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_516_, v_k_518_, v___x_519_, v_t_517_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f(lean_object* v_00_u03b1_521_, lean_object* v_cmp_522_, lean_object* v_inst_523_, lean_object* v_t_524_, lean_object* v_k_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_box(0);
v___x_527_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_522_, v_k_525_, v___x_526_, v_t_524_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f___redArg(lean_object* v_cmp_528_, lean_object* v_t_529_, lean_object* v_k_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_box(0);
v___x_532_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_528_, v_k_530_, v___x_531_, v_t_529_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f(lean_object* v_00_u03b1_533_, lean_object* v_cmp_534_, lean_object* v_inst_535_, lean_object* v_t_536_, lean_object* v_k_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_box(0);
v___x_539_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_534_, v_k_537_, v___x_538_, v_t_536_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f___redArg(lean_object* v_cmp_540_, lean_object* v_t_541_, lean_object* v_k_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_box(0);
v___x_544_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_540_, v_k_542_, v___x_543_, v_t_541_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f(lean_object* v_00_u03b1_545_, lean_object* v_cmp_546_, lean_object* v_inst_547_, lean_object* v_t_548_, lean_object* v_k_549_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_box(0);
v___x_551_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_546_, v_k_549_, v___x_550_, v_t_548_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f___redArg(lean_object* v_cmp_552_, lean_object* v_t_553_, lean_object* v_k_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_box(0);
v___x_556_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_552_, v_k_554_, v___x_555_, v_t_553_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f(lean_object* v_00_u03b1_557_, lean_object* v_cmp_558_, lean_object* v_inst_559_, lean_object* v_t_560_, lean_object* v_k_561_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_box(0);
v___x_563_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_558_, v_k_561_, v___x_562_, v_t_560_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE___redArg(lean_object* v_cmp_564_, lean_object* v_t_565_, lean_object* v_k_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_564_, v_k_566_, v_t_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE(lean_object* v_00_u03b1_568_, lean_object* v_cmp_569_, lean_object* v_inst_570_, lean_object* v_t_571_, lean_object* v_k_572_, lean_object* v_h_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_569_, v_k_572_, v_t_571_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT___redArg(lean_object* v_cmp_575_, lean_object* v_t_576_, lean_object* v_k_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_575_, v_k_577_, v_t_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT(lean_object* v_00_u03b1_579_, lean_object* v_cmp_580_, lean_object* v_inst_581_, lean_object* v_t_582_, lean_object* v_k_583_, lean_object* v_h_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_580_, v_k_583_, v_t_582_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE___redArg(lean_object* v_cmp_586_, lean_object* v_t_587_, lean_object* v_k_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_586_, v_k_588_, v_t_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE(lean_object* v_00_u03b1_590_, lean_object* v_cmp_591_, lean_object* v_inst_592_, lean_object* v_t_593_, lean_object* v_k_594_, lean_object* v_h_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_591_, v_k_594_, v_t_593_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT___redArg(lean_object* v_cmp_597_, lean_object* v_t_598_, lean_object* v_k_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_597_, v_k_599_, v_t_598_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT(lean_object* v_00_u03b1_601_, lean_object* v_cmp_602_, lean_object* v_inst_603_, lean_object* v_t_604_, lean_object* v_k_605_, lean_object* v_h_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_602_, v_k_605_, v_t_604_);
return v___x_607_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_611_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__2));
v___x_612_ = lean_unsigned_to_nat(14u);
v___x_613_ = lean_unsigned_to_nat(22u);
v___x_614_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__1));
v___x_615_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__0));
v___x_616_ = l_mkPanicMessageWithDecl(v___x_615_, v___x_614_, v___x_613_, v___x_612_, v___x_611_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___redArg(lean_object* v_cmp_617_, lean_object* v_inst_618_, lean_object* v_t_619_, lean_object* v_k_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_box(0);
v___x_622_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_617_, v_k_620_, v___x_621_, v_t_619_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_624_ = l_panic___redArg(v_inst_618_, v___x_623_);
return v___x_624_;
}
else
{
lean_object* v_val_625_; 
lean_dec(v_inst_618_);
v_val_625_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_val_625_);
lean_dec_ref(v___x_622_);
return v_val_625_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21(lean_object* v_00_u03b1_626_, lean_object* v_cmp_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_t_630_, lean_object* v_k_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_box(0);
v___x_633_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_627_, v_k_631_, v___x_632_, v_t_630_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_635_ = l_panic___redArg(v_inst_629_, v___x_634_);
return v___x_635_;
}
else
{
lean_object* v_val_636_; 
lean_dec(v_inst_629_);
v_val_636_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_val_636_);
lean_dec_ref(v___x_633_);
return v_val_636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg(lean_object* v_cmp_637_, lean_object* v_inst_638_, lean_object* v_t_639_, lean_object* v_k_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_box(0);
v___x_642_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_637_, v_k_640_, v___x_641_, v_t_639_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_644_ = l_panic___redArg(v_inst_638_, v___x_643_);
return v___x_644_;
}
else
{
lean_object* v_val_645_; 
lean_dec(v_inst_638_);
v_val_645_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_val_645_);
lean_dec_ref(v___x_642_);
return v_val_645_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21(lean_object* v_00_u03b1_646_, lean_object* v_cmp_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_t_650_, lean_object* v_k_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_box(0);
v___x_653_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_647_, v_k_651_, v___x_652_, v_t_650_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_655_ = l_panic___redArg(v_inst_649_, v___x_654_);
return v___x_655_;
}
else
{
lean_object* v_val_656_; 
lean_dec(v_inst_649_);
v_val_656_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_val_656_);
lean_dec_ref(v___x_653_);
return v_val_656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg(lean_object* v_cmp_657_, lean_object* v_inst_658_, lean_object* v_t_659_, lean_object* v_k_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_box(0);
v___x_662_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_657_, v_k_660_, v___x_661_, v_t_659_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_664_ = l_panic___redArg(v_inst_658_, v___x_663_);
return v___x_664_;
}
else
{
lean_object* v_val_665_; 
lean_dec(v_inst_658_);
v_val_665_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_val_665_);
lean_dec_ref(v___x_662_);
return v_val_665_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21(lean_object* v_00_u03b1_666_, lean_object* v_cmp_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_t_670_, lean_object* v_k_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_box(0);
v___x_673_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_667_, v_k_671_, v___x_672_, v_t_670_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_675_ = l_panic___redArg(v_inst_669_, v___x_674_);
return v___x_675_;
}
else
{
lean_object* v_val_676_; 
lean_dec(v_inst_669_);
v_val_676_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_val_676_);
lean_dec_ref(v___x_673_);
return v_val_676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg(lean_object* v_cmp_677_, lean_object* v_inst_678_, lean_object* v_t_679_, lean_object* v_k_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_box(0);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_677_, v_k_680_, v___x_681_, v_t_679_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_684_ = l_panic___redArg(v_inst_678_, v___x_683_);
return v___x_684_;
}
else
{
lean_object* v_val_685_; 
lean_dec(v_inst_678_);
v_val_685_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_val_685_);
lean_dec_ref(v___x_682_);
return v_val_685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21(lean_object* v_00_u03b1_686_, lean_object* v_cmp_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_t_690_, lean_object* v_k_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_box(0);
v___x_693_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_687_, v_k_691_, v___x_692_, v_t_690_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_695_ = l_panic___redArg(v_inst_689_, v___x_694_);
return v___x_695_;
}
else
{
lean_object* v_val_696_; 
lean_dec(v_inst_689_);
v_val_696_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_696_);
lean_dec_ref(v___x_693_);
return v_val_696_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg(lean_object* v_cmp_697_, lean_object* v_t_698_, lean_object* v_k_699_, lean_object* v_fallback_700_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_box(0);
v___x_702_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_697_, v_k_699_, v___x_701_, v_t_698_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_inc(v_fallback_700_);
return v_fallback_700_;
}
else
{
lean_object* v_val_703_; 
v_val_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_val_703_);
lean_dec_ref(v___x_702_);
return v_val_703_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg___boxed(lean_object* v_cmp_704_, lean_object* v_t_705_, lean_object* v_k_706_, lean_object* v_fallback_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_ExtTreeSet_getGED___redArg(v_cmp_704_, v_t_705_, v_k_706_, v_fallback_707_);
lean_dec(v_fallback_707_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED(lean_object* v_00_u03b1_709_, lean_object* v_cmp_710_, lean_object* v_inst_711_, lean_object* v_t_712_, lean_object* v_k_713_, lean_object* v_fallback_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_box(0);
v___x_716_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_710_, v_k_713_, v___x_715_, v_t_712_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_inc(v_fallback_714_);
return v_fallback_714_;
}
else
{
lean_object* v_val_717_; 
v_val_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_val_717_);
lean_dec_ref(v___x_716_);
return v_val_717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___boxed(lean_object* v_00_u03b1_718_, lean_object* v_cmp_719_, lean_object* v_inst_720_, lean_object* v_t_721_, lean_object* v_k_722_, lean_object* v_fallback_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_ExtTreeSet_getGED(v_00_u03b1_718_, v_cmp_719_, v_inst_720_, v_t_721_, v_k_722_, v_fallback_723_);
lean_dec(v_fallback_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg(lean_object* v_cmp_725_, lean_object* v_t_726_, lean_object* v_k_727_, lean_object* v_fallback_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_box(0);
v___x_730_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_725_, v_k_727_, v___x_729_, v_t_726_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_inc(v_fallback_728_);
return v_fallback_728_;
}
else
{
lean_object* v_val_731_; 
v_val_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_val_731_);
lean_dec_ref(v___x_730_);
return v_val_731_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg___boxed(lean_object* v_cmp_732_, lean_object* v_t_733_, lean_object* v_k_734_, lean_object* v_fallback_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Std_ExtTreeSet_getGTD___redArg(v_cmp_732_, v_t_733_, v_k_734_, v_fallback_735_);
lean_dec(v_fallback_735_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD(lean_object* v_00_u03b1_737_, lean_object* v_cmp_738_, lean_object* v_inst_739_, lean_object* v_t_740_, lean_object* v_k_741_, lean_object* v_fallback_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_box(0);
v___x_744_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_738_, v_k_741_, v___x_743_, v_t_740_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_inc(v_fallback_742_);
return v_fallback_742_;
}
else
{
lean_object* v_val_745_; 
v_val_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_val_745_);
lean_dec_ref(v___x_744_);
return v_val_745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___boxed(lean_object* v_00_u03b1_746_, lean_object* v_cmp_747_, lean_object* v_inst_748_, lean_object* v_t_749_, lean_object* v_k_750_, lean_object* v_fallback_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Std_ExtTreeSet_getGTD(v_00_u03b1_746_, v_cmp_747_, v_inst_748_, v_t_749_, v_k_750_, v_fallback_751_);
lean_dec(v_fallback_751_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg(lean_object* v_cmp_753_, lean_object* v_t_754_, lean_object* v_k_755_, lean_object* v_fallback_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_box(0);
v___x_758_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_753_, v_k_755_, v___x_757_, v_t_754_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_inc(v_fallback_756_);
return v_fallback_756_;
}
else
{
lean_object* v_val_759_; 
v_val_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref(v___x_758_);
return v_val_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg___boxed(lean_object* v_cmp_760_, lean_object* v_t_761_, lean_object* v_k_762_, lean_object* v_fallback_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_ExtTreeSet_getLED___redArg(v_cmp_760_, v_t_761_, v_k_762_, v_fallback_763_);
lean_dec(v_fallback_763_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED(lean_object* v_00_u03b1_765_, lean_object* v_cmp_766_, lean_object* v_inst_767_, lean_object* v_t_768_, lean_object* v_k_769_, lean_object* v_fallback_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_box(0);
v___x_772_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_766_, v_k_769_, v___x_771_, v_t_768_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_inc(v_fallback_770_);
return v_fallback_770_;
}
else
{
lean_object* v_val_773_; 
v_val_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_val_773_);
lean_dec_ref(v___x_772_);
return v_val_773_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___boxed(lean_object* v_00_u03b1_774_, lean_object* v_cmp_775_, lean_object* v_inst_776_, lean_object* v_t_777_, lean_object* v_k_778_, lean_object* v_fallback_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_ExtTreeSet_getLED(v_00_u03b1_774_, v_cmp_775_, v_inst_776_, v_t_777_, v_k_778_, v_fallback_779_);
lean_dec(v_fallback_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg(lean_object* v_cmp_781_, lean_object* v_t_782_, lean_object* v_k_783_, lean_object* v_fallback_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_box(0);
v___x_786_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_781_, v_k_783_, v___x_785_, v_t_782_);
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
lean_dec_ref(v___x_786_);
return v_val_787_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg___boxed(lean_object* v_cmp_788_, lean_object* v_t_789_, lean_object* v_k_790_, lean_object* v_fallback_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_ExtTreeSet_getLTD___redArg(v_cmp_788_, v_t_789_, v_k_790_, v_fallback_791_);
lean_dec(v_fallback_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD(lean_object* v_00_u03b1_793_, lean_object* v_cmp_794_, lean_object* v_inst_795_, lean_object* v_t_796_, lean_object* v_k_797_, lean_object* v_fallback_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_box(0);
v___x_800_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_794_, v_k_797_, v___x_799_, v_t_796_);
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
lean_dec_ref(v___x_800_);
return v_val_801_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___boxed(lean_object* v_00_u03b1_802_, lean_object* v_cmp_803_, lean_object* v_inst_804_, lean_object* v_t_805_, lean_object* v_k_806_, lean_object* v_fallback_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_ExtTreeSet_getLTD(v_00_u03b1_802_, v_cmp_803_, v_inst_804_, v_t_805_, v_k_806_, v_fallback_807_);
lean_dec(v_fallback_807_);
return v_res_808_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_filter___redArg___lam__0(lean_object* v_f_809_, lean_object* v_a_810_, lean_object* v_x_811_){
_start:
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_apply_1(v_f_809_, v_a_810_);
v___x_813_ = lean_unbox(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg___lam__0___boxed(lean_object* v_f_814_, lean_object* v_a_815_, lean_object* v_x_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l_Std_ExtTreeSet_filter___redArg___lam__0(v_f_814_, v_a_815_, v_x_816_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg(lean_object* v_f_819_, lean_object* v_m_820_){
_start:
{
lean_object* v___f_821_; lean_object* v___x_822_; 
v___f_821_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_821_, 0, v_f_819_);
v___x_822_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_821_, v_m_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter(lean_object* v_00_u03b1_823_, lean_object* v_cmp_824_, lean_object* v_f_825_, lean_object* v_m_826_){
_start:
{
lean_object* v___f_827_; lean_object* v___x_828_; 
v___f_827_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_827_, 0, v_f_825_);
v___x_828_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_827_, v_m_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___boxed(lean_object* v_00_u03b1_829_, lean_object* v_cmp_830_, lean_object* v_f_831_, lean_object* v_m_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_ExtTreeSet_filter(v_00_u03b1_829_, v_cmp_830_, v_f_831_, v_m_832_);
lean_dec_ref(v_cmp_830_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg___lam__0(lean_object* v_f_834_, lean_object* v_c_835_, lean_object* v_a_836_, lean_object* v_x_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = lean_apply_2(v_f_834_, v_c_835_, v_a_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg(lean_object* v_inst_839_, lean_object* v_f_840_, lean_object* v_init_841_, lean_object* v_t_842_){
_start:
{
lean_object* v___f_843_; lean_object* v___x_844_; 
v___f_843_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_843_, 0, v_f_840_);
v___x_844_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_839_, v___f_843_, v_init_841_, v_t_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM(lean_object* v_00_u03b1_845_, lean_object* v_cmp_846_, lean_object* v_00_u03b4_847_, lean_object* v_m_848_, lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_f_852_, lean_object* v_init_853_, lean_object* v_t_854_){
_start:
{
lean_object* v___f_855_; lean_object* v___x_856_; 
v___f_855_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_855_, 0, v_f_852_);
v___x_856_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_849_, v___f_855_, v_init_853_, v_t_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___boxed(lean_object* v_00_u03b1_857_, lean_object* v_cmp_858_, lean_object* v_00_u03b4_859_, lean_object* v_m_860_, lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_f_864_, lean_object* v_init_865_, lean_object* v_t_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Std_ExtTreeSet_foldlM(v_00_u03b1_857_, v_cmp_858_, v_00_u03b4_859_, v_m_860_, v_inst_861_, v_inst_862_, v_inst_863_, v_f_864_, v_init_865_, v_t_866_);
lean_dec_ref(v_cmp_858_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___redArg(lean_object* v_f_868_, lean_object* v_init_869_, lean_object* v_t_870_){
_start:
{
lean_object* v___f_871_; lean_object* v___x_872_; 
v___f_871_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_871_, 0, v_f_868_);
v___x_872_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_871_, v_init_869_, v_t_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl(lean_object* v_00_u03b1_873_, lean_object* v_cmp_874_, lean_object* v_00_u03b4_875_, lean_object* v_inst_876_, lean_object* v_f_877_, lean_object* v_init_878_, lean_object* v_t_879_){
_start:
{
lean_object* v___f_880_; lean_object* v___x_881_; 
v___f_880_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_880_, 0, v_f_877_);
v___x_881_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_880_, v_init_878_, v_t_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___boxed(lean_object* v_00_u03b1_882_, lean_object* v_cmp_883_, lean_object* v_00_u03b4_884_, lean_object* v_inst_885_, lean_object* v_f_886_, lean_object* v_init_887_, lean_object* v_t_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_ExtTreeSet_foldl(v_00_u03b1_882_, v_cmp_883_, v_00_u03b4_884_, v_inst_885_, v_f_886_, v_init_887_, v_t_888_);
lean_dec_ref(v_cmp_883_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg___lam__0(lean_object* v_f_890_, lean_object* v_a_891_, lean_object* v_x_892_, lean_object* v_acc_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_apply_2(v_f_890_, v_a_891_, v_acc_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg(lean_object* v_inst_895_, lean_object* v_f_896_, lean_object* v_init_897_, lean_object* v_t_898_){
_start:
{
lean_object* v___f_899_; lean_object* v___x_900_; 
v___f_899_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_899_, 0, v_f_896_);
v___x_900_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_895_, v___f_899_, v_init_897_, v_t_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM(lean_object* v_00_u03b1_901_, lean_object* v_cmp_902_, lean_object* v_00_u03b4_903_, lean_object* v_m_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_f_908_, lean_object* v_init_909_, lean_object* v_t_910_){
_start:
{
lean_object* v___f_911_; lean_object* v___x_912_; 
v___f_911_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_911_, 0, v_f_908_);
v___x_912_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_905_, v___f_911_, v_init_909_, v_t_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___boxed(lean_object* v_00_u03b1_913_, lean_object* v_cmp_914_, lean_object* v_00_u03b4_915_, lean_object* v_m_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_f_920_, lean_object* v_init_921_, lean_object* v_t_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_ExtTreeSet_foldrM(v_00_u03b1_913_, v_cmp_914_, v_00_u03b4_915_, v_m_916_, v_inst_917_, v_inst_918_, v_inst_919_, v_f_920_, v_init_921_, v_t_922_);
lean_dec_ref(v_cmp_914_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg___lam__0(lean_object* v_f_924_, lean_object* v_x1_925_, lean_object* v_x2_926_, lean_object* v_x3_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = lean_apply_2(v_f_924_, v_x1_925_, v_x3_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg(lean_object* v_f_948_, lean_object* v_init_949_, lean_object* v_t_950_){
_start:
{
lean_object* v___f_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___f_951_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_951_, 0, v_f_948_);
v___x_952_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_953_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_952_, v___f_951_, v_init_949_, v_t_950_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr(lean_object* v_00_u03b1_954_, lean_object* v_cmp_955_, lean_object* v_00_u03b4_956_, lean_object* v_inst_957_, lean_object* v_f_958_, lean_object* v_init_959_, lean_object* v_t_960_){
_start:
{
lean_object* v___f_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___f_961_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_961_, 0, v_f_958_);
v___x_962_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_963_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_962_, v___f_961_, v_init_959_, v_t_960_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___boxed(lean_object* v_00_u03b1_964_, lean_object* v_cmp_965_, lean_object* v_00_u03b4_966_, lean_object* v_inst_967_, lean_object* v_f_968_, lean_object* v_init_969_, lean_object* v_t_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Std_ExtTreeSet_foldr(v_00_u03b1_964_, v_cmp_965_, v_00_u03b4_966_, v_inst_967_, v_f_968_, v_init_969_, v_t_970_);
lean_dec_ref(v_cmp_965_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg___lam__0(lean_object* v_f_972_, lean_object* v_cmp_973_, lean_object* v_x_974_, lean_object* v_a_975_, lean_object* v_b_976_){
_start:
{
lean_object* v_fst_977_; lean_object* v_snd_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_992_; 
v_fst_977_ = lean_ctor_get(v_x_974_, 0);
v_snd_978_ = lean_ctor_get(v_x_974_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_x_974_);
if (v_isSharedCheck_992_ == 0)
{
v___x_980_ = v_x_974_;
v_isShared_981_ = v_isSharedCheck_992_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_978_);
lean_inc(v_fst_977_);
lean_dec(v_x_974_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_992_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; uint8_t v___x_983_; 
lean_inc(v_a_975_);
v___x_982_ = lean_apply_1(v_f_972_, v_a_975_);
v___x_983_ = lean_unbox(v___x_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_973_, v_a_975_, v_b_976_, v_snd_978_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v___x_984_);
v___x_986_ = v___x_980_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_fst_977_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_988_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_973_, v_a_975_, v_b_976_, v_fst_977_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_988_);
v___x_990_ = v___x_980_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_snd_978_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg(lean_object* v_cmp_995_, lean_object* v_f_996_, lean_object* v_t_997_){
_start:
{
lean_object* v___f_998_; lean_object* v___x_999_; lean_object* v_p_1000_; lean_object* v_fst_1001_; lean_object* v_snd_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v___f_998_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_998_, 0, v_f_996_);
lean_closure_set(v___f_998_, 1, v_cmp_995_);
v___x_999_ = ((lean_object*)(l_Std_ExtTreeSet_partition___redArg___closed__0));
v_p_1000_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_998_, v___x_999_, v_t_997_);
v_fst_1001_ = lean_ctor_get(v_p_1000_, 0);
v_snd_1002_ = lean_ctor_get(v_p_1000_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_p_1000_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v_p_1000_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_snd_1002_);
lean_inc(v_fst_1001_);
lean_dec(v_p_1000_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_fst_1001_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_snd_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition(lean_object* v_00_u03b1_1010_, lean_object* v_cmp_1011_, lean_object* v_inst_1012_, lean_object* v_f_1013_, lean_object* v_t_1014_){
_start:
{
lean_object* v___f_1015_; lean_object* v___x_1016_; lean_object* v_p_1017_; lean_object* v_fst_1018_; lean_object* v_snd_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v___f_1015_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1015_, 0, v_f_1013_);
lean_closure_set(v___f_1015_, 1, v_cmp_1011_);
v___x_1016_ = ((lean_object*)(l_Std_ExtTreeSet_partition___redArg___closed__0));
v_p_1017_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1015_, v___x_1016_, v_t_1014_);
v_fst_1018_ = lean_ctor_get(v_p_1017_, 0);
v_snd_1019_ = lean_ctor_get(v_p_1017_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_p_1017_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v_p_1017_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_snd_1019_);
lean_inc(v_fst_1018_);
lean_dec(v_p_1017_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_fst_1018_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_snd_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg___lam__0(lean_object* v_f_1027_, lean_object* v_x_1028_, lean_object* v_k_1029_, lean_object* v_v_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_apply_1(v_f_1027_, v_k_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg(lean_object* v_inst_1032_, lean_object* v_f_1033_, lean_object* v_t_1034_){
_start:
{
lean_object* v___f_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___f_1035_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1035_, 0, v_f_1033_);
v___x_1036_ = lean_box(0);
v___x_1037_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1032_, v___f_1035_, v___x_1036_, v_t_1034_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM(lean_object* v_00_u03b1_1038_, lean_object* v_cmp_1039_, lean_object* v_m_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_f_1044_, lean_object* v_t_1045_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___f_1046_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1046_, 0, v_f_1044_);
v___x_1047_ = lean_box(0);
v___x_1048_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1041_, v___f_1046_, v___x_1047_, v_t_1045_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___boxed(lean_object* v_00_u03b1_1049_, lean_object* v_cmp_1050_, lean_object* v_m_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_f_1055_, lean_object* v_t_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Std_ExtTreeSet_forM(v_00_u03b1_1049_, v_cmp_1050_, v_m_1051_, v_inst_1052_, v_inst_1053_, v_inst_1054_, v_f_1055_, v_t_1056_);
lean_dec_ref(v_cmp_1050_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__0(lean_object* v_f_1058_, lean_object* v_a_1059_, lean_object* v_b_1060_, lean_object* v_c_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_apply_2(v_f_1058_, v_a_1059_, v_c_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__1(lean_object* v_toPure_1063_, lean_object* v_____do__lift_1064_){
_start:
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1065_ = lean_ctor_get(v_____do__lift_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref(v_____do__lift_1064_);
v___x_1066_ = lean_apply_2(v_toPure_1063_, lean_box(0), v_a_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg(lean_object* v_inst_1067_, lean_object* v_f_1068_, lean_object* v_init_1069_, lean_object* v_t_1070_){
_start:
{
lean_object* v_toApplicative_1071_; lean_object* v_toBind_1072_; lean_object* v_toPure_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; 
v_toApplicative_1071_ = lean_ctor_get(v_inst_1067_, 0);
v_toBind_1072_ = lean_ctor_get(v_inst_1067_, 1);
lean_inc(v_toBind_1072_);
v_toPure_1073_ = lean_ctor_get(v_toApplicative_1071_, 1);
lean_inc(v_toPure_1073_);
v___f_1074_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1074_, 0, v_f_1068_);
v___x_1075_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1067_, v___f_1074_, v_init_1069_, v_t_1070_);
v___f_1076_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1076_, 0, v_toPure_1073_);
v___x_1077_ = lean_apply_4(v_toBind_1072_, lean_box(0), lean_box(0), v___x_1075_, v___f_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn(lean_object* v_00_u03b1_1078_, lean_object* v_cmp_1079_, lean_object* v_00_u03b4_1080_, lean_object* v_m_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v_f_1085_, lean_object* v_init_1086_, lean_object* v_t_1087_){
_start:
{
lean_object* v_toApplicative_1088_; lean_object* v_toBind_1089_; lean_object* v_toPure_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___f_1093_; lean_object* v___x_1094_; 
v_toApplicative_1088_ = lean_ctor_get(v_inst_1082_, 0);
v_toBind_1089_ = lean_ctor_get(v_inst_1082_, 1);
lean_inc(v_toBind_1089_);
v_toPure_1090_ = lean_ctor_get(v_toApplicative_1088_, 1);
lean_inc(v_toPure_1090_);
v___f_1091_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1091_, 0, v_f_1085_);
v___x_1092_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1082_, v___f_1091_, v_init_1086_, v_t_1087_);
v___f_1093_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1093_, 0, v_toPure_1090_);
v___x_1094_ = lean_apply_4(v_toBind_1089_, lean_box(0), lean_box(0), v___x_1092_, v___f_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___boxed(lean_object* v_00_u03b1_1095_, lean_object* v_cmp_1096_, lean_object* v_00_u03b4_1097_, lean_object* v_m_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_f_1102_, lean_object* v_init_1103_, lean_object* v_t_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_ExtTreeSet_forIn(v_00_u03b1_1095_, v_cmp_1096_, v_00_u03b4_1097_, v_m_1098_, v_inst_1099_, v_inst_1100_, v_inst_1101_, v_f_1102_, v_init_1103_, v_t_1104_);
lean_dec_ref(v_cmp_1096_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_1106_, lean_object* v_t_1107_, lean_object* v_f_1108_){
_start:
{
lean_object* v___f_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___f_1109_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1109_, 0, v_f_1108_);
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1106_, v___f_1109_, v___x_1110_, v_t_1107_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1112_){
_start:
{
lean_object* v___f_1113_; 
v___f_1113_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1113_, 0, v_inst_1112_);
return v___f_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1114_, lean_object* v_cmp_1115_, lean_object* v_m_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_){
_start:
{
lean_object* v___f_1120_; 
v___f_1120_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1120_, 0, v_inst_1118_);
return v___f_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1121_, lean_object* v_cmp_1122_, lean_object* v_m_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(v_00_u03b1_1121_, v_cmp_1122_, v_m_1123_, v_inst_1124_, v_inst_1125_, v_inst_1126_);
lean_dec_ref(v_cmp_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_m_1130_, lean_object* v_init_1131_, lean_object* v_f_1132_){
_start:
{
lean_object* v_toApplicative_1133_; lean_object* v_toBind_1134_; lean_object* v_toPure_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; lean_object* v___f_1138_; lean_object* v___x_1139_; 
v_toApplicative_1133_ = lean_ctor_get(v_inst_1128_, 0);
v_toBind_1134_ = lean_ctor_get(v_inst_1128_, 1);
lean_inc(v_toBind_1134_);
v_toPure_1135_ = lean_ctor_get(v_toApplicative_1133_, 1);
lean_inc(v_toPure_1135_);
v___f_1136_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1136_, 0, v_f_1132_);
v___x_1137_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1128_, v___f_1136_, v_init_1131_, v_m_1130_);
v___f_1138_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1138_, 0, v_toPure_1135_);
v___x_1139_ = lean_apply_4(v_toBind_1134_, lean_box(0), lean_box(0), v___x_1137_, v___f_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1140_){
_start:
{
lean_object* v___f_1141_; 
v___f_1141_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1141_, 0, v_inst_1140_);
return v___f_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1142_, lean_object* v_cmp_1143_, lean_object* v_m_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_){
_start:
{
lean_object* v___f_1148_; 
v___f_1148_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1148_, 0, v_inst_1146_);
return v___f_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1149_, lean_object* v_cmp_1150_, lean_object* v_m_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(v_00_u03b1_1149_, v_cmp_1150_, v_m_1151_, v_inst_1152_, v_inst_1153_, v_inst_1154_);
lean_dec_ref(v_cmp_1150_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0(lean_object* v_p_1156_, lean_object* v___x_1157_, lean_object* v___x_1158_, lean_object* v_a_1159_, lean_object* v_b_1160_, lean_object* v_acc_1161_){
_start:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_apply_1(v_p_1156_, v_a_1159_);
v___x_1163_ = lean_unbox(v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1157_);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec_ref(v___x_1157_);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1162_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v___x_1158_);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0___boxed(lean_object* v_p_1168_, lean_object* v___x_1169_, lean_object* v___x_1170_, lean_object* v_a_1171_, lean_object* v_b_1172_, lean_object* v_acc_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Std_ExtTreeSet_any___redArg___lam__0(v_p_1168_, v___x_1169_, v___x_1170_, v_a_1171_, v_b_1172_, v_acc_1173_);
lean_dec_ref(v_acc_1173_);
return v_res_1174_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_any___redArg(lean_object* v_t_1178_, lean_object* v_p_1179_){
_start:
{
lean_object* v___y_1181_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v_a_1191_; 
v___x_1186_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1187_ = lean_box(0);
v___x_1188_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1189_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1189_, 0, v_p_1179_);
lean_closure_set(v___f_1189_, 1, v___x_1188_);
lean_closure_set(v___f_1189_, 2, v___x_1187_);
v___x_1190_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1186_, v___f_1189_, v___x_1188_, v_t_1178_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___y_1181_ = v_a_1191_;
goto v___jp_1180_;
v___jp_1180_:
{
lean_object* v_fst_1182_; 
v_fst_1182_ = lean_ctor_get(v___y_1181_, 0);
lean_inc(v_fst_1182_);
lean_dec_ref(v___y_1181_);
if (lean_obj_tag(v_fst_1182_) == 0)
{
uint8_t v___x_1183_; 
v___x_1183_ = 0;
return v___x_1183_;
}
else
{
lean_object* v_val_1184_; uint8_t v___x_1185_; 
v_val_1184_ = lean_ctor_get(v_fst_1182_, 0);
lean_inc(v_val_1184_);
lean_dec_ref(v_fst_1182_);
v___x_1185_ = lean_unbox(v_val_1184_);
lean_dec(v_val_1184_);
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___boxed(lean_object* v_t_1192_, lean_object* v_p_1193_){
_start:
{
uint8_t v_res_1194_; lean_object* v_r_1195_; 
v_res_1194_ = l_Std_ExtTreeSet_any___redArg(v_t_1192_, v_p_1193_);
v_r_1195_ = lean_box(v_res_1194_);
return v_r_1195_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_any(lean_object* v_00_u03b1_1196_, lean_object* v_cmp_1197_, lean_object* v_inst_1198_, lean_object* v_t_1199_, lean_object* v_p_1200_){
_start:
{
lean_object* v___y_1202_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v_a_1212_; 
v___x_1207_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1208_ = lean_box(0);
v___x_1209_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1210_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1210_, 0, v_p_1200_);
lean_closure_set(v___f_1210_, 1, v___x_1209_);
lean_closure_set(v___f_1210_, 2, v___x_1208_);
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1207_, v___f_1210_, v___x_1209_, v_t_1199_);
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___y_1202_ = v_a_1212_;
goto v___jp_1201_;
v___jp_1201_:
{
lean_object* v_fst_1203_; 
v_fst_1203_ = lean_ctor_get(v___y_1202_, 0);
lean_inc(v_fst_1203_);
lean_dec_ref(v___y_1202_);
if (lean_obj_tag(v_fst_1203_) == 0)
{
uint8_t v___x_1204_; 
v___x_1204_ = 0;
return v___x_1204_;
}
else
{
lean_object* v_val_1205_; uint8_t v___x_1206_; 
v_val_1205_ = lean_ctor_get(v_fst_1203_, 0);
lean_inc(v_val_1205_);
lean_dec_ref(v_fst_1203_);
v___x_1206_ = lean_unbox(v_val_1205_);
lean_dec(v_val_1205_);
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___boxed(lean_object* v_00_u03b1_1213_, lean_object* v_cmp_1214_, lean_object* v_inst_1215_, lean_object* v_t_1216_, lean_object* v_p_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l_Std_ExtTreeSet_any(v_00_u03b1_1213_, v_cmp_1214_, v_inst_1215_, v_t_1216_, v_p_1217_);
lean_dec_ref(v_cmp_1214_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0(lean_object* v_p_1220_, lean_object* v___x_1221_, lean_object* v___x_1222_, lean_object* v_a_1223_, lean_object* v_b_1224_, lean_object* v_acc_1225_){
_start:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_apply_1(v_p_1220_, v_a_1223_);
v___x_1227_ = lean_unbox(v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec_ref(v___x_1222_);
v___x_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v___x_1221_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1222_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0___boxed(lean_object* v_p_1232_, lean_object* v___x_1233_, lean_object* v___x_1234_, lean_object* v_a_1235_, lean_object* v_b_1236_, lean_object* v_acc_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Std_ExtTreeSet_all___redArg___lam__0(v_p_1232_, v___x_1233_, v___x_1234_, v_a_1235_, v_b_1236_, v_acc_1237_);
lean_dec_ref(v_acc_1237_);
return v_res_1238_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_all___redArg(lean_object* v_t_1239_, lean_object* v_p_1240_){
_start:
{
lean_object* v___y_1242_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; lean_object* v_a_1252_; 
v___x_1247_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1248_ = lean_box(0);
v___x_1249_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1250_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1250_, 0, v_p_1240_);
lean_closure_set(v___f_1250_, 1, v___x_1248_);
lean_closure_set(v___f_1250_, 2, v___x_1249_);
v___x_1251_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1247_, v___f_1250_, v___x_1249_, v_t_1239_);
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___y_1242_ = v_a_1252_;
goto v___jp_1241_;
v___jp_1241_:
{
lean_object* v_fst_1243_; 
v_fst_1243_ = lean_ctor_get(v___y_1242_, 0);
lean_inc(v_fst_1243_);
lean_dec_ref(v___y_1242_);
if (lean_obj_tag(v_fst_1243_) == 0)
{
uint8_t v___x_1244_; 
v___x_1244_ = 1;
return v___x_1244_;
}
else
{
lean_object* v_val_1245_; uint8_t v___x_1246_; 
v_val_1245_ = lean_ctor_get(v_fst_1243_, 0);
lean_inc(v_val_1245_);
lean_dec_ref(v_fst_1243_);
v___x_1246_ = lean_unbox(v_val_1245_);
lean_dec(v_val_1245_);
return v___x_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___boxed(lean_object* v_t_1253_, lean_object* v_p_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Std_ExtTreeSet_all___redArg(v_t_1253_, v_p_1254_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_all(lean_object* v_00_u03b1_1257_, lean_object* v_cmp_1258_, lean_object* v_inst_1259_, lean_object* v_t_1260_, lean_object* v_p_1261_){
_start:
{
lean_object* v___y_1263_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; lean_object* v_a_1273_; 
v___x_1268_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1269_ = lean_box(0);
v___x_1270_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1271_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1271_, 0, v_p_1261_);
lean_closure_set(v___f_1271_, 1, v___x_1269_);
lean_closure_set(v___f_1271_, 2, v___x_1270_);
v___x_1272_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1268_, v___f_1271_, v___x_1270_, v_t_1260_);
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___y_1263_ = v_a_1273_;
goto v___jp_1262_;
v___jp_1262_:
{
lean_object* v_fst_1264_; 
v_fst_1264_ = lean_ctor_get(v___y_1263_, 0);
lean_inc(v_fst_1264_);
lean_dec_ref(v___y_1263_);
if (lean_obj_tag(v_fst_1264_) == 0)
{
uint8_t v___x_1265_; 
v___x_1265_ = 1;
return v___x_1265_;
}
else
{
lean_object* v_val_1266_; uint8_t v___x_1267_; 
v_val_1266_ = lean_ctor_get(v_fst_1264_, 0);
lean_inc(v_val_1266_);
lean_dec_ref(v_fst_1264_);
v___x_1267_ = lean_unbox(v_val_1266_);
lean_dec(v_val_1266_);
return v___x_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_cmp_1275_, lean_object* v_inst_1276_, lean_object* v_t_1277_, lean_object* v_p_1278_){
_start:
{
uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_res_1279_ = l_Std_ExtTreeSet_all(v_00_u03b1_1274_, v_cmp_1275_, v_inst_1276_, v_t_1277_, v_p_1278_);
lean_dec_ref(v_cmp_1275_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg___lam__0(lean_object* v_x1_1281_, lean_object* v_x2_1282_, lean_object* v_x3_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_x1_1281_);
lean_ctor_set(v___x_1284_, 1, v_x3_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg(lean_object* v_t_1286_){
_start:
{
lean_object* v___f_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___f_1287_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___x_1288_ = lean_box(0);
v___x_1289_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1290_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1289_, v___f_1287_, v___x_1288_, v_t_1286_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList(lean_object* v_00_u03b1_1291_, lean_object* v_cmp_1292_, lean_object* v_inst_1293_, lean_object* v_t_1294_){
_start:
{
lean_object* v___f_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___f_1295_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___x_1296_ = lean_box(0);
v___x_1297_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1298_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1297_, v___f_1295_, v___x_1296_, v_t_1294_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___boxed(lean_object* v_00_u03b1_1299_, lean_object* v_cmp_1300_, lean_object* v_inst_1301_, lean_object* v_t_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Std_ExtTreeSet_toList(v_00_u03b1_1299_, v_cmp_1300_, v_inst_1301_, v_t_1302_);
lean_dec_ref(v_cmp_1300_);
return v_res_1303_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_ofList___auto__1(void){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__26, &l_Std_ExtTreeSet___auto__1___closed__26_once, _init_l_Std_ExtTreeSet___auto__1___closed__26);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(lean_object* v_cmp_1305_, lean_object* v_k_1306_, lean_object* v_v_1307_, lean_object* v_t_1308_){
_start:
{
if (lean_obj_tag(v_t_1308_) == 0)
{
lean_object* v_size_1309_; lean_object* v_k_1310_; lean_object* v_v_1311_; lean_object* v_l_1312_; lean_object* v_r_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1594_; 
v_size_1309_ = lean_ctor_get(v_t_1308_, 0);
v_k_1310_ = lean_ctor_get(v_t_1308_, 1);
v_v_1311_ = lean_ctor_get(v_t_1308_, 2);
v_l_1312_ = lean_ctor_get(v_t_1308_, 3);
v_r_1313_ = lean_ctor_get(v_t_1308_, 4);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_t_1308_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1315_ = v_t_1308_;
v_isShared_1316_ = v_isSharedCheck_1594_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_r_1313_);
lean_inc(v_l_1312_);
lean_inc(v_v_1311_);
lean_inc(v_k_1310_);
lean_inc(v_size_1309_);
lean_dec(v_t_1308_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1594_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
lean_inc_ref(v_cmp_1305_);
lean_inc(v_k_1310_);
lean_inc(v_k_1306_);
v___x_1317_ = lean_apply_2(v_cmp_1305_, v_k_1306_, v_k_1310_);
v___x_1318_ = lean_unbox(v___x_1317_);
switch(v___x_1318_)
{
case 0:
{
lean_object* v_impl_1319_; lean_object* v___x_1320_; 
lean_dec(v_size_1309_);
v_impl_1319_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1305_, v_k_1306_, v_v_1307_, v_l_1312_);
v___x_1320_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1313_) == 0)
{
lean_object* v_size_1321_; lean_object* v_size_1322_; lean_object* v_k_1323_; lean_object* v_v_1324_; lean_object* v_l_1325_; lean_object* v_r_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_size_1321_ = lean_ctor_get(v_r_1313_, 0);
v_size_1322_ = lean_ctor_get(v_impl_1319_, 0);
lean_inc(v_size_1322_);
v_k_1323_ = lean_ctor_get(v_impl_1319_, 1);
lean_inc(v_k_1323_);
v_v_1324_ = lean_ctor_get(v_impl_1319_, 2);
lean_inc(v_v_1324_);
v_l_1325_ = lean_ctor_get(v_impl_1319_, 3);
lean_inc(v_l_1325_);
v_r_1326_ = lean_ctor_get(v_impl_1319_, 4);
lean_inc(v_r_1326_);
v___x_1327_ = lean_unsigned_to_nat(3u);
v___x_1328_ = lean_nat_mul(v___x_1327_, v_size_1321_);
v___x_1329_ = lean_nat_dec_lt(v___x_1328_, v_size_1322_);
lean_dec(v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
lean_dec(v_r_1326_);
lean_dec(v_l_1325_);
lean_dec(v_v_1324_);
lean_dec(v_k_1323_);
v___x_1330_ = lean_nat_add(v___x_1320_, v_size_1322_);
lean_dec(v_size_1322_);
v___x_1331_ = lean_nat_add(v___x_1330_, v_size_1321_);
lean_dec(v___x_1330_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 3, v_impl_1319_);
lean_ctor_set(v___x_1315_, 0, v___x_1331_);
v___x_1333_ = v___x_1315_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_impl_1319_);
lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_r_1313_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
else
{
lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1400_; 
v_isSharedCheck_1400_ = !lean_is_exclusive(v_impl_1319_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; lean_object* v_unused_1402_; lean_object* v_unused_1403_; lean_object* v_unused_1404_; lean_object* v_unused_1405_; 
v_unused_1401_ = lean_ctor_get(v_impl_1319_, 4);
lean_dec(v_unused_1401_);
v_unused_1402_ = lean_ctor_get(v_impl_1319_, 3);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_impl_1319_, 2);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_impl_1319_, 1);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_impl_1319_, 0);
lean_dec(v_unused_1405_);
v___x_1336_ = v_impl_1319_;
v_isShared_1337_ = v_isSharedCheck_1400_;
goto v_resetjp_1335_;
}
else
{
lean_dec(v_impl_1319_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1400_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_size_1338_; lean_object* v_size_1339_; lean_object* v_k_1340_; lean_object* v_v_1341_; lean_object* v_l_1342_; lean_object* v_r_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_size_1338_ = lean_ctor_get(v_l_1325_, 0);
v_size_1339_ = lean_ctor_get(v_r_1326_, 0);
v_k_1340_ = lean_ctor_get(v_r_1326_, 1);
v_v_1341_ = lean_ctor_get(v_r_1326_, 2);
v_l_1342_ = lean_ctor_get(v_r_1326_, 3);
v_r_1343_ = lean_ctor_get(v_r_1326_, 4);
v___x_1344_ = lean_unsigned_to_nat(2u);
v___x_1345_ = lean_nat_mul(v___x_1344_, v_size_1338_);
v___x_1346_ = lean_nat_dec_lt(v_size_1339_, v___x_1345_);
lean_dec(v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1375_; 
lean_inc(v_r_1343_);
lean_inc(v_l_1342_);
lean_inc(v_v_1341_);
lean_inc(v_k_1340_);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_r_1326_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; lean_object* v_unused_1377_; lean_object* v_unused_1378_; lean_object* v_unused_1379_; lean_object* v_unused_1380_; 
v_unused_1376_ = lean_ctor_get(v_r_1326_, 4);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v_r_1326_, 3);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_r_1326_, 2);
lean_dec(v_unused_1378_);
v_unused_1379_ = lean_ctor_get(v_r_1326_, 1);
lean_dec(v_unused_1379_);
v_unused_1380_ = lean_ctor_get(v_r_1326_, 0);
lean_dec(v_unused_1380_);
v___x_1348_ = v_r_1326_;
v_isShared_1349_ = v_isSharedCheck_1375_;
goto v_resetjp_1347_;
}
else
{
lean_dec(v_r_1326_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1375_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___x_1363_; lean_object* v___y_1365_; 
v___x_1350_ = lean_nat_add(v___x_1320_, v_size_1322_);
lean_dec(v_size_1322_);
v___x_1351_ = lean_nat_add(v___x_1350_, v_size_1321_);
lean_dec(v___x_1350_);
v___x_1363_ = lean_nat_add(v___x_1320_, v_size_1338_);
if (lean_obj_tag(v_l_1342_) == 0)
{
lean_object* v_size_1373_; 
v_size_1373_ = lean_ctor_get(v_l_1342_, 0);
lean_inc(v_size_1373_);
v___y_1365_ = v_size_1373_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_unsigned_to_nat(0u);
v___y_1365_ = v___x_1374_;
goto v___jp_1364_;
}
v___jp_1352_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_nat_add(v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec(v___y_1354_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v_r_1313_);
lean_ctor_set(v___x_1348_, 3, v_r_1343_);
lean_ctor_set(v___x_1348_, 2, v_v_1311_);
lean_ctor_set(v___x_1348_, 1, v_k_1310_);
lean_ctor_set(v___x_1348_, 0, v___x_1356_);
v___x_1358_ = v___x_1348_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_r_1343_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_r_1313_);
v___x_1358_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1360_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 4, v___x_1358_);
lean_ctor_set(v___x_1336_, 3, v___y_1353_);
lean_ctor_set(v___x_1336_, 2, v_v_1341_);
lean_ctor_set(v___x_1336_, 1, v_k_1340_);
lean_ctor_set(v___x_1336_, 0, v___x_1351_);
v___x_1360_ = v___x_1336_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_k_1340_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_v_1341_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v___y_1353_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
v___jp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_nat_add(v___x_1363_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec(v___x_1363_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v_l_1342_);
lean_ctor_set(v___x_1315_, 3, v_l_1325_);
lean_ctor_set(v___x_1315_, 2, v_v_1324_);
lean_ctor_set(v___x_1315_, 1, v_k_1323_);
lean_ctor_set(v___x_1315_, 0, v___x_1366_);
v___x_1368_ = v___x_1315_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_k_1323_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_v_1324_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_l_1325_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v_l_1342_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_nat_add(v___x_1320_, v_size_1321_);
if (lean_obj_tag(v_r_1343_) == 0)
{
lean_object* v_size_1370_; 
v_size_1370_ = lean_ctor_get(v_r_1343_, 0);
lean_inc(v_size_1370_);
v___y_1353_ = v___x_1368_;
v___y_1354_ = v___x_1369_;
v___y_1355_ = v_size_1370_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_unsigned_to_nat(0u);
v___y_1353_ = v___x_1368_;
v___y_1354_ = v___x_1369_;
v___y_1355_ = v___x_1371_;
goto v___jp_1352_;
}
}
}
}
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
lean_del_object(v___x_1315_);
v___x_1381_ = lean_nat_add(v___x_1320_, v_size_1322_);
lean_dec(v_size_1322_);
v___x_1382_ = lean_nat_add(v___x_1381_, v_size_1321_);
lean_dec(v___x_1381_);
v___x_1383_ = lean_nat_add(v___x_1320_, v_size_1321_);
v___x_1384_ = lean_nat_add(v___x_1383_, v_size_1339_);
lean_dec(v___x_1383_);
lean_inc_ref(v_r_1313_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 4, v_r_1313_);
lean_ctor_set(v___x_1336_, 3, v_r_1326_);
lean_ctor_set(v___x_1336_, 2, v_v_1311_);
lean_ctor_set(v___x_1336_, 1, v_k_1310_);
lean_ctor_set(v___x_1336_, 0, v___x_1384_);
v___x_1386_ = v___x_1336_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_r_1326_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_r_1313_);
v___x_1386_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
v_isSharedCheck_1393_ = !lean_is_exclusive(v_r_1313_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; lean_object* v_unused_1395_; lean_object* v_unused_1396_; lean_object* v_unused_1397_; lean_object* v_unused_1398_; 
v_unused_1394_ = lean_ctor_get(v_r_1313_, 4);
lean_dec(v_unused_1394_);
v_unused_1395_ = lean_ctor_get(v_r_1313_, 3);
lean_dec(v_unused_1395_);
v_unused_1396_ = lean_ctor_get(v_r_1313_, 2);
lean_dec(v_unused_1396_);
v_unused_1397_ = lean_ctor_get(v_r_1313_, 1);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_r_1313_, 0);
lean_dec(v_unused_1398_);
v___x_1388_ = v_r_1313_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_dec(v_r_1313_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 4, v___x_1386_);
lean_ctor_set(v___x_1388_, 3, v_l_1325_);
lean_ctor_set(v___x_1388_, 2, v_v_1324_);
lean_ctor_set(v___x_1388_, 1, v_k_1323_);
lean_ctor_set(v___x_1388_, 0, v___x_1382_);
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_k_1323_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_v_1324_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_l_1325_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v___x_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1406_; 
v_l_1406_ = lean_ctor_get(v_impl_1319_, 3);
lean_inc(v_l_1406_);
if (lean_obj_tag(v_l_1406_) == 0)
{
lean_object* v_r_1407_; lean_object* v_k_1408_; lean_object* v_v_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1420_; 
v_r_1407_ = lean_ctor_get(v_impl_1319_, 4);
v_k_1408_ = lean_ctor_get(v_impl_1319_, 1);
v_v_1409_ = lean_ctor_get(v_impl_1319_, 2);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_impl_1319_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; lean_object* v_unused_1422_; 
v_unused_1421_ = lean_ctor_get(v_impl_1319_, 3);
lean_dec(v_unused_1421_);
v_unused_1422_ = lean_ctor_get(v_impl_1319_, 0);
lean_dec(v_unused_1422_);
v___x_1411_ = v_impl_1319_;
v_isShared_1412_ = v_isSharedCheck_1420_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_r_1407_);
lean_inc(v_v_1409_);
lean_inc(v_k_1408_);
lean_dec(v_impl_1319_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1420_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1413_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1407_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 3, v_r_1407_);
lean_ctor_set(v___x_1411_, 2, v_v_1311_);
lean_ctor_set(v___x_1411_, 1, v_k_1310_);
lean_ctor_set(v___x_1411_, 0, v___x_1320_);
v___x_1415_ = v___x_1411_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_r_1407_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_r_1407_);
v___x_1415_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v___x_1415_);
lean_ctor_set(v___x_1315_, 3, v_l_1406_);
lean_ctor_set(v___x_1315_, 2, v_v_1409_);
lean_ctor_set(v___x_1315_, 1, v_k_1408_);
lean_ctor_set(v___x_1315_, 0, v___x_1413_);
v___x_1417_ = v___x_1315_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_k_1408_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_v_1409_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_object* v_r_1423_; 
v_r_1423_ = lean_ctor_get(v_impl_1319_, 4);
lean_inc(v_r_1423_);
if (lean_obj_tag(v_r_1423_) == 0)
{
lean_object* v_k_1424_; lean_object* v_v_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1448_; 
v_k_1424_ = lean_ctor_get(v_impl_1319_, 1);
v_v_1425_ = lean_ctor_get(v_impl_1319_, 2);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_impl_1319_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; 
v_unused_1449_ = lean_ctor_get(v_impl_1319_, 4);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_impl_1319_, 3);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_impl_1319_, 0);
lean_dec(v_unused_1451_);
v___x_1427_ = v_impl_1319_;
v_isShared_1428_ = v_isSharedCheck_1448_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_v_1425_);
lean_inc(v_k_1424_);
lean_dec(v_impl_1319_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1448_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v_k_1429_; lean_object* v_v_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1444_; 
v_k_1429_ = lean_ctor_get(v_r_1423_, 1);
v_v_1430_ = lean_ctor_get(v_r_1423_, 2);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_r_1423_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; lean_object* v_unused_1446_; lean_object* v_unused_1447_; 
v_unused_1445_ = lean_ctor_get(v_r_1423_, 4);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_r_1423_, 3);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_r_1423_, 0);
lean_dec(v_unused_1447_);
v___x_1432_ = v_r_1423_;
v_isShared_1433_ = v_isSharedCheck_1444_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_v_1430_);
lean_inc(v_k_1429_);
lean_dec(v_r_1423_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1444_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_unsigned_to_nat(3u);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v_l_1406_);
lean_ctor_set(v___x_1432_, 3, v_l_1406_);
lean_ctor_set(v___x_1432_, 2, v_v_1425_);
lean_ctor_set(v___x_1432_, 1, v_k_1424_);
lean_ctor_set(v___x_1432_, 0, v___x_1320_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_k_1424_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_v_1425_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_l_1406_);
v___x_1436_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1438_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 4, v_l_1406_);
lean_ctor_set(v___x_1427_, 2, v_v_1311_);
lean_ctor_set(v___x_1427_, 1, v_k_1310_);
lean_ctor_set(v___x_1427_, 0, v___x_1320_);
v___x_1438_ = v___x_1427_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_1442_, 4, v_l_1406_);
v___x_1438_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v___x_1438_);
lean_ctor_set(v___x_1315_, 3, v___x_1436_);
lean_ctor_set(v___x_1315_, 2, v_v_1430_);
lean_ctor_set(v___x_1315_, 1, v_k_1429_);
lean_ctor_set(v___x_1315_, 0, v___x_1434_);
v___x_1440_ = v___x_1315_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_k_1429_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_v_1430_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1452_ = lean_unsigned_to_nat(2u);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v_r_1423_);
lean_ctor_set(v___x_1315_, 3, v_impl_1319_);
lean_ctor_set(v___x_1315_, 0, v___x_1452_);
v___x_1454_ = v___x_1315_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_impl_1319_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_r_1423_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1457_; 
lean_dec(v_v_1311_);
lean_dec(v_k_1310_);
lean_dec_ref(v_cmp_1305_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 2, v_v_1307_);
lean_ctor_set(v___x_1315_, 1, v_k_1306_);
v___x_1457_ = v___x_1315_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_size_1309_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_k_1306_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_v_1307_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v_l_1312_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v_r_1313_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
default: 
{
lean_object* v_impl_1459_; lean_object* v___x_1460_; 
lean_dec(v_size_1309_);
v_impl_1459_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1305_, v_k_1306_, v_v_1307_, v_r_1313_);
v___x_1460_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1312_) == 0)
{
lean_object* v_size_1461_; lean_object* v_size_1462_; lean_object* v_k_1463_; lean_object* v_v_1464_; lean_object* v_l_1465_; lean_object* v_r_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_size_1461_ = lean_ctor_get(v_l_1312_, 0);
v_size_1462_ = lean_ctor_get(v_impl_1459_, 0);
lean_inc(v_size_1462_);
v_k_1463_ = lean_ctor_get(v_impl_1459_, 1);
lean_inc(v_k_1463_);
v_v_1464_ = lean_ctor_get(v_impl_1459_, 2);
lean_inc(v_v_1464_);
v_l_1465_ = lean_ctor_get(v_impl_1459_, 3);
lean_inc(v_l_1465_);
v_r_1466_ = lean_ctor_get(v_impl_1459_, 4);
lean_inc(v_r_1466_);
v___x_1467_ = lean_unsigned_to_nat(3u);
v___x_1468_ = lean_nat_mul(v___x_1467_, v_size_1461_);
v___x_1469_ = lean_nat_dec_lt(v___x_1468_, v_size_1462_);
lean_dec(v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
lean_dec(v_r_1466_);
lean_dec(v_l_1465_);
lean_dec(v_v_1464_);
lean_dec(v_k_1463_);
v___x_1470_ = lean_nat_add(v___x_1460_, v_size_1461_);
v___x_1471_ = lean_nat_add(v___x_1470_, v_size_1462_);
lean_dec(v_size_1462_);
lean_dec(v___x_1470_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v_impl_1459_);
lean_ctor_set(v___x_1315_, 0, v___x_1471_);
v___x_1473_ = v___x_1315_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_l_1312_);
lean_ctor_set(v_reuseFailAlloc_1474_, 4, v_impl_1459_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
else
{
lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1538_; 
v_isSharedCheck_1538_ = !lean_is_exclusive(v_impl_1459_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; lean_object* v_unused_1540_; lean_object* v_unused_1541_; lean_object* v_unused_1542_; lean_object* v_unused_1543_; 
v_unused_1539_ = lean_ctor_get(v_impl_1459_, 4);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_impl_1459_, 3);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v_impl_1459_, 2);
lean_dec(v_unused_1541_);
v_unused_1542_ = lean_ctor_get(v_impl_1459_, 1);
lean_dec(v_unused_1542_);
v_unused_1543_ = lean_ctor_get(v_impl_1459_, 0);
lean_dec(v_unused_1543_);
v___x_1476_ = v_impl_1459_;
v_isShared_1477_ = v_isSharedCheck_1538_;
goto v_resetjp_1475_;
}
else
{
lean_dec(v_impl_1459_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1538_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v_size_1478_; lean_object* v_k_1479_; lean_object* v_v_1480_; lean_object* v_l_1481_; lean_object* v_r_1482_; lean_object* v_size_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_size_1478_ = lean_ctor_get(v_l_1465_, 0);
v_k_1479_ = lean_ctor_get(v_l_1465_, 1);
v_v_1480_ = lean_ctor_get(v_l_1465_, 2);
v_l_1481_ = lean_ctor_get(v_l_1465_, 3);
v_r_1482_ = lean_ctor_get(v_l_1465_, 4);
v_size_1483_ = lean_ctor_get(v_r_1466_, 0);
v___x_1484_ = lean_unsigned_to_nat(2u);
v___x_1485_ = lean_nat_mul(v___x_1484_, v_size_1483_);
v___x_1486_ = lean_nat_dec_lt(v_size_1478_, v___x_1485_);
lean_dec(v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1514_; 
lean_inc(v_r_1482_);
lean_inc(v_l_1481_);
lean_inc(v_v_1480_);
lean_inc(v_k_1479_);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_l_1465_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; 
v_unused_1515_ = lean_ctor_get(v_l_1465_, 4);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_l_1465_, 3);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_l_1465_, 2);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_l_1465_, 1);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_l_1465_, 0);
lean_dec(v_unused_1519_);
v___x_1488_ = v_l_1465_;
v_isShared_1489_ = v_isSharedCheck_1514_;
goto v_resetjp_1487_;
}
else
{
lean_dec(v_l_1465_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1514_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1504_; 
v___x_1490_ = lean_nat_add(v___x_1460_, v_size_1461_);
v___x_1491_ = lean_nat_add(v___x_1490_, v_size_1462_);
lean_dec(v_size_1462_);
if (lean_obj_tag(v_l_1481_) == 0)
{
lean_object* v_size_1512_; 
v_size_1512_ = lean_ctor_get(v_l_1481_, 0);
lean_inc(v_size_1512_);
v___y_1504_ = v_size_1512_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_unsigned_to_nat(0u);
v___y_1504_ = v___x_1513_;
goto v___jp_1503_;
}
v___jp_1492_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = lean_nat_add(v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec(v___y_1494_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 4, v_r_1466_);
lean_ctor_set(v___x_1488_, 3, v_r_1482_);
lean_ctor_set(v___x_1488_, 2, v_v_1464_);
lean_ctor_set(v___x_1488_, 1, v_k_1463_);
lean_ctor_set(v___x_1488_, 0, v___x_1496_);
v___x_1498_ = v___x_1488_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1463_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1464_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_r_1482_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_r_1466_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 4, v___x_1498_);
lean_ctor_set(v___x_1476_, 3, v___y_1493_);
lean_ctor_set(v___x_1476_, 2, v_v_1480_);
lean_ctor_set(v___x_1476_, 1, v_k_1479_);
lean_ctor_set(v___x_1476_, 0, v___x_1491_);
v___x_1500_ = v___x_1476_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v___y_1493_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
v___jp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_nat_add(v___x_1490_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec(v___x_1490_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v_l_1481_);
lean_ctor_set(v___x_1315_, 0, v___x_1505_);
v___x_1507_ = v___x_1315_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_l_1312_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_l_1481_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_nat_add(v___x_1460_, v_size_1483_);
if (lean_obj_tag(v_r_1482_) == 0)
{
lean_object* v_size_1509_; 
v_size_1509_ = lean_ctor_get(v_r_1482_, 0);
lean_inc(v_size_1509_);
v___y_1493_ = v___x_1507_;
v___y_1494_ = v___x_1508_;
v___y_1495_ = v_size_1509_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_unsigned_to_nat(0u);
v___y_1493_ = v___x_1507_;
v___y_1494_ = v___x_1508_;
v___y_1495_ = v___x_1510_;
goto v___jp_1492_;
}
}
}
}
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
lean_del_object(v___x_1315_);
v___x_1520_ = lean_nat_add(v___x_1460_, v_size_1461_);
v___x_1521_ = lean_nat_add(v___x_1520_, v_size_1462_);
lean_dec(v_size_1462_);
v___x_1522_ = lean_nat_add(v___x_1520_, v_size_1478_);
lean_dec(v___x_1520_);
lean_inc_ref(v_l_1312_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 4, v_l_1465_);
lean_ctor_set(v___x_1476_, 3, v_l_1312_);
lean_ctor_set(v___x_1476_, 2, v_v_1311_);
lean_ctor_set(v___x_1476_, 1, v_k_1310_);
lean_ctor_set(v___x_1476_, 0, v___x_1522_);
v___x_1524_ = v___x_1476_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1537_, 3, v_l_1312_);
lean_ctor_set(v_reuseFailAlloc_1537_, 4, v_l_1465_);
v___x_1524_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
v_isSharedCheck_1531_ = !lean_is_exclusive(v_l_1312_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; 
v_unused_1532_ = lean_ctor_get(v_l_1312_, 4);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_l_1312_, 3);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_l_1312_, 2);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_l_1312_, 1);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_l_1312_, 0);
lean_dec(v_unused_1536_);
v___x_1526_ = v_l_1312_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_dec(v_l_1312_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 4, v_r_1466_);
lean_ctor_set(v___x_1526_, 3, v___x_1524_);
lean_ctor_set(v___x_1526_, 2, v_v_1464_);
lean_ctor_set(v___x_1526_, 1, v_k_1463_);
lean_ctor_set(v___x_1526_, 0, v___x_1521_);
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1463_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1464_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_r_1466_);
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
}
else
{
lean_object* v_l_1544_; 
v_l_1544_ = lean_ctor_get(v_impl_1459_, 3);
lean_inc(v_l_1544_);
if (lean_obj_tag(v_l_1544_) == 0)
{
lean_object* v_r_1545_; lean_object* v_k_1546_; lean_object* v_v_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1570_; 
v_r_1545_ = lean_ctor_get(v_impl_1459_, 4);
v_k_1546_ = lean_ctor_get(v_impl_1459_, 1);
v_v_1547_ = lean_ctor_get(v_impl_1459_, 2);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_impl_1459_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; lean_object* v_unused_1572_; 
v_unused_1571_ = lean_ctor_get(v_impl_1459_, 3);
lean_dec(v_unused_1571_);
v_unused_1572_ = lean_ctor_get(v_impl_1459_, 0);
lean_dec(v_unused_1572_);
v___x_1549_ = v_impl_1459_;
v_isShared_1550_ = v_isSharedCheck_1570_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_r_1545_);
lean_inc(v_v_1547_);
lean_inc(v_k_1546_);
lean_dec(v_impl_1459_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1570_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_k_1551_; lean_object* v_v_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1566_; 
v_k_1551_ = lean_ctor_get(v_l_1544_, 1);
v_v_1552_ = lean_ctor_get(v_l_1544_, 2);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_l_1544_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; lean_object* v_unused_1568_; lean_object* v_unused_1569_; 
v_unused_1567_ = lean_ctor_get(v_l_1544_, 4);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v_l_1544_, 3);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_l_1544_, 0);
lean_dec(v_unused_1569_);
v___x_1554_ = v_l_1544_;
v_isShared_1555_ = v_isSharedCheck_1566_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_v_1552_);
lean_inc(v_k_1551_);
lean_dec(v_l_1544_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1566_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1545_, 2);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 4, v_r_1545_);
lean_ctor_set(v___x_1554_, 3, v_r_1545_);
lean_ctor_set(v___x_1554_, 2, v_v_1311_);
lean_ctor_set(v___x_1554_, 1, v_k_1310_);
lean_ctor_set(v___x_1554_, 0, v___x_1460_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_r_1545_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_r_1545_);
v___x_1558_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
lean_inc(v_r_1545_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 3, v_r_1545_);
lean_ctor_set(v___x_1549_, 0, v___x_1460_);
v___x_1560_ = v___x_1549_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_k_1546_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_v_1547_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_r_1545_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_r_1545_);
v___x_1560_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v___x_1560_);
lean_ctor_set(v___x_1315_, 3, v___x_1558_);
lean_ctor_set(v___x_1315_, 2, v_v_1552_);
lean_ctor_set(v___x_1315_, 1, v_k_1551_);
lean_ctor_set(v___x_1315_, 0, v___x_1556_);
v___x_1562_ = v___x_1315_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_k_1551_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_v_1552_);
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1563_, 4, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
}
else
{
lean_object* v_r_1573_; 
v_r_1573_ = lean_ctor_get(v_impl_1459_, 4);
lean_inc(v_r_1573_);
if (lean_obj_tag(v_r_1573_) == 0)
{
lean_object* v_k_1574_; lean_object* v_v_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1586_; 
v_k_1574_ = lean_ctor_get(v_impl_1459_, 1);
v_v_1575_ = lean_ctor_get(v_impl_1459_, 2);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_impl_1459_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; lean_object* v_unused_1588_; lean_object* v_unused_1589_; 
v_unused_1587_ = lean_ctor_get(v_impl_1459_, 4);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_impl_1459_, 3);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_impl_1459_, 0);
lean_dec(v_unused_1589_);
v___x_1577_ = v_impl_1459_;
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_v_1575_);
lean_inc(v_k_1574_);
lean_dec(v_impl_1459_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_unsigned_to_nat(3u);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 4, v_l_1544_);
lean_ctor_set(v___x_1577_, 2, v_v_1311_);
lean_ctor_set(v___x_1577_, 1, v_k_1310_);
lean_ctor_set(v___x_1577_, 0, v___x_1460_);
v___x_1581_ = v___x_1577_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_l_1544_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_l_1544_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v_r_1573_);
lean_ctor_set(v___x_1315_, 3, v___x_1581_);
lean_ctor_set(v___x_1315_, 2, v_v_1575_);
lean_ctor_set(v___x_1315_, 1, v_k_1574_);
lean_ctor_set(v___x_1315_, 0, v___x_1579_);
v___x_1583_ = v___x_1315_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_k_1574_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_v_1575_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v_r_1573_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1590_ = lean_unsigned_to_nat(2u);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v_impl_1459_);
lean_ctor_set(v___x_1315_, 3, v_r_1573_);
lean_ctor_set(v___x_1315_, 0, v___x_1590_);
v___x_1592_ = v___x_1315_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_r_1573_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_impl_1459_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
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
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec_ref(v_cmp_1305_);
v___x_1595_ = lean_unsigned_to_nat(1u);
v___x_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v_k_1306_);
lean_ctor_set(v___x_1596_, 2, v_v_1307_);
lean_ctor_set(v___x_1596_, 3, v_t_1308_);
lean_ctor_set(v___x_1596_, 4, v_t_1308_);
return v___x_1596_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(lean_object* v_cmp_1597_, lean_object* v_k_1598_, lean_object* v_t_1599_){
_start:
{
if (lean_obj_tag(v_t_1599_) == 0)
{
lean_object* v_k_1600_; lean_object* v_l_1601_; lean_object* v_r_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v_k_1600_ = lean_ctor_get(v_t_1599_, 1);
lean_inc(v_k_1600_);
v_l_1601_ = lean_ctor_get(v_t_1599_, 3);
lean_inc(v_l_1601_);
v_r_1602_ = lean_ctor_get(v_t_1599_, 4);
lean_inc(v_r_1602_);
lean_dec_ref(v_t_1599_);
lean_inc_ref(v_cmp_1597_);
lean_inc(v_k_1598_);
v___x_1603_ = lean_apply_2(v_cmp_1597_, v_k_1598_, v_k_1600_);
v___x_1604_ = lean_unbox(v___x_1603_);
switch(v___x_1604_)
{
case 0:
{
lean_dec(v_r_1602_);
v_t_1599_ = v_l_1601_;
goto _start;
}
case 1:
{
uint8_t v___x_1606_; 
lean_dec(v_r_1602_);
lean_dec(v_l_1601_);
lean_dec(v_k_1598_);
lean_dec_ref(v_cmp_1597_);
v___x_1606_ = 1;
return v___x_1606_;
}
default: 
{
lean_dec(v_l_1601_);
v_t_1599_ = v_r_1602_;
goto _start;
}
}
}
else
{
uint8_t v___x_1608_; 
lean_dec(v_k_1598_);
lean_dec_ref(v_cmp_1597_);
v___x_1608_ = 0;
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg___boxed(lean_object* v_cmp_1609_, lean_object* v_k_1610_, lean_object* v_t_1611_){
_start:
{
uint8_t v_res_1612_; lean_object* v_r_1613_; 
v_res_1612_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1609_, v_k_1610_, v_t_1611_);
v_r_1613_ = lean_box(v_res_1612_);
return v_r_1613_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(lean_object* v_cmp_1614_, lean_object* v_as_x27_1615_, lean_object* v_b_1616_){
_start:
{
if (lean_obj_tag(v_as_x27_1615_) == 0)
{
lean_dec_ref(v_cmp_1614_);
return v_b_1616_;
}
else
{
lean_object* v_head_1617_; lean_object* v_tail_1618_; uint8_t v___x_1619_; 
v_head_1617_ = lean_ctor_get(v_as_x27_1615_, 0);
lean_inc(v_head_1617_);
v_tail_1618_ = lean_ctor_get(v_as_x27_1615_, 1);
lean_inc(v_tail_1618_);
lean_dec_ref(v_as_x27_1615_);
lean_inc(v_b_1616_);
lean_inc(v_head_1617_);
lean_inc_ref(v_cmp_1614_);
v___x_1619_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1614_, v_head_1617_, v_b_1616_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_box(0);
lean_inc_ref(v_cmp_1614_);
v___x_1621_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1614_, v_head_1617_, v___x_1620_, v_b_1616_);
v_as_x27_1615_ = v_tail_1618_;
v_b_1616_ = v___x_1621_;
goto _start;
}
else
{
lean_dec(v_head_1617_);
v_as_x27_1615_ = v_tail_1618_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___redArg(lean_object* v_l_1624_, lean_object* v_cmp_1625_){
_start:
{
lean_object* v_r_1626_; lean_object* v___x_1627_; 
v_r_1626_ = lean_box(1);
v___x_1627_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1625_, v_l_1624_, v_r_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList(lean_object* v_00_u03b1_1628_, lean_object* v_l_1629_, lean_object* v_cmp_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Std_ExtTreeSet_ofList___redArg(v_l_1629_, v_cmp_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(lean_object* v_00_u03b1_1632_, lean_object* v_cmp_1633_, lean_object* v_00_u03b2_1634_, lean_object* v_k_1635_, lean_object* v_t_1636_){
_start:
{
uint8_t v___x_1637_; 
v___x_1637_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1633_, v_k_1635_, v_t_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___boxed(lean_object* v_00_u03b1_1638_, lean_object* v_cmp_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_k_1641_, lean_object* v_t_1642_){
_start:
{
uint8_t v_res_1643_; lean_object* v_r_1644_; 
v_res_1643_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(v_00_u03b1_1638_, v_cmp_1639_, v_00_u03b2_1640_, v_k_1641_, v_t_1642_);
v_r_1644_ = lean_box(v_res_1643_);
return v_r_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1(lean_object* v_00_u03b1_1645_, lean_object* v_cmp_1646_, lean_object* v_00_u03b2_1647_, lean_object* v_k_1648_, lean_object* v_v_1649_, lean_object* v_t_1650_, lean_object* v_hl_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1646_, v_k_1648_, v_v_1649_, v_t_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(lean_object* v_00_u03b1_1653_, lean_object* v_cmp_1654_, lean_object* v_as_1655_, lean_object* v_as_x27_1656_, lean_object* v_b_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1654_, v_as_x27_1656_, v_b_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___boxed(lean_object* v_00_u03b1_1660_, lean_object* v_cmp_1661_, lean_object* v_as_1662_, lean_object* v_as_x27_1663_, lean_object* v_b_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(v_00_u03b1_1660_, v_cmp_1661_, v_as_1662_, v_as_x27_1663_, v_b_1664_, v_a_1665_);
lean_dec(v_as_1662_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg___lam__0(lean_object* v_l_1667_, lean_object* v_k_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_array_push(v_l_1667_, v_k_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg(lean_object* v_t_1672_){
_start:
{
lean_object* v___f_1673_; lean_object* v___y_1675_; 
v___f_1673_ = ((lean_object*)(l_Std_ExtTreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1672_) == 0)
{
lean_object* v_size_1678_; 
v_size_1678_ = lean_ctor_get(v_t_1672_, 0);
lean_inc(v_size_1678_);
v___y_1675_ = v_size_1678_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_unsigned_to_nat(0u);
v___y_1675_ = v___x_1679_;
goto v___jp_1674_;
}
v___jp_1674_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_mk_empty_array_with_capacity(v___y_1675_);
lean_dec(v___y_1675_);
v___x_1677_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1673_, v___x_1676_, v_t_1672_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray(lean_object* v_00_u03b1_1680_, lean_object* v_cmp_1681_, lean_object* v_inst_1682_, lean_object* v_t_1683_){
_start:
{
lean_object* v___f_1684_; lean_object* v___y_1686_; 
v___f_1684_ = ((lean_object*)(l_Std_ExtTreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1683_) == 0)
{
lean_object* v_size_1689_; 
v_size_1689_ = lean_ctor_get(v_t_1683_, 0);
lean_inc(v_size_1689_);
v___y_1686_ = v_size_1689_;
goto v___jp_1685_;
}
else
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_unsigned_to_nat(0u);
v___y_1686_ = v___x_1690_;
goto v___jp_1685_;
}
v___jp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_mk_empty_array_with_capacity(v___y_1686_);
lean_dec(v___y_1686_);
v___x_1688_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1684_, v___x_1687_, v_t_1683_);
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___boxed(lean_object* v_00_u03b1_1691_, lean_object* v_cmp_1692_, lean_object* v_inst_1693_, lean_object* v_t_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Std_ExtTreeSet_toArray(v_00_u03b1_1691_, v_cmp_1692_, v_inst_1693_, v_t_1694_);
lean_dec_ref(v_cmp_1692_);
return v_res_1695_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__26, &l_Std_ExtTreeSet___auto__1___closed__26_once, _init_l_Std_ExtTreeSet___auto__1___closed__26);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(lean_object* v_cmp_1697_, lean_object* v_as_1698_, size_t v_sz_1699_, size_t v_i_1700_, lean_object* v_b_1701_){
_start:
{
lean_object* v___y_1703_; uint8_t v___x_1707_; 
v___x_1707_ = lean_usize_dec_lt(v_i_1700_, v_sz_1699_);
if (v___x_1707_ == 0)
{
lean_dec_ref(v_cmp_1697_);
return v_b_1701_;
}
else
{
lean_object* v_a_1708_; uint8_t v___x_1709_; 
v_a_1708_ = lean_array_uget_borrowed(v_as_1698_, v_i_1700_);
lean_inc(v_b_1701_);
lean_inc(v_a_1708_);
lean_inc_ref(v_cmp_1697_);
v___x_1709_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1697_, v_a_1708_, v_b_1701_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_box(0);
lean_inc(v_a_1708_);
lean_inc_ref(v_cmp_1697_);
v___x_1711_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1697_, v_a_1708_, v___x_1710_, v_b_1701_);
v___y_1703_ = v___x_1711_;
goto v___jp_1702_;
}
else
{
v___y_1703_ = v_b_1701_;
goto v___jp_1702_;
}
}
v___jp_1702_:
{
size_t v___x_1704_; size_t v___x_1705_; 
v___x_1704_ = ((size_t)1ULL);
v___x_1705_ = lean_usize_add(v_i_1700_, v___x_1704_);
v_i_1700_ = v___x_1705_;
v_b_1701_ = v___y_1703_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg___boxed(lean_object* v_cmp_1712_, lean_object* v_as_1713_, lean_object* v_sz_1714_, lean_object* v_i_1715_, lean_object* v_b_1716_){
_start:
{
size_t v_sz_boxed_1717_; size_t v_i_boxed_1718_; lean_object* v_res_1719_; 
v_sz_boxed_1717_ = lean_unbox_usize(v_sz_1714_);
lean_dec(v_sz_1714_);
v_i_boxed_1718_ = lean_unbox_usize(v_i_1715_);
lean_dec(v_i_1715_);
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1712_, v_as_1713_, v_sz_boxed_1717_, v_i_boxed_1718_, v_b_1716_);
lean_dec_ref(v_as_1713_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg(lean_object* v_a_1720_, lean_object* v_cmp_1721_){
_start:
{
lean_object* v_r_1722_; size_t v_sz_1723_; size_t v___x_1724_; lean_object* v___x_1725_; 
v_r_1722_ = lean_box(1);
v_sz_1723_ = lean_array_size(v_a_1720_);
v___x_1724_ = ((size_t)0ULL);
v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1721_, v_a_1720_, v_sz_1723_, v___x_1724_, v_r_1722_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg___boxed(lean_object* v_a_1726_, lean_object* v_cmp_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_1726_, v_cmp_1727_);
lean_dec_ref(v_a_1726_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray(lean_object* v_00_u03b1_1729_, lean_object* v_a_1730_, lean_object* v_cmp_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_1730_, v_cmp_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___boxed(lean_object* v_00_u03b1_1733_, lean_object* v_a_1734_, lean_object* v_cmp_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Std_ExtTreeSet_ofArray(v_00_u03b1_1733_, v_a_1734_, v_cmp_1735_);
lean_dec_ref(v_a_1734_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(lean_object* v_00_u03b1_1737_, lean_object* v_cmp_1738_, lean_object* v_as_1739_, size_t v_sz_1740_, size_t v_i_1741_, lean_object* v_b_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1738_, v_as_1739_, v_sz_1740_, v_i_1741_, v_b_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___boxed(lean_object* v_00_u03b1_1744_, lean_object* v_cmp_1745_, lean_object* v_as_1746_, lean_object* v_sz_1747_, lean_object* v_i_1748_, lean_object* v_b_1749_){
_start:
{
size_t v_sz_boxed_1750_; size_t v_i_boxed_1751_; lean_object* v_res_1752_; 
v_sz_boxed_1750_ = lean_unbox_usize(v_sz_1747_);
lean_dec(v_sz_1747_);
v_i_boxed_1751_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(v_00_u03b1_1744_, v_cmp_1745_, v_as_1746_, v_sz_boxed_1750_, v_i_boxed_1751_, v_b_1749_);
lean_dec_ref(v_as_1746_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0(lean_object* v_b_u2082_1755_, lean_object* v_x_1756_){
_start:
{
if (lean_obj_tag(v_x_1756_) == 0)
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_b_u2082_1755_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = ((lean_object*)(l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0));
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1759_, lean_object* v_x_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Std_ExtTreeSet_merge___redArg___lam__0(v_b_u2082_1759_, v_x_1760_);
lean_dec(v_x_1760_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__1(lean_object* v_cmp_1762_, lean_object* v_t_1763_, lean_object* v_a_1764_, lean_object* v_b_u2082_1765_){
_start:
{
lean_object* v___f_1766_; lean_object* v___x_1767_; 
v___f_1766_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1766_, 0, v_b_u2082_1765_);
v___x_1767_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_1762_, v_a_1764_, v___f_1766_, v_t_1763_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg(lean_object* v_cmp_1768_, lean_object* v_t_u2081_1769_, lean_object* v_t_u2082_1770_){
_start:
{
lean_object* v___f_1771_; lean_object* v___x_1772_; 
v___f_1771_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1771_, 0, v_cmp_1768_);
v___x_1772_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1771_, v_t_u2081_1769_, v_t_u2082_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge(lean_object* v_00_u03b1_1773_, lean_object* v_cmp_1774_, lean_object* v_inst_1775_, lean_object* v_t_u2081_1776_, lean_object* v_t_u2082_1777_){
_start:
{
lean_object* v___f_1778_; lean_object* v___x_1779_; 
v___f_1778_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1778_, 0, v_cmp_1774_);
v___x_1779_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1778_, v_t_u2081_1776_, v_t_u2082_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg___lam__0(lean_object* v_cmp_1780_, lean_object* v_a_1781_, lean_object* v_____s_1782_){
_start:
{
uint8_t v___x_1783_; 
lean_inc(v_____s_1782_);
lean_inc(v_a_1781_);
lean_inc_ref(v_cmp_1780_);
v___x_1783_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1780_, v_a_1781_, v_____s_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_box(0);
v___x_1785_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1780_, v_a_1781_, v___x_1784_, v_____s_1782_);
v___x_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
return v___x_1786_;
}
else
{
lean_object* v___x_1787_; 
lean_dec(v_a_1781_);
lean_dec_ref(v_cmp_1780_);
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v_____s_1782_);
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg(lean_object* v_cmp_1788_, lean_object* v_inst_1789_, lean_object* v_t_1790_, lean_object* v_l_1791_){
_start:
{
lean_object* v___f_1792_; lean_object* v___x_1793_; 
v___f_1792_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1792_, 0, v_cmp_1788_);
v___x_1793_ = lean_apply_4(v_inst_1789_, lean_box(0), v_l_1791_, v_t_1790_, v___f_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany(lean_object* v_00_u03b1_1794_, lean_object* v_cmp_1795_, lean_object* v_inst_1796_, lean_object* v_00_u03c1_1797_, lean_object* v_inst_1798_, lean_object* v_t_1799_, lean_object* v_l_1800_){
_start:
{
lean_object* v___f_1801_; lean_object* v___x_1802_; 
v___f_1801_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1801_, 0, v_cmp_1795_);
v___x_1802_ = lean_apply_4(v_inst_1798_, lean_box(0), v_l_1800_, v_t_1799_, v___f_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union___redArg(lean_object* v_cmp_1803_, lean_object* v_t_u2081_1804_, lean_object* v_t_u2082_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1803_, v_t_u2081_1804_, v_t_u2082_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union(lean_object* v_00_u03b1_1807_, lean_object* v_cmp_1808_, lean_object* v_inst_1809_, lean_object* v_t_u2081_1810_, lean_object* v_t_u2082_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1808_, v_t_u2081_1810_, v_t_u2082_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp___redArg(lean_object* v_cmp_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_union), 5, 3);
lean_closure_set(v___x_1814_, 0, lean_box(0));
lean_closure_set(v___x_1814_, 1, v_cmp_1813_);
lean_closure_set(v___x_1814_, 2, lean_box(0));
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp(lean_object* v_00_u03b1_1815_, lean_object* v_cmp_1816_, lean_object* v_inst_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_union), 5, 3);
lean_closure_set(v___x_1818_, 0, lean_box(0));
lean_closure_set(v___x_1818_, 1, v_cmp_1816_);
lean_closure_set(v___x_1818_, 2, lean_box(0));
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter___redArg(lean_object* v_cmp_1819_, lean_object* v_t_u2081_1820_, lean_object* v_t_u2082_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1819_, v_t_u2081_1820_, v_t_u2082_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter(lean_object* v_00_u03b1_1823_, lean_object* v_cmp_1824_, lean_object* v_inst_1825_, lean_object* v_t_u2081_1826_, lean_object* v_t_u2082_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1824_, v_t_u2081_1826_, v_t_u2082_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp___redArg(lean_object* v_cmp_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_inter), 5, 3);
lean_closure_set(v___x_1830_, 0, lean_box(0));
lean_closure_set(v___x_1830_, 1, v_cmp_1829_);
lean_closure_set(v___x_1830_, 2, lean_box(0));
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp(lean_object* v_00_u03b1_1831_, lean_object* v_cmp_1832_, lean_object* v_inst_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_inter), 5, 3);
lean_closure_set(v___x_1834_, 0, lean_box(0));
lean_closure_set(v___x_1834_, 1, v_cmp_1832_);
lean_closure_set(v___x_1834_, 2, lean_box(0));
return v___x_1834_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___f_1836_; 
v___x_1835_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1836_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1836_, 0, v___x_1835_);
return v___f_1836_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(lean_object* v_cmp_1837_, lean_object* v_m_u2081_1838_, lean_object* v_m_u2082_1839_){
_start:
{
lean_object* v___f_1840_; uint8_t v___x_1841_; 
v___f_1840_ = lean_obj_once(&l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0, &l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once, _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0);
v___x_1841_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_1837_, v___f_1840_, v_m_u2081_1838_, v_m_u2082_1839_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_1842_, lean_object* v_m_u2081_1843_, lean_object* v_m_u2082_1844_){
_start:
{
uint8_t v_res_1845_; lean_object* v_r_1846_; 
v_res_1845_ = l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(v_cmp_1842_, v_m_u2081_1843_, v_m_u2082_1844_);
v_r_1846_ = lean_box(v_res_1845_);
return v_r_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg(lean_object* v_cmp_1847_){
_start:
{
lean_object* v___f_1848_; 
v___f_1848_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1848_, 0, v_cmp_1847_);
return v___f_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp(lean_object* v_00_u03b1_1849_, lean_object* v_cmp_1850_, lean_object* v_inst_1851_){
_start:
{
lean_object* v___f_1852_; 
v___f_1852_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1852_, 0, v_cmp_1850_);
return v___f_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff___redArg(lean_object* v_cmp_1853_, lean_object* v_t_u2081_1854_, lean_object* v_t_u2082_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1853_, v_t_u2081_1854_, v_t_u2082_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff(lean_object* v_00_u03b1_1857_, lean_object* v_cmp_1858_, lean_object* v_inst_1859_, lean_object* v_t_u2081_1860_, lean_object* v_t_u2082_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1858_, v_t_u2081_1860_, v_t_u2082_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp___redArg(lean_object* v_cmp_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_diff), 5, 3);
lean_closure_set(v___x_1864_, 0, lean_box(0));
lean_closure_set(v___x_1864_, 1, v_cmp_1863_);
lean_closure_set(v___x_1864_, 2, lean_box(0));
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp(lean_object* v_00_u03b1_1865_, lean_object* v_cmp_1866_, lean_object* v_inst_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_diff), 5, 3);
lean_closure_set(v___x_1868_, 0, lean_box(0));
lean_closure_set(v___x_1868_, 1, v_cmp_1866_);
lean_closure_set(v___x_1868_, 2, lean_box(0));
return v___x_1868_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(lean_object* v_cmp_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_){
_start:
{
lean_object* v___f_1872_; uint8_t v___x_1873_; 
v___f_1872_ = lean_obj_once(&l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0, &l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once, _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0);
v___x_1873_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_1869_, v___f_1872_, v_x_1870_, v_x_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg___boxed(lean_object* v_cmp_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
uint8_t v_res_1877_; lean_object* v_r_1878_; 
v_res_1877_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_1874_, v_x_1875_, v_x_1876_);
v_r_1878_ = lean_box(v_res_1877_);
return v_r_1878_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(lean_object* v_00_u03b1_1879_, lean_object* v_cmp_1880_, lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
uint8_t v___x_1885_; 
v___x_1885_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_1880_, v_x_1883_, v_x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___boxed(lean_object* v_00_u03b1_1886_, lean_object* v_cmp_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
uint8_t v_res_1892_; lean_object* v_r_1893_; 
v_res_1892_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(v_00_u03b1_1886_, v_cmp_1887_, v_inst_1888_, v_inst_1889_, v_x_1890_, v_x_1891_);
v_r_1893_ = lean_box(v_res_1892_);
return v_r_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg___lam__0(lean_object* v_cmp_1894_, lean_object* v_a_1895_, lean_object* v_____s_1896_){
_start:
{
lean_object* v_acc_1897_; lean_object* v___x_1898_; 
v_acc_1897_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_1894_, v_a_1895_, v_____s_1896_);
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_acc_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg(lean_object* v_cmp_1899_, lean_object* v_inst_1900_, lean_object* v_t_1901_, lean_object* v_l_1902_){
_start:
{
lean_object* v___f_1903_; lean_object* v___x_1904_; 
v___f_1903_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1903_, 0, v_cmp_1899_);
v___x_1904_ = lean_apply_4(v_inst_1900_, lean_box(0), v_l_1902_, v_t_1901_, v___f_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany(lean_object* v_00_u03b1_1905_, lean_object* v_cmp_1906_, lean_object* v_inst_1907_, lean_object* v_00_u03c1_1908_, lean_object* v_inst_1909_, lean_object* v_t_1910_, lean_object* v_l_1911_){
_start:
{
lean_object* v___f_1912_; lean_object* v___x_1913_; 
v___f_1912_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1912_, 0, v_cmp_1906_);
v___x_1913_ = lean_apply_4(v_inst_1909_, lean_box(0), v_l_1911_, v_t_1910_, v___f_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_1917_, lean_object* v_inst_1918_, lean_object* v_m_1919_, lean_object* v_prec_1920_){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1921_ = ((lean_object*)(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_1922_ = lean_box(0);
v___x_1923_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1924_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1923_, v___f_1917_, v___x_1922_, v_m_1919_);
v___x_1925_ = l_List_repr___redArg(v_inst_1918_, v___x_1924_);
v___x_1926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1921_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = l_Repr_addAppParen(v___x_1926_, v_prec_1920_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_1928_, lean_object* v_inst_1929_, lean_object* v_m_1930_, lean_object* v_prec_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(v___f_1928_, v_inst_1929_, v_m_1930_, v_prec_1931_);
lean_dec(v_prec_1931_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg(lean_object* v_inst_1933_){
_start:
{
lean_object* v___f_1934_; lean_object* v___f_1935_; 
v___f_1934_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___f_1935_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1935_, 0, v___f_1934_);
lean_closure_set(v___f_1935_, 1, v_inst_1933_);
return v___f_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp(lean_object* v_00_u03b1_1936_, lean_object* v_cmp_1937_, lean_object* v_inst_1938_, lean_object* v_inst_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg(v_inst_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_1941_, lean_object* v_cmp_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Std_ExtTreeSet_instReprOfTransCmp(v_00_u03b1_1941_, v_cmp_1942_, v_inst_1943_, v_inst_1944_);
lean_dec_ref(v_cmp_1942_);
return v_res_1945_;
}
}
lean_object* runtime_initialize_Std_Data_ExtTreeMap_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtTreeSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
