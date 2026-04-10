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
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___redArg___boxed(lean_object* v_cmp_271_, lean_object* v_inst_272_, lean_object* v_t_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_ExtTreeSet_get_x21___redArg(v_cmp_271_, v_inst_272_, v_t_273_, v_a_274_);
lean_dec(v_inst_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21(lean_object* v_00_u03b1_276_, lean_object* v_cmp_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_t_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_277_, v_t_280_, v_a_281_, v_inst_279_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___boxed(lean_object* v_00_u03b1_283_, lean_object* v_cmp_284_, lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_t_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_ExtTreeSet_get_x21(v_00_u03b1_283_, v_cmp_284_, v_inst_285_, v_inst_286_, v_t_287_, v_a_288_);
lean_dec(v_inst_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg(lean_object* v_cmp_290_, lean_object* v_t_291_, lean_object* v_a_292_, lean_object* v_fallback_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_290_, v_t_291_, v_a_292_, v_fallback_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg___boxed(lean_object* v_cmp_295_, lean_object* v_t_296_, lean_object* v_a_297_, lean_object* v_fallback_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Std_ExtTreeSet_getD___redArg(v_cmp_295_, v_t_296_, v_a_297_, v_fallback_298_);
lean_dec(v_fallback_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD(lean_object* v_00_u03b1_300_, lean_object* v_cmp_301_, lean_object* v_inst_302_, lean_object* v_t_303_, lean_object* v_a_304_, lean_object* v_fallback_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_301_, v_t_303_, v_a_304_, v_fallback_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___boxed(lean_object* v_00_u03b1_307_, lean_object* v_cmp_308_, lean_object* v_inst_309_, lean_object* v_t_310_, lean_object* v_a_311_, lean_object* v_fallback_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_ExtTreeSet_getD(v_00_u03b1_307_, v_cmp_308_, v_inst_309_, v_t_310_, v_a_311_, v_fallback_312_);
lean_dec(v_fallback_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg(lean_object* v_t_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg___boxed(lean_object* v_t_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_ExtTreeSet_min_x3f___redArg(v_t_316_);
lean_dec(v_t_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f(lean_object* v_00_u03b1_318_, lean_object* v_cmp_319_, lean_object* v_inst_320_, lean_object* v_t_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___boxed(lean_object* v_00_u03b1_323_, lean_object* v_cmp_324_, lean_object* v_inst_325_, lean_object* v_t_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_ExtTreeSet_min_x3f(v_00_u03b1_323_, v_cmp_324_, v_inst_325_, v_t_326_);
lean_dec(v_t_326_);
lean_dec_ref(v_cmp_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg(lean_object* v_t_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg___boxed(lean_object* v_t_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_ExtTreeSet_min___redArg(v_t_330_);
lean_dec(v_t_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min(lean_object* v_00_u03b1_332_, lean_object* v_cmp_333_, lean_object* v_inst_334_, lean_object* v_t_335_, lean_object* v_h_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___boxed(lean_object* v_00_u03b1_338_, lean_object* v_cmp_339_, lean_object* v_inst_340_, lean_object* v_t_341_, lean_object* v_h_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_ExtTreeSet_min(v_00_u03b1_338_, v_cmp_339_, v_inst_340_, v_t_341_, v_h_342_);
lean_dec(v_t_341_);
lean_dec_ref(v_cmp_339_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg(lean_object* v_inst_344_, lean_object* v_t_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_344_, v_t_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg___boxed(lean_object* v_inst_347_, lean_object* v_t_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_ExtTreeSet_min_x21___redArg(v_inst_347_, v_t_348_);
lean_dec(v_t_348_);
lean_dec(v_inst_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21(lean_object* v_00_u03b1_350_, lean_object* v_cmp_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_t_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_353_, v_t_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___boxed(lean_object* v_00_u03b1_356_, lean_object* v_cmp_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_t_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_ExtTreeSet_min_x21(v_00_u03b1_356_, v_cmp_357_, v_inst_358_, v_inst_359_, v_t_360_);
lean_dec(v_t_360_);
lean_dec(v_inst_359_);
lean_dec_ref(v_cmp_357_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg(lean_object* v_t_362_, lean_object* v_fallback_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_362_, v_fallback_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg___boxed(lean_object* v_t_365_, lean_object* v_fallback_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_ExtTreeSet_minD___redArg(v_t_365_, v_fallback_366_);
lean_dec(v_fallback_366_);
lean_dec(v_t_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD(lean_object* v_00_u03b1_368_, lean_object* v_cmp_369_, lean_object* v_inst_370_, lean_object* v_t_371_, lean_object* v_fallback_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_371_, v_fallback_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___boxed(lean_object* v_00_u03b1_374_, lean_object* v_cmp_375_, lean_object* v_inst_376_, lean_object* v_t_377_, lean_object* v_fallback_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_ExtTreeSet_minD(v_00_u03b1_374_, v_cmp_375_, v_inst_376_, v_t_377_, v_fallback_378_);
lean_dec(v_fallback_378_);
lean_dec(v_t_377_);
lean_dec_ref(v_cmp_375_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg(lean_object* v_t_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg___boxed(lean_object* v_t_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_ExtTreeSet_max_x3f___redArg(v_t_382_);
lean_dec(v_t_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f(lean_object* v_00_u03b1_384_, lean_object* v_cmp_385_, lean_object* v_inst_386_, lean_object* v_t_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___boxed(lean_object* v_00_u03b1_389_, lean_object* v_cmp_390_, lean_object* v_inst_391_, lean_object* v_t_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_ExtTreeSet_max_x3f(v_00_u03b1_389_, v_cmp_390_, v_inst_391_, v_t_392_);
lean_dec(v_t_392_);
lean_dec_ref(v_cmp_390_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg(lean_object* v_t_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg___boxed(lean_object* v_t_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_ExtTreeSet_max___redArg(v_t_396_);
lean_dec(v_t_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max(lean_object* v_00_u03b1_398_, lean_object* v_cmp_399_, lean_object* v_inst_400_, lean_object* v_t_401_, lean_object* v_h_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___boxed(lean_object* v_00_u03b1_404_, lean_object* v_cmp_405_, lean_object* v_inst_406_, lean_object* v_t_407_, lean_object* v_h_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_ExtTreeSet_max(v_00_u03b1_404_, v_cmp_405_, v_inst_406_, v_t_407_, v_h_408_);
lean_dec(v_t_407_);
lean_dec_ref(v_cmp_405_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg(lean_object* v_inst_410_, lean_object* v_t_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_410_, v_t_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg___boxed(lean_object* v_inst_413_, lean_object* v_t_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_ExtTreeSet_max_x21___redArg(v_inst_413_, v_t_414_);
lean_dec(v_t_414_);
lean_dec(v_inst_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21(lean_object* v_00_u03b1_416_, lean_object* v_cmp_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_t_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_419_, v_t_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___boxed(lean_object* v_00_u03b1_422_, lean_object* v_cmp_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_t_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_ExtTreeSet_max_x21(v_00_u03b1_422_, v_cmp_423_, v_inst_424_, v_inst_425_, v_t_426_);
lean_dec(v_t_426_);
lean_dec(v_inst_425_);
lean_dec_ref(v_cmp_423_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg(lean_object* v_t_428_, lean_object* v_fallback_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_428_, v_fallback_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg___boxed(lean_object* v_t_431_, lean_object* v_fallback_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_ExtTreeSet_maxD___redArg(v_t_431_, v_fallback_432_);
lean_dec(v_fallback_432_);
lean_dec(v_t_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD(lean_object* v_00_u03b1_434_, lean_object* v_cmp_435_, lean_object* v_inst_436_, lean_object* v_t_437_, lean_object* v_fallback_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_437_, v_fallback_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___boxed(lean_object* v_00_u03b1_440_, lean_object* v_cmp_441_, lean_object* v_inst_442_, lean_object* v_t_443_, lean_object* v_fallback_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_ExtTreeSet_maxD(v_00_u03b1_440_, v_cmp_441_, v_inst_442_, v_t_443_, v_fallback_444_);
lean_dec(v_fallback_444_);
lean_dec(v_t_443_);
lean_dec_ref(v_cmp_441_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg(lean_object* v_t_446_, lean_object* v_n_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_446_, v_n_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg___boxed(lean_object* v_t_449_, lean_object* v_n_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_ExtTreeSet_atIdx_x3f___redArg(v_t_449_, v_n_450_);
lean_dec(v_t_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f(lean_object* v_00_u03b1_452_, lean_object* v_cmp_453_, lean_object* v_inst_454_, lean_object* v_t_455_, lean_object* v_n_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_455_, v_n_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___boxed(lean_object* v_00_u03b1_458_, lean_object* v_cmp_459_, lean_object* v_inst_460_, lean_object* v_t_461_, lean_object* v_n_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Std_ExtTreeSet_atIdx_x3f(v_00_u03b1_458_, v_cmp_459_, v_inst_460_, v_t_461_, v_n_462_);
lean_dec(v_t_461_);
lean_dec_ref(v_cmp_459_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg(lean_object* v_t_464_, lean_object* v_n_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_464_, v_n_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg___boxed(lean_object* v_t_467_, lean_object* v_n_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_ExtTreeSet_atIdx___redArg(v_t_467_, v_n_468_);
lean_dec(v_t_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx(lean_object* v_00_u03b1_470_, lean_object* v_cmp_471_, lean_object* v_inst_472_, lean_object* v_t_473_, lean_object* v_n_474_, lean_object* v_h_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_473_, v_n_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___boxed(lean_object* v_00_u03b1_477_, lean_object* v_cmp_478_, lean_object* v_inst_479_, lean_object* v_t_480_, lean_object* v_n_481_, lean_object* v_h_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_ExtTreeSet_atIdx(v_00_u03b1_477_, v_cmp_478_, v_inst_479_, v_t_480_, v_n_481_, v_h_482_);
lean_dec(v_t_480_);
lean_dec_ref(v_cmp_478_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg(lean_object* v_inst_484_, lean_object* v_t_485_, lean_object* v_n_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_484_, v_t_485_, v_n_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg___boxed(lean_object* v_inst_488_, lean_object* v_t_489_, lean_object* v_n_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_ExtTreeSet_atIdx_x21___redArg(v_inst_488_, v_t_489_, v_n_490_);
lean_dec(v_t_489_);
lean_dec(v_inst_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21(lean_object* v_00_u03b1_492_, lean_object* v_cmp_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_t_496_, lean_object* v_n_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_495_, v_t_496_, v_n_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___boxed(lean_object* v_00_u03b1_499_, lean_object* v_cmp_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_t_503_, lean_object* v_n_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_ExtTreeSet_atIdx_x21(v_00_u03b1_499_, v_cmp_500_, v_inst_501_, v_inst_502_, v_t_503_, v_n_504_);
lean_dec(v_t_503_);
lean_dec(v_inst_502_);
lean_dec_ref(v_cmp_500_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg(lean_object* v_t_506_, lean_object* v_n_507_, lean_object* v_fallback_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_506_, v_n_507_, v_fallback_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg___boxed(lean_object* v_t_510_, lean_object* v_n_511_, lean_object* v_fallback_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_ExtTreeSet_atIdxD___redArg(v_t_510_, v_n_511_, v_fallback_512_);
lean_dec(v_fallback_512_);
lean_dec(v_t_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD(lean_object* v_00_u03b1_514_, lean_object* v_cmp_515_, lean_object* v_inst_516_, lean_object* v_t_517_, lean_object* v_n_518_, lean_object* v_fallback_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_517_, v_n_518_, v_fallback_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___boxed(lean_object* v_00_u03b1_521_, lean_object* v_cmp_522_, lean_object* v_inst_523_, lean_object* v_t_524_, lean_object* v_n_525_, lean_object* v_fallback_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_ExtTreeSet_atIdxD(v_00_u03b1_521_, v_cmp_522_, v_inst_523_, v_t_524_, v_n_525_, v_fallback_526_);
lean_dec(v_fallback_526_);
lean_dec(v_t_524_);
lean_dec_ref(v_cmp_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f___redArg(lean_object* v_cmp_528_, lean_object* v_t_529_, lean_object* v_k_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_box(0);
v___x_532_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_528_, v_k_530_, v___x_531_, v_t_529_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f(lean_object* v_00_u03b1_533_, lean_object* v_cmp_534_, lean_object* v_inst_535_, lean_object* v_t_536_, lean_object* v_k_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_box(0);
v___x_539_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_534_, v_k_537_, v___x_538_, v_t_536_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f___redArg(lean_object* v_cmp_540_, lean_object* v_t_541_, lean_object* v_k_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_box(0);
v___x_544_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_540_, v_k_542_, v___x_543_, v_t_541_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f(lean_object* v_00_u03b1_545_, lean_object* v_cmp_546_, lean_object* v_inst_547_, lean_object* v_t_548_, lean_object* v_k_549_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_box(0);
v___x_551_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_546_, v_k_549_, v___x_550_, v_t_548_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f___redArg(lean_object* v_cmp_552_, lean_object* v_t_553_, lean_object* v_k_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_box(0);
v___x_556_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_552_, v_k_554_, v___x_555_, v_t_553_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f(lean_object* v_00_u03b1_557_, lean_object* v_cmp_558_, lean_object* v_inst_559_, lean_object* v_t_560_, lean_object* v_k_561_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_box(0);
v___x_563_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_558_, v_k_561_, v___x_562_, v_t_560_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f___redArg(lean_object* v_cmp_564_, lean_object* v_t_565_, lean_object* v_k_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_box(0);
v___x_568_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_564_, v_k_566_, v___x_567_, v_t_565_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f(lean_object* v_00_u03b1_569_, lean_object* v_cmp_570_, lean_object* v_inst_571_, lean_object* v_t_572_, lean_object* v_k_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_box(0);
v___x_575_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_570_, v_k_573_, v___x_574_, v_t_572_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE___redArg(lean_object* v_cmp_576_, lean_object* v_t_577_, lean_object* v_k_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_576_, v_k_578_, v_t_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE(lean_object* v_00_u03b1_580_, lean_object* v_cmp_581_, lean_object* v_inst_582_, lean_object* v_t_583_, lean_object* v_k_584_, lean_object* v_h_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_581_, v_k_584_, v_t_583_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT___redArg(lean_object* v_cmp_587_, lean_object* v_t_588_, lean_object* v_k_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_587_, v_k_589_, v_t_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT(lean_object* v_00_u03b1_591_, lean_object* v_cmp_592_, lean_object* v_inst_593_, lean_object* v_t_594_, lean_object* v_k_595_, lean_object* v_h_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_592_, v_k_595_, v_t_594_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE___redArg(lean_object* v_cmp_598_, lean_object* v_t_599_, lean_object* v_k_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_598_, v_k_600_, v_t_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE(lean_object* v_00_u03b1_602_, lean_object* v_cmp_603_, lean_object* v_inst_604_, lean_object* v_t_605_, lean_object* v_k_606_, lean_object* v_h_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_603_, v_k_606_, v_t_605_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT___redArg(lean_object* v_cmp_609_, lean_object* v_t_610_, lean_object* v_k_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_609_, v_k_611_, v_t_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT(lean_object* v_00_u03b1_613_, lean_object* v_cmp_614_, lean_object* v_inst_615_, lean_object* v_t_616_, lean_object* v_k_617_, lean_object* v_h_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_614_, v_k_617_, v_t_616_);
return v___x_619_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_623_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__2));
v___x_624_ = lean_unsigned_to_nat(14u);
v___x_625_ = lean_unsigned_to_nat(22u);
v___x_626_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__1));
v___x_627_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__0));
v___x_628_ = l_mkPanicMessageWithDecl(v___x_627_, v___x_626_, v___x_625_, v___x_624_, v___x_623_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___redArg(lean_object* v_cmp_629_, lean_object* v_inst_630_, lean_object* v_t_631_, lean_object* v_k_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_box(0);
v___x_634_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_629_, v_k_632_, v___x_633_, v_t_631_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_636_ = l_panic___redArg(v_inst_630_, v___x_635_);
return v___x_636_;
}
else
{
lean_object* v_val_637_; 
v_val_637_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_val_637_);
lean_dec_ref(v___x_634_);
return v_val_637_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___redArg___boxed(lean_object* v_cmp_638_, lean_object* v_inst_639_, lean_object* v_t_640_, lean_object* v_k_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_ExtTreeSet_getGE_x21___redArg(v_cmp_638_, v_inst_639_, v_t_640_, v_k_641_);
lean_dec(v_inst_639_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21(lean_object* v_00_u03b1_643_, lean_object* v_cmp_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_t_647_, lean_object* v_k_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_box(0);
v___x_650_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_644_, v_k_648_, v___x_649_, v_t_647_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_652_ = l_panic___redArg(v_inst_646_, v___x_651_);
return v___x_652_;
}
else
{
lean_object* v_val_653_; 
v_val_653_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_653_);
lean_dec_ref(v___x_650_);
return v_val_653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___boxed(lean_object* v_00_u03b1_654_, lean_object* v_cmp_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_t_658_, lean_object* v_k_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_ExtTreeSet_getGE_x21(v_00_u03b1_654_, v_cmp_655_, v_inst_656_, v_inst_657_, v_t_658_, v_k_659_);
lean_dec(v_inst_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg(lean_object* v_cmp_661_, lean_object* v_inst_662_, lean_object* v_t_663_, lean_object* v_k_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_box(0);
v___x_666_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_661_, v_k_664_, v___x_665_, v_t_663_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_668_ = l_panic___redArg(v_inst_662_, v___x_667_);
return v___x_668_;
}
else
{
lean_object* v_val_669_; 
v_val_669_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_val_669_);
lean_dec_ref(v___x_666_);
return v_val_669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg___boxed(lean_object* v_cmp_670_, lean_object* v_inst_671_, lean_object* v_t_672_, lean_object* v_k_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_ExtTreeSet_getGT_x21___redArg(v_cmp_670_, v_inst_671_, v_t_672_, v_k_673_);
lean_dec(v_inst_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21(lean_object* v_00_u03b1_675_, lean_object* v_cmp_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_t_679_, lean_object* v_k_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_box(0);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_676_, v_k_680_, v___x_681_, v_t_679_);
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
v_val_685_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_val_685_);
lean_dec_ref(v___x_682_);
return v_val_685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___boxed(lean_object* v_00_u03b1_686_, lean_object* v_cmp_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_t_690_, lean_object* v_k_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_ExtTreeSet_getGT_x21(v_00_u03b1_686_, v_cmp_687_, v_inst_688_, v_inst_689_, v_t_690_, v_k_691_);
lean_dec(v_inst_689_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg(lean_object* v_cmp_693_, lean_object* v_inst_694_, lean_object* v_t_695_, lean_object* v_k_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_box(0);
v___x_698_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_693_, v_k_696_, v___x_697_, v_t_695_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_700_ = l_panic___redArg(v_inst_694_, v___x_699_);
return v___x_700_;
}
else
{
lean_object* v_val_701_; 
v_val_701_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_val_701_);
lean_dec_ref(v___x_698_);
return v_val_701_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg___boxed(lean_object* v_cmp_702_, lean_object* v_inst_703_, lean_object* v_t_704_, lean_object* v_k_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_ExtTreeSet_getLE_x21___redArg(v_cmp_702_, v_inst_703_, v_t_704_, v_k_705_);
lean_dec(v_inst_703_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21(lean_object* v_00_u03b1_707_, lean_object* v_cmp_708_, lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v_t_711_, lean_object* v_k_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_box(0);
v___x_714_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_708_, v_k_712_, v___x_713_, v_t_711_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_716_ = l_panic___redArg(v_inst_710_, v___x_715_);
return v___x_716_;
}
else
{
lean_object* v_val_717_; 
v_val_717_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_val_717_);
lean_dec_ref(v___x_714_);
return v_val_717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___boxed(lean_object* v_00_u03b1_718_, lean_object* v_cmp_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_t_722_, lean_object* v_k_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_ExtTreeSet_getLE_x21(v_00_u03b1_718_, v_cmp_719_, v_inst_720_, v_inst_721_, v_t_722_, v_k_723_);
lean_dec(v_inst_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg(lean_object* v_cmp_725_, lean_object* v_inst_726_, lean_object* v_t_727_, lean_object* v_k_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_box(0);
v___x_730_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_725_, v_k_728_, v___x_729_, v_t_727_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_732_ = l_panic___redArg(v_inst_726_, v___x_731_);
return v___x_732_;
}
else
{
lean_object* v_val_733_; 
v_val_733_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_val_733_);
lean_dec_ref(v___x_730_);
return v_val_733_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg___boxed(lean_object* v_cmp_734_, lean_object* v_inst_735_, lean_object* v_t_736_, lean_object* v_k_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_ExtTreeSet_getLT_x21___redArg(v_cmp_734_, v_inst_735_, v_t_736_, v_k_737_);
lean_dec(v_inst_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21(lean_object* v_00_u03b1_739_, lean_object* v_cmp_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_t_743_, lean_object* v_k_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_box(0);
v___x_746_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_740_, v_k_744_, v___x_745_, v_t_743_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_748_ = l_panic___redArg(v_inst_742_, v___x_747_);
return v___x_748_;
}
else
{
lean_object* v_val_749_; 
v_val_749_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_val_749_);
lean_dec_ref(v___x_746_);
return v_val_749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___boxed(lean_object* v_00_u03b1_750_, lean_object* v_cmp_751_, lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_t_754_, lean_object* v_k_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_ExtTreeSet_getLT_x21(v_00_u03b1_750_, v_cmp_751_, v_inst_752_, v_inst_753_, v_t_754_, v_k_755_);
lean_dec(v_inst_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg(lean_object* v_cmp_757_, lean_object* v_t_758_, lean_object* v_k_759_, lean_object* v_fallback_760_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_box(0);
v___x_762_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_757_, v_k_759_, v___x_761_, v_t_758_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_inc(v_fallback_760_);
return v_fallback_760_;
}
else
{
lean_object* v_val_763_; 
v_val_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_val_763_);
lean_dec_ref(v___x_762_);
return v_val_763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg___boxed(lean_object* v_cmp_764_, lean_object* v_t_765_, lean_object* v_k_766_, lean_object* v_fallback_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_ExtTreeSet_getGED___redArg(v_cmp_764_, v_t_765_, v_k_766_, v_fallback_767_);
lean_dec(v_fallback_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED(lean_object* v_00_u03b1_769_, lean_object* v_cmp_770_, lean_object* v_inst_771_, lean_object* v_t_772_, lean_object* v_k_773_, lean_object* v_fallback_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_box(0);
v___x_776_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_770_, v_k_773_, v___x_775_, v_t_772_);
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
lean_dec_ref(v___x_776_);
return v_val_777_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___boxed(lean_object* v_00_u03b1_778_, lean_object* v_cmp_779_, lean_object* v_inst_780_, lean_object* v_t_781_, lean_object* v_k_782_, lean_object* v_fallback_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_ExtTreeSet_getGED(v_00_u03b1_778_, v_cmp_779_, v_inst_780_, v_t_781_, v_k_782_, v_fallback_783_);
lean_dec(v_fallback_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg(lean_object* v_cmp_785_, lean_object* v_t_786_, lean_object* v_k_787_, lean_object* v_fallback_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_box(0);
v___x_790_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_785_, v_k_787_, v___x_789_, v_t_786_);
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
lean_dec_ref(v___x_790_);
return v_val_791_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg___boxed(lean_object* v_cmp_792_, lean_object* v_t_793_, lean_object* v_k_794_, lean_object* v_fallback_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Std_ExtTreeSet_getGTD___redArg(v_cmp_792_, v_t_793_, v_k_794_, v_fallback_795_);
lean_dec(v_fallback_795_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD(lean_object* v_00_u03b1_797_, lean_object* v_cmp_798_, lean_object* v_inst_799_, lean_object* v_t_800_, lean_object* v_k_801_, lean_object* v_fallback_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_box(0);
v___x_804_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_798_, v_k_801_, v___x_803_, v_t_800_);
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
lean_dec_ref(v___x_804_);
return v_val_805_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___boxed(lean_object* v_00_u03b1_806_, lean_object* v_cmp_807_, lean_object* v_inst_808_, lean_object* v_t_809_, lean_object* v_k_810_, lean_object* v_fallback_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_ExtTreeSet_getGTD(v_00_u03b1_806_, v_cmp_807_, v_inst_808_, v_t_809_, v_k_810_, v_fallback_811_);
lean_dec(v_fallback_811_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg(lean_object* v_cmp_813_, lean_object* v_t_814_, lean_object* v_k_815_, lean_object* v_fallback_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_box(0);
v___x_818_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_813_, v_k_815_, v___x_817_, v_t_814_);
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
lean_dec_ref(v___x_818_);
return v_val_819_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg___boxed(lean_object* v_cmp_820_, lean_object* v_t_821_, lean_object* v_k_822_, lean_object* v_fallback_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_ExtTreeSet_getLED___redArg(v_cmp_820_, v_t_821_, v_k_822_, v_fallback_823_);
lean_dec(v_fallback_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED(lean_object* v_00_u03b1_825_, lean_object* v_cmp_826_, lean_object* v_inst_827_, lean_object* v_t_828_, lean_object* v_k_829_, lean_object* v_fallback_830_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_box(0);
v___x_832_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_826_, v_k_829_, v___x_831_, v_t_828_);
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
lean_dec_ref(v___x_832_);
return v_val_833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___boxed(lean_object* v_00_u03b1_834_, lean_object* v_cmp_835_, lean_object* v_inst_836_, lean_object* v_t_837_, lean_object* v_k_838_, lean_object* v_fallback_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_ExtTreeSet_getLED(v_00_u03b1_834_, v_cmp_835_, v_inst_836_, v_t_837_, v_k_838_, v_fallback_839_);
lean_dec(v_fallback_839_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg(lean_object* v_cmp_841_, lean_object* v_t_842_, lean_object* v_k_843_, lean_object* v_fallback_844_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_box(0);
v___x_846_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_841_, v_k_843_, v___x_845_, v_t_842_);
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
lean_dec_ref(v___x_846_);
return v_val_847_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg___boxed(lean_object* v_cmp_848_, lean_object* v_t_849_, lean_object* v_k_850_, lean_object* v_fallback_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_ExtTreeSet_getLTD___redArg(v_cmp_848_, v_t_849_, v_k_850_, v_fallback_851_);
lean_dec(v_fallback_851_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD(lean_object* v_00_u03b1_853_, lean_object* v_cmp_854_, lean_object* v_inst_855_, lean_object* v_t_856_, lean_object* v_k_857_, lean_object* v_fallback_858_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_box(0);
v___x_860_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_854_, v_k_857_, v___x_859_, v_t_856_);
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
lean_dec_ref(v___x_860_);
return v_val_861_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___boxed(lean_object* v_00_u03b1_862_, lean_object* v_cmp_863_, lean_object* v_inst_864_, lean_object* v_t_865_, lean_object* v_k_866_, lean_object* v_fallback_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_ExtTreeSet_getLTD(v_00_u03b1_862_, v_cmp_863_, v_inst_864_, v_t_865_, v_k_866_, v_fallback_867_);
lean_dec(v_fallback_867_);
return v_res_868_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_filter___redArg___lam__0(lean_object* v_f_869_, lean_object* v_a_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = lean_apply_1(v_f_869_, v_a_870_);
v___x_873_ = lean_unbox(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg___lam__0___boxed(lean_object* v_f_874_, lean_object* v_a_875_, lean_object* v_x_876_){
_start:
{
uint8_t v_res_877_; lean_object* v_r_878_; 
v_res_877_ = l_Std_ExtTreeSet_filter___redArg___lam__0(v_f_874_, v_a_875_, v_x_876_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg(lean_object* v_f_879_, lean_object* v_m_880_){
_start:
{
lean_object* v___f_881_; lean_object* v___x_882_; 
v___f_881_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_881_, 0, v_f_879_);
v___x_882_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_881_, v_m_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter(lean_object* v_00_u03b1_883_, lean_object* v_cmp_884_, lean_object* v_f_885_, lean_object* v_m_886_){
_start:
{
lean_object* v___f_887_; lean_object* v___x_888_; 
v___f_887_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_887_, 0, v_f_885_);
v___x_888_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_887_, v_m_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___boxed(lean_object* v_00_u03b1_889_, lean_object* v_cmp_890_, lean_object* v_f_891_, lean_object* v_m_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_ExtTreeSet_filter(v_00_u03b1_889_, v_cmp_890_, v_f_891_, v_m_892_);
lean_dec_ref(v_cmp_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg___lam__0(lean_object* v_f_894_, lean_object* v_c_895_, lean_object* v_a_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_apply_2(v_f_894_, v_c_895_, v_a_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg(lean_object* v_inst_899_, lean_object* v_f_900_, lean_object* v_init_901_, lean_object* v_t_902_){
_start:
{
lean_object* v___f_903_; lean_object* v___x_904_; 
v___f_903_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_903_, 0, v_f_900_);
v___x_904_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_899_, v___f_903_, v_init_901_, v_t_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM(lean_object* v_00_u03b1_905_, lean_object* v_cmp_906_, lean_object* v_00_u03b4_907_, lean_object* v_m_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_f_912_, lean_object* v_init_913_, lean_object* v_t_914_){
_start:
{
lean_object* v___f_915_; lean_object* v___x_916_; 
v___f_915_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_915_, 0, v_f_912_);
v___x_916_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_909_, v___f_915_, v_init_913_, v_t_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___boxed(lean_object* v_00_u03b1_917_, lean_object* v_cmp_918_, lean_object* v_00_u03b4_919_, lean_object* v_m_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_f_924_, lean_object* v_init_925_, lean_object* v_t_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_ExtTreeSet_foldlM(v_00_u03b1_917_, v_cmp_918_, v_00_u03b4_919_, v_m_920_, v_inst_921_, v_inst_922_, v_inst_923_, v_f_924_, v_init_925_, v_t_926_);
lean_dec_ref(v_cmp_918_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___redArg(lean_object* v_f_928_, lean_object* v_init_929_, lean_object* v_t_930_){
_start:
{
lean_object* v___f_931_; lean_object* v___x_932_; 
v___f_931_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_931_, 0, v_f_928_);
v___x_932_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_931_, v_init_929_, v_t_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl(lean_object* v_00_u03b1_933_, lean_object* v_cmp_934_, lean_object* v_00_u03b4_935_, lean_object* v_inst_936_, lean_object* v_f_937_, lean_object* v_init_938_, lean_object* v_t_939_){
_start:
{
lean_object* v___f_940_; lean_object* v___x_941_; 
v___f_940_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_940_, 0, v_f_937_);
v___x_941_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_940_, v_init_938_, v_t_939_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___boxed(lean_object* v_00_u03b1_942_, lean_object* v_cmp_943_, lean_object* v_00_u03b4_944_, lean_object* v_inst_945_, lean_object* v_f_946_, lean_object* v_init_947_, lean_object* v_t_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_ExtTreeSet_foldl(v_00_u03b1_942_, v_cmp_943_, v_00_u03b4_944_, v_inst_945_, v_f_946_, v_init_947_, v_t_948_);
lean_dec_ref(v_cmp_943_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg___lam__0(lean_object* v_f_950_, lean_object* v_a_951_, lean_object* v_x_952_, lean_object* v_acc_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = lean_apply_2(v_f_950_, v_a_951_, v_acc_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg(lean_object* v_inst_955_, lean_object* v_f_956_, lean_object* v_init_957_, lean_object* v_t_958_){
_start:
{
lean_object* v___f_959_; lean_object* v___x_960_; 
v___f_959_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_959_, 0, v_f_956_);
v___x_960_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_955_, v___f_959_, v_init_957_, v_t_958_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM(lean_object* v_00_u03b1_961_, lean_object* v_cmp_962_, lean_object* v_00_u03b4_963_, lean_object* v_m_964_, lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_inst_967_, lean_object* v_f_968_, lean_object* v_init_969_, lean_object* v_t_970_){
_start:
{
lean_object* v___f_971_; lean_object* v___x_972_; 
v___f_971_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_971_, 0, v_f_968_);
v___x_972_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_965_, v___f_971_, v_init_969_, v_t_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___boxed(lean_object* v_00_u03b1_973_, lean_object* v_cmp_974_, lean_object* v_00_u03b4_975_, lean_object* v_m_976_, lean_object* v_inst_977_, lean_object* v_inst_978_, lean_object* v_inst_979_, lean_object* v_f_980_, lean_object* v_init_981_, lean_object* v_t_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Std_ExtTreeSet_foldrM(v_00_u03b1_973_, v_cmp_974_, v_00_u03b4_975_, v_m_976_, v_inst_977_, v_inst_978_, v_inst_979_, v_f_980_, v_init_981_, v_t_982_);
lean_dec_ref(v_cmp_974_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg___lam__0(lean_object* v_f_984_, lean_object* v_x1_985_, lean_object* v_x2_986_, lean_object* v_x3_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = lean_apply_2(v_f_984_, v_x1_985_, v_x3_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg(lean_object* v_f_1008_, lean_object* v_init_1009_, lean_object* v_t_1010_){
_start:
{
lean_object* v___f_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___f_1011_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1011_, 0, v_f_1008_);
v___x_1012_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1013_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1012_, v___f_1011_, v_init_1009_, v_t_1010_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr(lean_object* v_00_u03b1_1014_, lean_object* v_cmp_1015_, lean_object* v_00_u03b4_1016_, lean_object* v_inst_1017_, lean_object* v_f_1018_, lean_object* v_init_1019_, lean_object* v_t_1020_){
_start:
{
lean_object* v___f_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___f_1021_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1021_, 0, v_f_1018_);
v___x_1022_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1023_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1022_, v___f_1021_, v_init_1019_, v_t_1020_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___boxed(lean_object* v_00_u03b1_1024_, lean_object* v_cmp_1025_, lean_object* v_00_u03b4_1026_, lean_object* v_inst_1027_, lean_object* v_f_1028_, lean_object* v_init_1029_, lean_object* v_t_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Std_ExtTreeSet_foldr(v_00_u03b1_1024_, v_cmp_1025_, v_00_u03b4_1026_, v_inst_1027_, v_f_1028_, v_init_1029_, v_t_1030_);
lean_dec_ref(v_cmp_1025_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg___lam__0(lean_object* v_f_1032_, lean_object* v_cmp_1033_, lean_object* v_x_1034_, lean_object* v_a_1035_, lean_object* v_b_1036_){
_start:
{
lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1052_; 
v_fst_1037_ = lean_ctor_get(v_x_1034_, 0);
v_snd_1038_ = lean_ctor_get(v_x_1034_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1040_ = v_x_1034_;
v_isShared_1041_ = v_isSharedCheck_1052_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snd_1038_);
lean_inc(v_fst_1037_);
lean_dec(v_x_1034_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1052_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
lean_inc(v_a_1035_);
v___x_1042_ = lean_apply_1(v_f_1032_, v_a_1035_);
v___x_1043_ = lean_unbox(v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1033_, v_a_1035_, v_b_1036_, v_snd_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___x_1044_);
v___x_1046_ = v___x_1040_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_fst_1037_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1033_, v_a_1035_, v_b_1036_, v_fst_1037_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1048_);
v___x_1050_ = v___x_1040_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_snd_1038_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg(lean_object* v_cmp_1055_, lean_object* v_f_1056_, lean_object* v_t_1057_){
_start:
{
lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v_p_1060_; lean_object* v_fst_1061_; lean_object* v_snd_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v___f_1058_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1058_, 0, v_f_1056_);
lean_closure_set(v___f_1058_, 1, v_cmp_1055_);
v___x_1059_ = ((lean_object*)(l_Std_ExtTreeSet_partition___redArg___closed__0));
v_p_1060_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1058_, v___x_1059_, v_t_1057_);
v_fst_1061_ = lean_ctor_get(v_p_1060_, 0);
v_snd_1062_ = lean_ctor_get(v_p_1060_, 1);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_p_1060_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v_p_1060_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_snd_1062_);
lean_inc(v_fst_1061_);
lean_dec(v_p_1060_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_fst_1061_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_snd_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition(lean_object* v_00_u03b1_1070_, lean_object* v_cmp_1071_, lean_object* v_inst_1072_, lean_object* v_f_1073_, lean_object* v_t_1074_){
_start:
{
lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v_p_1077_; lean_object* v_fst_1078_; lean_object* v_snd_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v___f_1075_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1075_, 0, v_f_1073_);
lean_closure_set(v___f_1075_, 1, v_cmp_1071_);
v___x_1076_ = ((lean_object*)(l_Std_ExtTreeSet_partition___redArg___closed__0));
v_p_1077_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1075_, v___x_1076_, v_t_1074_);
v_fst_1078_ = lean_ctor_get(v_p_1077_, 0);
v_snd_1079_ = lean_ctor_get(v_p_1077_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_p_1077_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v_p_1077_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_snd_1079_);
lean_inc(v_fst_1078_);
lean_dec(v_p_1077_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_fst_1078_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_snd_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg___lam__0(lean_object* v_f_1087_, lean_object* v_x_1088_, lean_object* v_k_1089_, lean_object* v_v_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_apply_1(v_f_1087_, v_k_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg(lean_object* v_inst_1092_, lean_object* v_f_1093_, lean_object* v_t_1094_){
_start:
{
lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___f_1095_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1095_, 0, v_f_1093_);
v___x_1096_ = lean_box(0);
v___x_1097_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1092_, v___f_1095_, v___x_1096_, v_t_1094_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM(lean_object* v_00_u03b1_1098_, lean_object* v_cmp_1099_, lean_object* v_m_1100_, lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_f_1104_, lean_object* v_t_1105_){
_start:
{
lean_object* v___f_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___f_1106_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1106_, 0, v_f_1104_);
v___x_1107_ = lean_box(0);
v___x_1108_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1101_, v___f_1106_, v___x_1107_, v_t_1105_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___boxed(lean_object* v_00_u03b1_1109_, lean_object* v_cmp_1110_, lean_object* v_m_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_f_1115_, lean_object* v_t_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_ExtTreeSet_forM(v_00_u03b1_1109_, v_cmp_1110_, v_m_1111_, v_inst_1112_, v_inst_1113_, v_inst_1114_, v_f_1115_, v_t_1116_);
lean_dec_ref(v_cmp_1110_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__0(lean_object* v_f_1118_, lean_object* v_a_1119_, lean_object* v_b_1120_, lean_object* v_c_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_apply_2(v_f_1118_, v_a_1119_, v_c_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__1(lean_object* v_toPure_1123_, lean_object* v_____do__lift_1124_){
_start:
{
lean_object* v_a_1125_; lean_object* v___x_1126_; 
v_a_1125_ = lean_ctor_get(v_____do__lift_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref(v_____do__lift_1124_);
v___x_1126_ = lean_apply_2(v_toPure_1123_, lean_box(0), v_a_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg(lean_object* v_inst_1127_, lean_object* v_f_1128_, lean_object* v_init_1129_, lean_object* v_t_1130_){
_start:
{
lean_object* v_toApplicative_1131_; lean_object* v_toBind_1132_; lean_object* v_toPure_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; 
v_toApplicative_1131_ = lean_ctor_get(v_inst_1127_, 0);
v_toBind_1132_ = lean_ctor_get(v_inst_1127_, 1);
lean_inc(v_toBind_1132_);
v_toPure_1133_ = lean_ctor_get(v_toApplicative_1131_, 1);
lean_inc(v_toPure_1133_);
v___f_1134_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1134_, 0, v_f_1128_);
v___x_1135_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1127_, v___f_1134_, v_init_1129_, v_t_1130_);
v___f_1136_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1136_, 0, v_toPure_1133_);
v___x_1137_ = lean_apply_4(v_toBind_1132_, lean_box(0), lean_box(0), v___x_1135_, v___f_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn(lean_object* v_00_u03b1_1138_, lean_object* v_cmp_1139_, lean_object* v_00_u03b4_1140_, lean_object* v_m_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_f_1145_, lean_object* v_init_1146_, lean_object* v_t_1147_){
_start:
{
lean_object* v_toApplicative_1148_; lean_object* v_toBind_1149_; lean_object* v_toPure_1150_; lean_object* v___f_1151_; lean_object* v___x_1152_; lean_object* v___f_1153_; lean_object* v___x_1154_; 
v_toApplicative_1148_ = lean_ctor_get(v_inst_1142_, 0);
v_toBind_1149_ = lean_ctor_get(v_inst_1142_, 1);
lean_inc(v_toBind_1149_);
v_toPure_1150_ = lean_ctor_get(v_toApplicative_1148_, 1);
lean_inc(v_toPure_1150_);
v___f_1151_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1151_, 0, v_f_1145_);
v___x_1152_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1142_, v___f_1151_, v_init_1146_, v_t_1147_);
v___f_1153_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1153_, 0, v_toPure_1150_);
v___x_1154_ = lean_apply_4(v_toBind_1149_, lean_box(0), lean_box(0), v___x_1152_, v___f_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_cmp_1156_, lean_object* v_00_u03b4_1157_, lean_object* v_m_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_f_1162_, lean_object* v_init_1163_, lean_object* v_t_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Std_ExtTreeSet_forIn(v_00_u03b1_1155_, v_cmp_1156_, v_00_u03b4_1157_, v_m_1158_, v_inst_1159_, v_inst_1160_, v_inst_1161_, v_f_1162_, v_init_1163_, v_t_1164_);
lean_dec_ref(v_cmp_1156_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_1166_, lean_object* v_t_1167_, lean_object* v_f_1168_){
_start:
{
lean_object* v___f_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___f_1169_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1169_, 0, v_f_1168_);
v___x_1170_ = lean_box(0);
v___x_1171_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1166_, v___f_1169_, v___x_1170_, v_t_1167_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1172_){
_start:
{
lean_object* v___f_1173_; 
v___f_1173_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1173_, 0, v_inst_1172_);
return v___f_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1174_, lean_object* v_cmp_1175_, lean_object* v_m_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_){
_start:
{
lean_object* v___f_1180_; 
v___f_1180_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1180_, 0, v_inst_1178_);
return v___f_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_cmp_1182_, lean_object* v_m_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(v_00_u03b1_1181_, v_cmp_1182_, v_m_1183_, v_inst_1184_, v_inst_1185_, v_inst_1186_);
lean_dec_ref(v_cmp_1182_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_1188_, lean_object* v_00_u03b2_1189_, lean_object* v_m_1190_, lean_object* v_init_1191_, lean_object* v_f_1192_){
_start:
{
lean_object* v_toApplicative_1193_; lean_object* v_toBind_1194_; lean_object* v_toPure_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; lean_object* v___f_1198_; lean_object* v___x_1199_; 
v_toApplicative_1193_ = lean_ctor_get(v_inst_1188_, 0);
v_toBind_1194_ = lean_ctor_get(v_inst_1188_, 1);
lean_inc(v_toBind_1194_);
v_toPure_1195_ = lean_ctor_get(v_toApplicative_1193_, 1);
lean_inc(v_toPure_1195_);
v___f_1196_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1196_, 0, v_f_1192_);
v___x_1197_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1188_, v___f_1196_, v_init_1191_, v_m_1190_);
v___f_1198_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1198_, 0, v_toPure_1195_);
v___x_1199_ = lean_apply_4(v_toBind_1194_, lean_box(0), lean_box(0), v___x_1197_, v___f_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1200_){
_start:
{
lean_object* v___f_1201_; 
v___f_1201_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1201_, 0, v_inst_1200_);
return v___f_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1202_, lean_object* v_cmp_1203_, lean_object* v_m_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_){
_start:
{
lean_object* v___f_1208_; 
v___f_1208_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1208_, 0, v_inst_1206_);
return v___f_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1209_, lean_object* v_cmp_1210_, lean_object* v_m_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(v_00_u03b1_1209_, v_cmp_1210_, v_m_1211_, v_inst_1212_, v_inst_1213_, v_inst_1214_);
lean_dec_ref(v_cmp_1210_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0(lean_object* v_p_1216_, lean_object* v___x_1217_, lean_object* v___x_1218_, lean_object* v_a_1219_, lean_object* v_b_1220_, lean_object* v_acc_1221_){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = lean_apply_1(v_p_1216_, v_a_1219_);
v___x_1223_ = lean_unbox(v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1217_);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v___x_1217_);
v___x_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1222_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1218_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0___boxed(lean_object* v_p_1228_, lean_object* v___x_1229_, lean_object* v___x_1230_, lean_object* v_a_1231_, lean_object* v_b_1232_, lean_object* v_acc_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Std_ExtTreeSet_any___redArg___lam__0(v_p_1228_, v___x_1229_, v___x_1230_, v_a_1231_, v_b_1232_, v_acc_1233_);
lean_dec_ref(v_acc_1233_);
return v_res_1234_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_any___redArg(lean_object* v_t_1238_, lean_object* v_p_1239_){
_start:
{
lean_object* v___y_1241_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___f_1249_; lean_object* v___x_1250_; lean_object* v_a_1251_; 
v___x_1246_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1247_ = lean_box(0);
v___x_1248_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1249_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1249_, 0, v_p_1239_);
lean_closure_set(v___f_1249_, 1, v___x_1248_);
lean_closure_set(v___f_1249_, 2, v___x_1247_);
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1246_, v___f_1249_, v___x_1248_, v_t_1238_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___y_1241_ = v_a_1251_;
goto v___jp_1240_;
v___jp_1240_:
{
lean_object* v_fst_1242_; 
v_fst_1242_ = lean_ctor_get(v___y_1241_, 0);
lean_inc(v_fst_1242_);
lean_dec_ref(v___y_1241_);
if (lean_obj_tag(v_fst_1242_) == 0)
{
uint8_t v___x_1243_; 
v___x_1243_ = 0;
return v___x_1243_;
}
else
{
lean_object* v_val_1244_; uint8_t v___x_1245_; 
v_val_1244_ = lean_ctor_get(v_fst_1242_, 0);
lean_inc(v_val_1244_);
lean_dec_ref(v_fst_1242_);
v___x_1245_ = lean_unbox(v_val_1244_);
lean_dec(v_val_1244_);
return v___x_1245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___boxed(lean_object* v_t_1252_, lean_object* v_p_1253_){
_start:
{
uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_res_1254_ = l_Std_ExtTreeSet_any___redArg(v_t_1252_, v_p_1253_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_any(lean_object* v_00_u03b1_1256_, lean_object* v_cmp_1257_, lean_object* v_inst_1258_, lean_object* v_t_1259_, lean_object* v_p_1260_){
_start:
{
lean_object* v___y_1262_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v_a_1272_; 
v___x_1267_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1268_ = lean_box(0);
v___x_1269_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1270_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1270_, 0, v_p_1260_);
lean_closure_set(v___f_1270_, 1, v___x_1269_);
lean_closure_set(v___f_1270_, 2, v___x_1268_);
v___x_1271_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1267_, v___f_1270_, v___x_1269_, v_t_1259_);
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___y_1262_ = v_a_1272_;
goto v___jp_1261_;
v___jp_1261_:
{
lean_object* v_fst_1263_; 
v_fst_1263_ = lean_ctor_get(v___y_1262_, 0);
lean_inc(v_fst_1263_);
lean_dec_ref(v___y_1262_);
if (lean_obj_tag(v_fst_1263_) == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = 0;
return v___x_1264_;
}
else
{
lean_object* v_val_1265_; uint8_t v___x_1266_; 
v_val_1265_ = lean_ctor_get(v_fst_1263_, 0);
lean_inc(v_val_1265_);
lean_dec_ref(v_fst_1263_);
v___x_1266_ = lean_unbox(v_val_1265_);
lean_dec(v_val_1265_);
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___boxed(lean_object* v_00_u03b1_1273_, lean_object* v_cmp_1274_, lean_object* v_inst_1275_, lean_object* v_t_1276_, lean_object* v_p_1277_){
_start:
{
uint8_t v_res_1278_; lean_object* v_r_1279_; 
v_res_1278_ = l_Std_ExtTreeSet_any(v_00_u03b1_1273_, v_cmp_1274_, v_inst_1275_, v_t_1276_, v_p_1277_);
lean_dec_ref(v_cmp_1274_);
v_r_1279_ = lean_box(v_res_1278_);
return v_r_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0(lean_object* v_p_1280_, lean_object* v___x_1281_, lean_object* v___x_1282_, lean_object* v_a_1283_, lean_object* v_b_1284_, lean_object* v_acc_1285_){
_start:
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = lean_apply_1(v_p_1280_, v_a_1283_);
v___x_1287_ = lean_unbox(v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec_ref(v___x_1282_);
v___x_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v___x_1281_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1282_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0___boxed(lean_object* v_p_1292_, lean_object* v___x_1293_, lean_object* v___x_1294_, lean_object* v_a_1295_, lean_object* v_b_1296_, lean_object* v_acc_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Std_ExtTreeSet_all___redArg___lam__0(v_p_1292_, v___x_1293_, v___x_1294_, v_a_1295_, v_b_1296_, v_acc_1297_);
lean_dec_ref(v_acc_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_all___redArg(lean_object* v_t_1299_, lean_object* v_p_1300_){
_start:
{
lean_object* v___y_1302_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___f_1310_; lean_object* v___x_1311_; lean_object* v_a_1312_; 
v___x_1307_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1308_ = lean_box(0);
v___x_1309_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1310_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1310_, 0, v_p_1300_);
lean_closure_set(v___f_1310_, 1, v___x_1308_);
lean_closure_set(v___f_1310_, 2, v___x_1309_);
v___x_1311_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1307_, v___f_1310_, v___x_1309_, v_t_1299_);
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___y_1302_ = v_a_1312_;
goto v___jp_1301_;
v___jp_1301_:
{
lean_object* v_fst_1303_; 
v_fst_1303_ = lean_ctor_get(v___y_1302_, 0);
lean_inc(v_fst_1303_);
lean_dec_ref(v___y_1302_);
if (lean_obj_tag(v_fst_1303_) == 0)
{
uint8_t v___x_1304_; 
v___x_1304_ = 1;
return v___x_1304_;
}
else
{
lean_object* v_val_1305_; uint8_t v___x_1306_; 
v_val_1305_ = lean_ctor_get(v_fst_1303_, 0);
lean_inc(v_val_1305_);
lean_dec_ref(v_fst_1303_);
v___x_1306_ = lean_unbox(v_val_1305_);
lean_dec(v_val_1305_);
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___boxed(lean_object* v_t_1313_, lean_object* v_p_1314_){
_start:
{
uint8_t v_res_1315_; lean_object* v_r_1316_; 
v_res_1315_ = l_Std_ExtTreeSet_all___redArg(v_t_1313_, v_p_1314_);
v_r_1316_ = lean_box(v_res_1315_);
return v_r_1316_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_all(lean_object* v_00_u03b1_1317_, lean_object* v_cmp_1318_, lean_object* v_inst_1319_, lean_object* v_t_1320_, lean_object* v_p_1321_){
_start:
{
lean_object* v___y_1323_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___f_1331_; lean_object* v___x_1332_; lean_object* v_a_1333_; 
v___x_1328_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1329_ = lean_box(0);
v___x_1330_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1331_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1331_, 0, v_p_1321_);
lean_closure_set(v___f_1331_, 1, v___x_1329_);
lean_closure_set(v___f_1331_, 2, v___x_1330_);
v___x_1332_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1328_, v___f_1331_, v___x_1330_, v_t_1320_);
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___y_1323_ = v_a_1333_;
goto v___jp_1322_;
v___jp_1322_:
{
lean_object* v_fst_1324_; 
v_fst_1324_ = lean_ctor_get(v___y_1323_, 0);
lean_inc(v_fst_1324_);
lean_dec_ref(v___y_1323_);
if (lean_obj_tag(v_fst_1324_) == 0)
{
uint8_t v___x_1325_; 
v___x_1325_ = 1;
return v___x_1325_;
}
else
{
lean_object* v_val_1326_; uint8_t v___x_1327_; 
v_val_1326_ = lean_ctor_get(v_fst_1324_, 0);
lean_inc(v_val_1326_);
lean_dec_ref(v_fst_1324_);
v___x_1327_ = lean_unbox(v_val_1326_);
lean_dec(v_val_1326_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___boxed(lean_object* v_00_u03b1_1334_, lean_object* v_cmp_1335_, lean_object* v_inst_1336_, lean_object* v_t_1337_, lean_object* v_p_1338_){
_start:
{
uint8_t v_res_1339_; lean_object* v_r_1340_; 
v_res_1339_ = l_Std_ExtTreeSet_all(v_00_u03b1_1334_, v_cmp_1335_, v_inst_1336_, v_t_1337_, v_p_1338_);
lean_dec_ref(v_cmp_1335_);
v_r_1340_ = lean_box(v_res_1339_);
return v_r_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg___lam__0(lean_object* v_x1_1341_, lean_object* v_x2_1342_, lean_object* v_x3_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_x1_1341_);
lean_ctor_set(v___x_1344_, 1, v_x3_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg(lean_object* v_t_1346_){
_start:
{
lean_object* v___f_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___f_1347_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___x_1348_ = lean_box(0);
v___x_1349_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1350_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1349_, v___f_1347_, v___x_1348_, v_t_1346_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList(lean_object* v_00_u03b1_1351_, lean_object* v_cmp_1352_, lean_object* v_inst_1353_, lean_object* v_t_1354_){
_start:
{
lean_object* v___f_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___f_1355_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___x_1356_ = lean_box(0);
v___x_1357_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1358_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1357_, v___f_1355_, v___x_1356_, v_t_1354_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___boxed(lean_object* v_00_u03b1_1359_, lean_object* v_cmp_1360_, lean_object* v_inst_1361_, lean_object* v_t_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_ExtTreeSet_toList(v_00_u03b1_1359_, v_cmp_1360_, v_inst_1361_, v_t_1362_);
lean_dec_ref(v_cmp_1360_);
return v_res_1363_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_ofList___auto__1(void){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__26, &l_Std_ExtTreeSet___auto__1___closed__26_once, _init_l_Std_ExtTreeSet___auto__1___closed__26);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(lean_object* v_cmp_1365_, lean_object* v_k_1366_, lean_object* v_v_1367_, lean_object* v_t_1368_){
_start:
{
if (lean_obj_tag(v_t_1368_) == 0)
{
lean_object* v_size_1369_; lean_object* v_k_1370_; lean_object* v_v_1371_; lean_object* v_l_1372_; lean_object* v_r_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1654_; 
v_size_1369_ = lean_ctor_get(v_t_1368_, 0);
v_k_1370_ = lean_ctor_get(v_t_1368_, 1);
v_v_1371_ = lean_ctor_get(v_t_1368_, 2);
v_l_1372_ = lean_ctor_get(v_t_1368_, 3);
v_r_1373_ = lean_ctor_get(v_t_1368_, 4);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_t_1368_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1375_ = v_t_1368_;
v_isShared_1376_ = v_isSharedCheck_1654_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_r_1373_);
lean_inc(v_l_1372_);
lean_inc(v_v_1371_);
lean_inc(v_k_1370_);
lean_inc(v_size_1369_);
lean_dec(v_t_1368_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1654_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
lean_inc_ref(v_cmp_1365_);
lean_inc(v_k_1370_);
lean_inc(v_k_1366_);
v___x_1377_ = lean_apply_2(v_cmp_1365_, v_k_1366_, v_k_1370_);
v___x_1378_ = lean_unbox(v___x_1377_);
switch(v___x_1378_)
{
case 0:
{
lean_object* v_impl_1379_; lean_object* v___x_1380_; 
lean_dec(v_size_1369_);
v_impl_1379_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1365_, v_k_1366_, v_v_1367_, v_l_1372_);
v___x_1380_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1373_) == 0)
{
lean_object* v_size_1381_; lean_object* v_size_1382_; lean_object* v_k_1383_; lean_object* v_v_1384_; lean_object* v_l_1385_; lean_object* v_r_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v_size_1381_ = lean_ctor_get(v_r_1373_, 0);
v_size_1382_ = lean_ctor_get(v_impl_1379_, 0);
lean_inc(v_size_1382_);
v_k_1383_ = lean_ctor_get(v_impl_1379_, 1);
lean_inc(v_k_1383_);
v_v_1384_ = lean_ctor_get(v_impl_1379_, 2);
lean_inc(v_v_1384_);
v_l_1385_ = lean_ctor_get(v_impl_1379_, 3);
lean_inc(v_l_1385_);
v_r_1386_ = lean_ctor_get(v_impl_1379_, 4);
lean_inc(v_r_1386_);
v___x_1387_ = lean_unsigned_to_nat(3u);
v___x_1388_ = lean_nat_mul(v___x_1387_, v_size_1381_);
v___x_1389_ = lean_nat_dec_lt(v___x_1388_, v_size_1382_);
lean_dec(v___x_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
lean_dec(v_r_1386_);
lean_dec(v_l_1385_);
lean_dec(v_v_1384_);
lean_dec(v_k_1383_);
v___x_1390_ = lean_nat_add(v___x_1380_, v_size_1382_);
lean_dec(v_size_1382_);
v___x_1391_ = lean_nat_add(v___x_1390_, v_size_1381_);
lean_dec(v___x_1390_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 3, v_impl_1379_);
lean_ctor_set(v___x_1375_, 0, v___x_1391_);
v___x_1393_ = v___x_1375_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_impl_1379_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_r_1373_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
else
{
lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1460_; 
v_isSharedCheck_1460_ = !lean_is_exclusive(v_impl_1379_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; lean_object* v_unused_1462_; lean_object* v_unused_1463_; lean_object* v_unused_1464_; lean_object* v_unused_1465_; 
v_unused_1461_ = lean_ctor_get(v_impl_1379_, 4);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_impl_1379_, 3);
lean_dec(v_unused_1462_);
v_unused_1463_ = lean_ctor_get(v_impl_1379_, 2);
lean_dec(v_unused_1463_);
v_unused_1464_ = lean_ctor_get(v_impl_1379_, 1);
lean_dec(v_unused_1464_);
v_unused_1465_ = lean_ctor_get(v_impl_1379_, 0);
lean_dec(v_unused_1465_);
v___x_1396_ = v_impl_1379_;
v_isShared_1397_ = v_isSharedCheck_1460_;
goto v_resetjp_1395_;
}
else
{
lean_dec(v_impl_1379_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1460_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_size_1398_; lean_object* v_size_1399_; lean_object* v_k_1400_; lean_object* v_v_1401_; lean_object* v_l_1402_; lean_object* v_r_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_size_1398_ = lean_ctor_get(v_l_1385_, 0);
v_size_1399_ = lean_ctor_get(v_r_1386_, 0);
v_k_1400_ = lean_ctor_get(v_r_1386_, 1);
v_v_1401_ = lean_ctor_get(v_r_1386_, 2);
v_l_1402_ = lean_ctor_get(v_r_1386_, 3);
v_r_1403_ = lean_ctor_get(v_r_1386_, 4);
v___x_1404_ = lean_unsigned_to_nat(2u);
v___x_1405_ = lean_nat_mul(v___x_1404_, v_size_1398_);
v___x_1406_ = lean_nat_dec_lt(v_size_1399_, v___x_1405_);
lean_dec(v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1435_; 
lean_inc(v_r_1403_);
lean_inc(v_l_1402_);
lean_inc(v_v_1401_);
lean_inc(v_k_1400_);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_r_1386_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; lean_object* v_unused_1439_; lean_object* v_unused_1440_; 
v_unused_1436_ = lean_ctor_get(v_r_1386_, 4);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_r_1386_, 3);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_r_1386_, 2);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_r_1386_, 1);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_r_1386_, 0);
lean_dec(v_unused_1440_);
v___x_1408_ = v_r_1386_;
v_isShared_1409_ = v_isSharedCheck_1435_;
goto v_resetjp_1407_;
}
else
{
lean_dec(v_r_1386_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1435_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___x_1423_; lean_object* v___y_1425_; 
v___x_1410_ = lean_nat_add(v___x_1380_, v_size_1382_);
lean_dec(v_size_1382_);
v___x_1411_ = lean_nat_add(v___x_1410_, v_size_1381_);
lean_dec(v___x_1410_);
v___x_1423_ = lean_nat_add(v___x_1380_, v_size_1398_);
if (lean_obj_tag(v_l_1402_) == 0)
{
lean_object* v_size_1433_; 
v_size_1433_ = lean_ctor_get(v_l_1402_, 0);
lean_inc(v_size_1433_);
v___y_1425_ = v_size_1433_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v___y_1425_ = v___x_1434_;
goto v___jp_1424_;
}
v___jp_1412_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_nat_add(v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec(v___y_1414_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 4, v_r_1373_);
lean_ctor_set(v___x_1408_, 3, v_r_1403_);
lean_ctor_set(v___x_1408_, 2, v_v_1371_);
lean_ctor_set(v___x_1408_, 1, v_k_1370_);
lean_ctor_set(v___x_1408_, 0, v___x_1416_);
v___x_1418_ = v___x_1408_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_r_1403_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_r_1373_);
v___x_1418_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v___x_1418_);
lean_ctor_set(v___x_1396_, 3, v___y_1413_);
lean_ctor_set(v___x_1396_, 2, v_v_1401_);
lean_ctor_set(v___x_1396_, 1, v_k_1400_);
lean_ctor_set(v___x_1396_, 0, v___x_1411_);
v___x_1420_ = v___x_1396_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_k_1400_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_v_1401_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v___y_1413_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
v___jp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1426_ = lean_nat_add(v___x_1423_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec(v___x_1423_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_l_1402_);
lean_ctor_set(v___x_1375_, 3, v_l_1385_);
lean_ctor_set(v___x_1375_, 2, v_v_1384_);
lean_ctor_set(v___x_1375_, 1, v_k_1383_);
lean_ctor_set(v___x_1375_, 0, v___x_1426_);
v___x_1428_ = v___x_1375_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_k_1383_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_v_1384_);
lean_ctor_set(v_reuseFailAlloc_1432_, 3, v_l_1385_);
lean_ctor_set(v_reuseFailAlloc_1432_, 4, v_l_1402_);
v___x_1428_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_nat_add(v___x_1380_, v_size_1381_);
if (lean_obj_tag(v_r_1403_) == 0)
{
lean_object* v_size_1430_; 
v_size_1430_ = lean_ctor_get(v_r_1403_, 0);
lean_inc(v_size_1430_);
v___y_1413_ = v___x_1428_;
v___y_1414_ = v___x_1429_;
v___y_1415_ = v_size_1430_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___y_1413_ = v___x_1428_;
v___y_1414_ = v___x_1429_;
v___y_1415_ = v___x_1431_;
goto v___jp_1412_;
}
}
}
}
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_del_object(v___x_1375_);
v___x_1441_ = lean_nat_add(v___x_1380_, v_size_1382_);
lean_dec(v_size_1382_);
v___x_1442_ = lean_nat_add(v___x_1441_, v_size_1381_);
lean_dec(v___x_1441_);
v___x_1443_ = lean_nat_add(v___x_1380_, v_size_1381_);
v___x_1444_ = lean_nat_add(v___x_1443_, v_size_1399_);
lean_dec(v___x_1443_);
lean_inc_ref(v_r_1373_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_r_1373_);
lean_ctor_set(v___x_1396_, 3, v_r_1386_);
lean_ctor_set(v___x_1396_, 2, v_v_1371_);
lean_ctor_set(v___x_1396_, 1, v_k_1370_);
lean_ctor_set(v___x_1396_, 0, v___x_1444_);
v___x_1446_ = v___x_1396_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_r_1386_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v_r_1373_);
v___x_1446_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_isSharedCheck_1453_ = !lean_is_exclusive(v_r_1373_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; lean_object* v_unused_1455_; lean_object* v_unused_1456_; lean_object* v_unused_1457_; lean_object* v_unused_1458_; 
v_unused_1454_ = lean_ctor_get(v_r_1373_, 4);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_r_1373_, 3);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_r_1373_, 2);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_r_1373_, 1);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_r_1373_, 0);
lean_dec(v_unused_1458_);
v___x_1448_ = v_r_1373_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_dec(v_r_1373_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 4, v___x_1446_);
lean_ctor_set(v___x_1448_, 3, v_l_1385_);
lean_ctor_set(v___x_1448_, 2, v_v_1384_);
lean_ctor_set(v___x_1448_, 1, v_k_1383_);
lean_ctor_set(v___x_1448_, 0, v___x_1442_);
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_k_1383_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_v_1384_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_l_1385_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v___x_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1466_; 
v_l_1466_ = lean_ctor_get(v_impl_1379_, 3);
lean_inc(v_l_1466_);
if (lean_obj_tag(v_l_1466_) == 0)
{
lean_object* v_r_1467_; lean_object* v_k_1468_; lean_object* v_v_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1480_; 
v_r_1467_ = lean_ctor_get(v_impl_1379_, 4);
v_k_1468_ = lean_ctor_get(v_impl_1379_, 1);
v_v_1469_ = lean_ctor_get(v_impl_1379_, 2);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_impl_1379_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; lean_object* v_unused_1482_; 
v_unused_1481_ = lean_ctor_get(v_impl_1379_, 3);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v_impl_1379_, 0);
lean_dec(v_unused_1482_);
v___x_1471_ = v_impl_1379_;
v_isShared_1472_ = v_isSharedCheck_1480_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_r_1467_);
lean_inc(v_v_1469_);
lean_inc(v_k_1468_);
lean_dec(v_impl_1379_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1480_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1467_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 3, v_r_1467_);
lean_ctor_set(v___x_1471_, 2, v_v_1371_);
lean_ctor_set(v___x_1471_, 1, v_k_1370_);
lean_ctor_set(v___x_1471_, 0, v___x_1380_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_r_1467_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_r_1467_);
v___x_1475_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v___x_1475_);
lean_ctor_set(v___x_1375_, 3, v_l_1466_);
lean_ctor_set(v___x_1375_, 2, v_v_1469_);
lean_ctor_set(v___x_1375_, 1, v_k_1468_);
lean_ctor_set(v___x_1375_, 0, v___x_1473_);
v___x_1477_ = v___x_1375_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1468_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1469_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v_l_1466_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_r_1483_; 
v_r_1483_ = lean_ctor_get(v_impl_1379_, 4);
lean_inc(v_r_1483_);
if (lean_obj_tag(v_r_1483_) == 0)
{
lean_object* v_k_1484_; lean_object* v_v_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1508_; 
v_k_1484_ = lean_ctor_get(v_impl_1379_, 1);
v_v_1485_ = lean_ctor_get(v_impl_1379_, 2);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_impl_1379_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; lean_object* v_unused_1510_; lean_object* v_unused_1511_; 
v_unused_1509_ = lean_ctor_get(v_impl_1379_, 4);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_impl_1379_, 3);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_impl_1379_, 0);
lean_dec(v_unused_1511_);
v___x_1487_ = v_impl_1379_;
v_isShared_1488_ = v_isSharedCheck_1508_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_v_1485_);
lean_inc(v_k_1484_);
lean_dec(v_impl_1379_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1508_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1504_; 
v_k_1489_ = lean_ctor_get(v_r_1483_, 1);
v_v_1490_ = lean_ctor_get(v_r_1483_, 2);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_r_1483_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; 
v_unused_1505_ = lean_ctor_get(v_r_1483_, 4);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_r_1483_, 3);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_r_1483_, 0);
lean_dec(v_unused_1507_);
v___x_1492_ = v_r_1483_;
v_isShared_1493_ = v_isSharedCheck_1504_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_v_1490_);
lean_inc(v_k_1489_);
lean_dec(v_r_1483_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1504_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_unsigned_to_nat(3u);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 4, v_l_1466_);
lean_ctor_set(v___x_1492_, 3, v_l_1466_);
lean_ctor_set(v___x_1492_, 2, v_v_1485_);
lean_ctor_set(v___x_1492_, 1, v_k_1484_);
lean_ctor_set(v___x_1492_, 0, v___x_1380_);
v___x_1496_ = v___x_1492_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_k_1484_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_v_1485_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_l_1466_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v_l_1466_);
v___x_1496_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 4, v_l_1466_);
lean_ctor_set(v___x_1487_, 2, v_v_1371_);
lean_ctor_set(v___x_1487_, 1, v_k_1370_);
lean_ctor_set(v___x_1487_, 0, v___x_1380_);
v___x_1498_ = v___x_1487_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_l_1466_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_l_1466_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v___x_1498_);
lean_ctor_set(v___x_1375_, 3, v___x_1496_);
lean_ctor_set(v___x_1375_, 2, v_v_1490_);
lean_ctor_set(v___x_1375_, 1, v_k_1489_);
lean_ctor_set(v___x_1375_, 0, v___x_1494_);
v___x_1500_ = v___x_1375_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v___x_1496_);
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
}
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_unsigned_to_nat(2u);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_r_1483_);
lean_ctor_set(v___x_1375_, 3, v_impl_1379_);
lean_ctor_set(v___x_1375_, 0, v___x_1512_);
v___x_1514_ = v___x_1375_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v_impl_1379_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_r_1483_);
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
case 1:
{
lean_object* v___x_1517_; 
lean_dec(v_v_1371_);
lean_dec(v_k_1370_);
lean_dec_ref(v_cmp_1365_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 2, v_v_1367_);
lean_ctor_set(v___x_1375_, 1, v_k_1366_);
v___x_1517_ = v___x_1375_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_size_1369_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_l_1372_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_r_1373_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
default: 
{
lean_object* v_impl_1519_; lean_object* v___x_1520_; 
lean_dec(v_size_1369_);
v_impl_1519_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1365_, v_k_1366_, v_v_1367_, v_r_1373_);
v___x_1520_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1372_) == 0)
{
lean_object* v_size_1521_; lean_object* v_size_1522_; lean_object* v_k_1523_; lean_object* v_v_1524_; lean_object* v_l_1525_; lean_object* v_r_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v_size_1521_ = lean_ctor_get(v_l_1372_, 0);
v_size_1522_ = lean_ctor_get(v_impl_1519_, 0);
lean_inc(v_size_1522_);
v_k_1523_ = lean_ctor_get(v_impl_1519_, 1);
lean_inc(v_k_1523_);
v_v_1524_ = lean_ctor_get(v_impl_1519_, 2);
lean_inc(v_v_1524_);
v_l_1525_ = lean_ctor_get(v_impl_1519_, 3);
lean_inc(v_l_1525_);
v_r_1526_ = lean_ctor_get(v_impl_1519_, 4);
lean_inc(v_r_1526_);
v___x_1527_ = lean_unsigned_to_nat(3u);
v___x_1528_ = lean_nat_mul(v___x_1527_, v_size_1521_);
v___x_1529_ = lean_nat_dec_lt(v___x_1528_, v_size_1522_);
lean_dec(v___x_1528_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
lean_dec(v_r_1526_);
lean_dec(v_l_1525_);
lean_dec(v_v_1524_);
lean_dec(v_k_1523_);
v___x_1530_ = lean_nat_add(v___x_1520_, v_size_1521_);
v___x_1531_ = lean_nat_add(v___x_1530_, v_size_1522_);
lean_dec(v_size_1522_);
lean_dec(v___x_1530_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_impl_1519_);
lean_ctor_set(v___x_1375_, 0, v___x_1531_);
v___x_1533_ = v___x_1375_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v_l_1372_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v_impl_1519_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
else
{
lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1598_; 
v_isSharedCheck_1598_ = !lean_is_exclusive(v_impl_1519_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; lean_object* v_unused_1602_; lean_object* v_unused_1603_; 
v_unused_1599_ = lean_ctor_get(v_impl_1519_, 4);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_impl_1519_, 3);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_impl_1519_, 2);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_impl_1519_, 1);
lean_dec(v_unused_1602_);
v_unused_1603_ = lean_ctor_get(v_impl_1519_, 0);
lean_dec(v_unused_1603_);
v___x_1536_ = v_impl_1519_;
v_isShared_1537_ = v_isSharedCheck_1598_;
goto v_resetjp_1535_;
}
else
{
lean_dec(v_impl_1519_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1598_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v_size_1538_; lean_object* v_k_1539_; lean_object* v_v_1540_; lean_object* v_l_1541_; lean_object* v_r_1542_; lean_object* v_size_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v_size_1538_ = lean_ctor_get(v_l_1525_, 0);
v_k_1539_ = lean_ctor_get(v_l_1525_, 1);
v_v_1540_ = lean_ctor_get(v_l_1525_, 2);
v_l_1541_ = lean_ctor_get(v_l_1525_, 3);
v_r_1542_ = lean_ctor_get(v_l_1525_, 4);
v_size_1543_ = lean_ctor_get(v_r_1526_, 0);
v___x_1544_ = lean_unsigned_to_nat(2u);
v___x_1545_ = lean_nat_mul(v___x_1544_, v_size_1543_);
v___x_1546_ = lean_nat_dec_lt(v_size_1538_, v___x_1545_);
lean_dec(v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1574_; 
lean_inc(v_r_1542_);
lean_inc(v_l_1541_);
lean_inc(v_v_1540_);
lean_inc(v_k_1539_);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_l_1525_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; lean_object* v_unused_1578_; lean_object* v_unused_1579_; 
v_unused_1575_ = lean_ctor_get(v_l_1525_, 4);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_l_1525_, 3);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_l_1525_, 2);
lean_dec(v_unused_1577_);
v_unused_1578_ = lean_ctor_get(v_l_1525_, 1);
lean_dec(v_unused_1578_);
v_unused_1579_ = lean_ctor_get(v_l_1525_, 0);
lean_dec(v_unused_1579_);
v___x_1548_ = v_l_1525_;
v_isShared_1549_ = v_isSharedCheck_1574_;
goto v_resetjp_1547_;
}
else
{
lean_dec(v_l_1525_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1574_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1564_; 
v___x_1550_ = lean_nat_add(v___x_1520_, v_size_1521_);
v___x_1551_ = lean_nat_add(v___x_1550_, v_size_1522_);
lean_dec(v_size_1522_);
if (lean_obj_tag(v_l_1541_) == 0)
{
lean_object* v_size_1572_; 
v_size_1572_ = lean_ctor_get(v_l_1541_, 0);
lean_inc(v_size_1572_);
v___y_1564_ = v_size_1572_;
goto v___jp_1563_;
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_unsigned_to_nat(0u);
v___y_1564_ = v___x_1573_;
goto v___jp_1563_;
}
v___jp_1552_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = lean_nat_add(v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec(v___y_1554_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v_r_1526_);
lean_ctor_set(v___x_1548_, 3, v_r_1542_);
lean_ctor_set(v___x_1548_, 2, v_v_1524_);
lean_ctor_set(v___x_1548_, 1, v_k_1523_);
lean_ctor_set(v___x_1548_, 0, v___x_1556_);
v___x_1558_ = v___x_1548_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1523_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1524_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_r_1542_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v_r_1526_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 4, v___x_1558_);
lean_ctor_set(v___x_1536_, 3, v___y_1553_);
lean_ctor_set(v___x_1536_, 2, v_v_1540_);
lean_ctor_set(v___x_1536_, 1, v_k_1539_);
lean_ctor_set(v___x_1536_, 0, v___x_1551_);
v___x_1560_ = v___x_1536_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_k_1539_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_v_1540_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v___y_1553_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
v___jp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1565_ = lean_nat_add(v___x_1550_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec(v___x_1550_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_l_1541_);
lean_ctor_set(v___x_1375_, 0, v___x_1565_);
v___x_1567_ = v___x_1375_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v_l_1372_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_l_1541_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_nat_add(v___x_1520_, v_size_1543_);
if (lean_obj_tag(v_r_1542_) == 0)
{
lean_object* v_size_1569_; 
v_size_1569_ = lean_ctor_get(v_r_1542_, 0);
lean_inc(v_size_1569_);
v___y_1553_ = v___x_1567_;
v___y_1554_ = v___x_1568_;
v___y_1555_ = v_size_1569_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_unsigned_to_nat(0u);
v___y_1553_ = v___x_1567_;
v___y_1554_ = v___x_1568_;
v___y_1555_ = v___x_1570_;
goto v___jp_1552_;
}
}
}
}
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
lean_del_object(v___x_1375_);
v___x_1580_ = lean_nat_add(v___x_1520_, v_size_1521_);
v___x_1581_ = lean_nat_add(v___x_1580_, v_size_1522_);
lean_dec(v_size_1522_);
v___x_1582_ = lean_nat_add(v___x_1580_, v_size_1538_);
lean_dec(v___x_1580_);
lean_inc_ref(v_l_1372_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 4, v_l_1525_);
lean_ctor_set(v___x_1536_, 3, v_l_1372_);
lean_ctor_set(v___x_1536_, 2, v_v_1371_);
lean_ctor_set(v___x_1536_, 1, v_k_1370_);
lean_ctor_set(v___x_1536_, 0, v___x_1582_);
v___x_1584_ = v___x_1536_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v_l_1372_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v_l_1525_);
v___x_1584_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
v_isSharedCheck_1591_ = !lean_is_exclusive(v_l_1372_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; lean_object* v_unused_1596_; 
v_unused_1592_ = lean_ctor_get(v_l_1372_, 4);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_l_1372_, 3);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_l_1372_, 2);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_l_1372_, 1);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_l_1372_, 0);
lean_dec(v_unused_1596_);
v___x_1586_ = v_l_1372_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v_l_1372_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 4, v_r_1526_);
lean_ctor_set(v___x_1586_, 3, v___x_1584_);
lean_ctor_set(v___x_1586_, 2, v_v_1524_);
lean_ctor_set(v___x_1586_, 1, v_k_1523_);
lean_ctor_set(v___x_1586_, 0, v___x_1581_);
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_k_1523_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_v_1524_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v_r_1526_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1604_; 
v_l_1604_ = lean_ctor_get(v_impl_1519_, 3);
lean_inc(v_l_1604_);
if (lean_obj_tag(v_l_1604_) == 0)
{
lean_object* v_r_1605_; lean_object* v_k_1606_; lean_object* v_v_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1630_; 
v_r_1605_ = lean_ctor_get(v_impl_1519_, 4);
v_k_1606_ = lean_ctor_get(v_impl_1519_, 1);
v_v_1607_ = lean_ctor_get(v_impl_1519_, 2);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_impl_1519_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; lean_object* v_unused_1632_; 
v_unused_1631_ = lean_ctor_get(v_impl_1519_, 3);
lean_dec(v_unused_1631_);
v_unused_1632_ = lean_ctor_get(v_impl_1519_, 0);
lean_dec(v_unused_1632_);
v___x_1609_ = v_impl_1519_;
v_isShared_1610_ = v_isSharedCheck_1630_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_r_1605_);
lean_inc(v_v_1607_);
lean_inc(v_k_1606_);
lean_dec(v_impl_1519_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1630_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_k_1611_; lean_object* v_v_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1626_; 
v_k_1611_ = lean_ctor_get(v_l_1604_, 1);
v_v_1612_ = lean_ctor_get(v_l_1604_, 2);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_l_1604_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; lean_object* v_unused_1628_; lean_object* v_unused_1629_; 
v_unused_1627_ = lean_ctor_get(v_l_1604_, 4);
lean_dec(v_unused_1627_);
v_unused_1628_ = lean_ctor_get(v_l_1604_, 3);
lean_dec(v_unused_1628_);
v_unused_1629_ = lean_ctor_get(v_l_1604_, 0);
lean_dec(v_unused_1629_);
v___x_1614_ = v_l_1604_;
v_isShared_1615_ = v_isSharedCheck_1626_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_v_1612_);
lean_inc(v_k_1611_);
lean_dec(v_l_1604_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1626_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1616_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1605_, 2);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 4, v_r_1605_);
lean_ctor_set(v___x_1614_, 3, v_r_1605_);
lean_ctor_set(v___x_1614_, 2, v_v_1371_);
lean_ctor_set(v___x_1614_, 1, v_k_1370_);
lean_ctor_set(v___x_1614_, 0, v___x_1520_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1625_, 3, v_r_1605_);
lean_ctor_set(v_reuseFailAlloc_1625_, 4, v_r_1605_);
v___x_1618_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1620_; 
lean_inc(v_r_1605_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 3, v_r_1605_);
lean_ctor_set(v___x_1609_, 0, v___x_1520_);
v___x_1620_ = v___x_1609_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_k_1606_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_v_1607_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v_r_1605_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v_r_1605_);
v___x_1620_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1622_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v___x_1620_);
lean_ctor_set(v___x_1375_, 3, v___x_1618_);
lean_ctor_set(v___x_1375_, 2, v_v_1612_);
lean_ctor_set(v___x_1375_, 1, v_k_1611_);
lean_ctor_set(v___x_1375_, 0, v___x_1616_);
v___x_1622_ = v___x_1375_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_k_1611_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_v_1612_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1623_, 4, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
}
else
{
lean_object* v_r_1633_; 
v_r_1633_ = lean_ctor_get(v_impl_1519_, 4);
lean_inc(v_r_1633_);
if (lean_obj_tag(v_r_1633_) == 0)
{
lean_object* v_k_1634_; lean_object* v_v_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1646_; 
v_k_1634_ = lean_ctor_get(v_impl_1519_, 1);
v_v_1635_ = lean_ctor_get(v_impl_1519_, 2);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_impl_1519_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; lean_object* v_unused_1648_; lean_object* v_unused_1649_; 
v_unused_1647_ = lean_ctor_get(v_impl_1519_, 4);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_impl_1519_, 3);
lean_dec(v_unused_1648_);
v_unused_1649_ = lean_ctor_get(v_impl_1519_, 0);
lean_dec(v_unused_1649_);
v___x_1637_ = v_impl_1519_;
v_isShared_1638_ = v_isSharedCheck_1646_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_v_1635_);
lean_inc(v_k_1634_);
lean_dec(v_impl_1519_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1646_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_unsigned_to_nat(3u);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v_l_1604_);
lean_ctor_set(v___x_1637_, 2, v_v_1371_);
lean_ctor_set(v___x_1637_, 1, v_k_1370_);
lean_ctor_set(v___x_1637_, 0, v___x_1520_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_l_1604_);
lean_ctor_set(v_reuseFailAlloc_1645_, 4, v_l_1604_);
v___x_1641_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_r_1633_);
lean_ctor_set(v___x_1375_, 3, v___x_1641_);
lean_ctor_set(v___x_1375_, 2, v_v_1635_);
lean_ctor_set(v___x_1375_, 1, v_k_1634_);
lean_ctor_set(v___x_1375_, 0, v___x_1639_);
v___x_1643_ = v___x_1375_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_k_1634_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_v_1635_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_r_1633_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_unsigned_to_nat(2u);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_impl_1519_);
lean_ctor_set(v___x_1375_, 3, v_r_1633_);
lean_ctor_set(v___x_1375_, 0, v___x_1650_);
v___x_1652_ = v___x_1375_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1653_, 3, v_r_1633_);
lean_ctor_set(v_reuseFailAlloc_1653_, 4, v_impl_1519_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
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
lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_dec_ref(v_cmp_1365_);
v___x_1655_ = lean_unsigned_to_nat(1u);
v___x_1656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v_k_1366_);
lean_ctor_set(v___x_1656_, 2, v_v_1367_);
lean_ctor_set(v___x_1656_, 3, v_t_1368_);
lean_ctor_set(v___x_1656_, 4, v_t_1368_);
return v___x_1656_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(lean_object* v_cmp_1657_, lean_object* v_k_1658_, lean_object* v_t_1659_){
_start:
{
if (lean_obj_tag(v_t_1659_) == 0)
{
lean_object* v_k_1660_; lean_object* v_l_1661_; lean_object* v_r_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v_k_1660_ = lean_ctor_get(v_t_1659_, 1);
lean_inc(v_k_1660_);
v_l_1661_ = lean_ctor_get(v_t_1659_, 3);
lean_inc(v_l_1661_);
v_r_1662_ = lean_ctor_get(v_t_1659_, 4);
lean_inc(v_r_1662_);
lean_dec_ref(v_t_1659_);
lean_inc_ref(v_cmp_1657_);
lean_inc(v_k_1658_);
v___x_1663_ = lean_apply_2(v_cmp_1657_, v_k_1658_, v_k_1660_);
v___x_1664_ = lean_unbox(v___x_1663_);
switch(v___x_1664_)
{
case 0:
{
lean_dec(v_r_1662_);
v_t_1659_ = v_l_1661_;
goto _start;
}
case 1:
{
uint8_t v___x_1666_; 
lean_dec(v_r_1662_);
lean_dec(v_l_1661_);
lean_dec(v_k_1658_);
lean_dec_ref(v_cmp_1657_);
v___x_1666_ = 1;
return v___x_1666_;
}
default: 
{
lean_dec(v_l_1661_);
v_t_1659_ = v_r_1662_;
goto _start;
}
}
}
else
{
uint8_t v___x_1668_; 
lean_dec(v_k_1658_);
lean_dec_ref(v_cmp_1657_);
v___x_1668_ = 0;
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg___boxed(lean_object* v_cmp_1669_, lean_object* v_k_1670_, lean_object* v_t_1671_){
_start:
{
uint8_t v_res_1672_; lean_object* v_r_1673_; 
v_res_1672_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1669_, v_k_1670_, v_t_1671_);
v_r_1673_ = lean_box(v_res_1672_);
return v_r_1673_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(lean_object* v_cmp_1674_, lean_object* v_as_x27_1675_, lean_object* v_b_1676_){
_start:
{
if (lean_obj_tag(v_as_x27_1675_) == 0)
{
lean_dec_ref(v_cmp_1674_);
return v_b_1676_;
}
else
{
lean_object* v_head_1677_; lean_object* v_tail_1678_; uint8_t v___x_1679_; 
v_head_1677_ = lean_ctor_get(v_as_x27_1675_, 0);
lean_inc_n(v_head_1677_, 2);
v_tail_1678_ = lean_ctor_get(v_as_x27_1675_, 1);
lean_inc(v_tail_1678_);
lean_dec_ref(v_as_x27_1675_);
lean_inc(v_b_1676_);
lean_inc_ref(v_cmp_1674_);
v___x_1679_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1674_, v_head_1677_, v_b_1676_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_box(0);
lean_inc_ref(v_cmp_1674_);
v___x_1681_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1674_, v_head_1677_, v___x_1680_, v_b_1676_);
v_as_x27_1675_ = v_tail_1678_;
v_b_1676_ = v___x_1681_;
goto _start;
}
else
{
lean_dec(v_head_1677_);
v_as_x27_1675_ = v_tail_1678_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___redArg(lean_object* v_l_1684_, lean_object* v_cmp_1685_){
_start:
{
lean_object* v_r_1686_; lean_object* v___x_1687_; 
v_r_1686_ = lean_box(1);
v___x_1687_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1685_, v_l_1684_, v_r_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList(lean_object* v_00_u03b1_1688_, lean_object* v_l_1689_, lean_object* v_cmp_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Std_ExtTreeSet_ofList___redArg(v_l_1689_, v_cmp_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(lean_object* v_00_u03b1_1692_, lean_object* v_cmp_1693_, lean_object* v_00_u03b2_1694_, lean_object* v_k_1695_, lean_object* v_t_1696_){
_start:
{
uint8_t v___x_1697_; 
v___x_1697_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1693_, v_k_1695_, v_t_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___boxed(lean_object* v_00_u03b1_1698_, lean_object* v_cmp_1699_, lean_object* v_00_u03b2_1700_, lean_object* v_k_1701_, lean_object* v_t_1702_){
_start:
{
uint8_t v_res_1703_; lean_object* v_r_1704_; 
v_res_1703_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(v_00_u03b1_1698_, v_cmp_1699_, v_00_u03b2_1700_, v_k_1701_, v_t_1702_);
v_r_1704_ = lean_box(v_res_1703_);
return v_r_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1(lean_object* v_00_u03b1_1705_, lean_object* v_cmp_1706_, lean_object* v_00_u03b2_1707_, lean_object* v_k_1708_, lean_object* v_v_1709_, lean_object* v_t_1710_, lean_object* v_hl_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1706_, v_k_1708_, v_v_1709_, v_t_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(lean_object* v_00_u03b1_1713_, lean_object* v_cmp_1714_, lean_object* v_as_1715_, lean_object* v_as_x27_1716_, lean_object* v_b_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1714_, v_as_x27_1716_, v_b_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___boxed(lean_object* v_00_u03b1_1720_, lean_object* v_cmp_1721_, lean_object* v_as_1722_, lean_object* v_as_x27_1723_, lean_object* v_b_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(v_00_u03b1_1720_, v_cmp_1721_, v_as_1722_, v_as_x27_1723_, v_b_1724_, v_a_1725_);
lean_dec(v_as_1722_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg___lam__0(lean_object* v_l_1727_, lean_object* v_k_1728_, lean_object* v_x_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_array_push(v_l_1727_, v_k_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg(lean_object* v_t_1732_){
_start:
{
lean_object* v___f_1733_; lean_object* v___y_1735_; 
v___f_1733_ = ((lean_object*)(l_Std_ExtTreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1732_) == 0)
{
lean_object* v_size_1738_; 
v_size_1738_ = lean_ctor_get(v_t_1732_, 0);
lean_inc(v_size_1738_);
v___y_1735_ = v_size_1738_;
goto v___jp_1734_;
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_unsigned_to_nat(0u);
v___y_1735_ = v___x_1739_;
goto v___jp_1734_;
}
v___jp_1734_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_mk_empty_array_with_capacity(v___y_1735_);
lean_dec(v___y_1735_);
v___x_1737_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1733_, v___x_1736_, v_t_1732_);
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray(lean_object* v_00_u03b1_1740_, lean_object* v_cmp_1741_, lean_object* v_inst_1742_, lean_object* v_t_1743_){
_start:
{
lean_object* v___f_1744_; lean_object* v___y_1746_; 
v___f_1744_ = ((lean_object*)(l_Std_ExtTreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1743_) == 0)
{
lean_object* v_size_1749_; 
v_size_1749_ = lean_ctor_get(v_t_1743_, 0);
lean_inc(v_size_1749_);
v___y_1746_ = v_size_1749_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_unsigned_to_nat(0u);
v___y_1746_ = v___x_1750_;
goto v___jp_1745_;
}
v___jp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_mk_empty_array_with_capacity(v___y_1746_);
lean_dec(v___y_1746_);
v___x_1748_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1744_, v___x_1747_, v_t_1743_);
return v___x_1748_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___boxed(lean_object* v_00_u03b1_1751_, lean_object* v_cmp_1752_, lean_object* v_inst_1753_, lean_object* v_t_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Std_ExtTreeSet_toArray(v_00_u03b1_1751_, v_cmp_1752_, v_inst_1753_, v_t_1754_);
lean_dec_ref(v_cmp_1752_);
return v_res_1755_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__26, &l_Std_ExtTreeSet___auto__1___closed__26_once, _init_l_Std_ExtTreeSet___auto__1___closed__26);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(lean_object* v_cmp_1757_, lean_object* v_as_1758_, size_t v_sz_1759_, size_t v_i_1760_, lean_object* v_b_1761_){
_start:
{
lean_object* v___y_1763_; uint8_t v___x_1767_; 
v___x_1767_ = lean_usize_dec_lt(v_i_1760_, v_sz_1759_);
if (v___x_1767_ == 0)
{
lean_dec_ref(v_cmp_1757_);
return v_b_1761_;
}
else
{
lean_object* v_a_1768_; uint8_t v___x_1769_; 
v_a_1768_ = lean_array_uget_borrowed(v_as_1758_, v_i_1760_);
lean_inc(v_b_1761_);
lean_inc(v_a_1768_);
lean_inc_ref(v_cmp_1757_);
v___x_1769_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1757_, v_a_1768_, v_b_1761_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_box(0);
lean_inc(v_a_1768_);
lean_inc_ref(v_cmp_1757_);
v___x_1771_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1757_, v_a_1768_, v___x_1770_, v_b_1761_);
v___y_1763_ = v___x_1771_;
goto v___jp_1762_;
}
else
{
v___y_1763_ = v_b_1761_;
goto v___jp_1762_;
}
}
v___jp_1762_:
{
size_t v___x_1764_; size_t v___x_1765_; 
v___x_1764_ = ((size_t)1ULL);
v___x_1765_ = lean_usize_add(v_i_1760_, v___x_1764_);
v_i_1760_ = v___x_1765_;
v_b_1761_ = v___y_1763_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg___boxed(lean_object* v_cmp_1772_, lean_object* v_as_1773_, lean_object* v_sz_1774_, lean_object* v_i_1775_, lean_object* v_b_1776_){
_start:
{
size_t v_sz_boxed_1777_; size_t v_i_boxed_1778_; lean_object* v_res_1779_; 
v_sz_boxed_1777_ = lean_unbox_usize(v_sz_1774_);
lean_dec(v_sz_1774_);
v_i_boxed_1778_ = lean_unbox_usize(v_i_1775_);
lean_dec(v_i_1775_);
v_res_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1772_, v_as_1773_, v_sz_boxed_1777_, v_i_boxed_1778_, v_b_1776_);
lean_dec_ref(v_as_1773_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg(lean_object* v_a_1780_, lean_object* v_cmp_1781_){
_start:
{
lean_object* v_r_1782_; size_t v_sz_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v_r_1782_ = lean_box(1);
v_sz_1783_ = lean_array_size(v_a_1780_);
v___x_1784_ = ((size_t)0ULL);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1781_, v_a_1780_, v_sz_1783_, v___x_1784_, v_r_1782_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg___boxed(lean_object* v_a_1786_, lean_object* v_cmp_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_1786_, v_cmp_1787_);
lean_dec_ref(v_a_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray(lean_object* v_00_u03b1_1789_, lean_object* v_a_1790_, lean_object* v_cmp_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_1790_, v_cmp_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___boxed(lean_object* v_00_u03b1_1793_, lean_object* v_a_1794_, lean_object* v_cmp_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Std_ExtTreeSet_ofArray(v_00_u03b1_1793_, v_a_1794_, v_cmp_1795_);
lean_dec_ref(v_a_1794_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(lean_object* v_00_u03b1_1797_, lean_object* v_cmp_1798_, lean_object* v_as_1799_, size_t v_sz_1800_, size_t v_i_1801_, lean_object* v_b_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1798_, v_as_1799_, v_sz_1800_, v_i_1801_, v_b_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___boxed(lean_object* v_00_u03b1_1804_, lean_object* v_cmp_1805_, lean_object* v_as_1806_, lean_object* v_sz_1807_, lean_object* v_i_1808_, lean_object* v_b_1809_){
_start:
{
size_t v_sz_boxed_1810_; size_t v_i_boxed_1811_; lean_object* v_res_1812_; 
v_sz_boxed_1810_ = lean_unbox_usize(v_sz_1807_);
lean_dec(v_sz_1807_);
v_i_boxed_1811_ = lean_unbox_usize(v_i_1808_);
lean_dec(v_i_1808_);
v_res_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(v_00_u03b1_1804_, v_cmp_1805_, v_as_1806_, v_sz_boxed_1810_, v_i_boxed_1811_, v_b_1809_);
lean_dec_ref(v_as_1806_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0(lean_object* v_b_u2082_1815_, lean_object* v_x_1816_){
_start:
{
if (lean_obj_tag(v_x_1816_) == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v_b_u2082_1815_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; 
v___x_1818_ = ((lean_object*)(l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0));
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1819_, lean_object* v_x_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Std_ExtTreeSet_merge___redArg___lam__0(v_b_u2082_1819_, v_x_1820_);
lean_dec(v_x_1820_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__1(lean_object* v_cmp_1822_, lean_object* v_t_1823_, lean_object* v_a_1824_, lean_object* v_b_u2082_1825_){
_start:
{
lean_object* v___f_1826_; lean_object* v___x_1827_; 
v___f_1826_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1826_, 0, v_b_u2082_1825_);
v___x_1827_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_1822_, v_a_1824_, v___f_1826_, v_t_1823_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg(lean_object* v_cmp_1828_, lean_object* v_t_u2081_1829_, lean_object* v_t_u2082_1830_){
_start:
{
lean_object* v___f_1831_; lean_object* v___x_1832_; 
v___f_1831_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1831_, 0, v_cmp_1828_);
v___x_1832_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1831_, v_t_u2081_1829_, v_t_u2082_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge(lean_object* v_00_u03b1_1833_, lean_object* v_cmp_1834_, lean_object* v_inst_1835_, lean_object* v_t_u2081_1836_, lean_object* v_t_u2082_1837_){
_start:
{
lean_object* v___f_1838_; lean_object* v___x_1839_; 
v___f_1838_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1838_, 0, v_cmp_1834_);
v___x_1839_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1838_, v_t_u2081_1836_, v_t_u2082_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg___lam__0(lean_object* v_cmp_1840_, lean_object* v_a_1841_, lean_object* v_____s_1842_){
_start:
{
uint8_t v___x_1843_; 
lean_inc(v_____s_1842_);
lean_inc(v_a_1841_);
lean_inc_ref(v_cmp_1840_);
v___x_1843_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1840_, v_a_1841_, v_____s_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_box(0);
v___x_1845_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1840_, v_a_1841_, v___x_1844_, v_____s_1842_);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; 
lean_dec(v_a_1841_);
lean_dec_ref(v_cmp_1840_);
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_____s_1842_);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg(lean_object* v_cmp_1848_, lean_object* v_inst_1849_, lean_object* v_t_1850_, lean_object* v_l_1851_){
_start:
{
lean_object* v___f_1852_; lean_object* v___x_1853_; 
v___f_1852_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1852_, 0, v_cmp_1848_);
v___x_1853_ = lean_apply_4(v_inst_1849_, lean_box(0), v_l_1851_, v_t_1850_, v___f_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany(lean_object* v_00_u03b1_1854_, lean_object* v_cmp_1855_, lean_object* v_inst_1856_, lean_object* v_00_u03c1_1857_, lean_object* v_inst_1858_, lean_object* v_t_1859_, lean_object* v_l_1860_){
_start:
{
lean_object* v___f_1861_; lean_object* v___x_1862_; 
v___f_1861_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1861_, 0, v_cmp_1855_);
v___x_1862_ = lean_apply_4(v_inst_1858_, lean_box(0), v_l_1860_, v_t_1859_, v___f_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union___redArg(lean_object* v_cmp_1863_, lean_object* v_t_u2081_1864_, lean_object* v_t_u2082_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1863_, v_t_u2081_1864_, v_t_u2082_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union(lean_object* v_00_u03b1_1867_, lean_object* v_cmp_1868_, lean_object* v_inst_1869_, lean_object* v_t_u2081_1870_, lean_object* v_t_u2082_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1868_, v_t_u2081_1870_, v_t_u2082_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp___redArg(lean_object* v_cmp_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_union), 5, 3);
lean_closure_set(v___x_1874_, 0, lean_box(0));
lean_closure_set(v___x_1874_, 1, v_cmp_1873_);
lean_closure_set(v___x_1874_, 2, lean_box(0));
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp(lean_object* v_00_u03b1_1875_, lean_object* v_cmp_1876_, lean_object* v_inst_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_union), 5, 3);
lean_closure_set(v___x_1878_, 0, lean_box(0));
lean_closure_set(v___x_1878_, 1, v_cmp_1876_);
lean_closure_set(v___x_1878_, 2, lean_box(0));
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter___redArg(lean_object* v_cmp_1879_, lean_object* v_t_u2081_1880_, lean_object* v_t_u2082_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1879_, v_t_u2081_1880_, v_t_u2082_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter(lean_object* v_00_u03b1_1883_, lean_object* v_cmp_1884_, lean_object* v_inst_1885_, lean_object* v_t_u2081_1886_, lean_object* v_t_u2082_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1884_, v_t_u2081_1886_, v_t_u2082_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp___redArg(lean_object* v_cmp_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_inter), 5, 3);
lean_closure_set(v___x_1890_, 0, lean_box(0));
lean_closure_set(v___x_1890_, 1, v_cmp_1889_);
lean_closure_set(v___x_1890_, 2, lean_box(0));
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp(lean_object* v_00_u03b1_1891_, lean_object* v_cmp_1892_, lean_object* v_inst_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_inter), 5, 3);
lean_closure_set(v___x_1894_, 0, lean_box(0));
lean_closure_set(v___x_1894_, 1, v_cmp_1892_);
lean_closure_set(v___x_1894_, 2, lean_box(0));
return v___x_1894_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___f_1896_; 
v___x_1895_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1896_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1896_, 0, v___x_1895_);
return v___f_1896_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(lean_object* v_cmp_1897_, lean_object* v_m_u2081_1898_, lean_object* v_m_u2082_1899_){
_start:
{
lean_object* v___f_1900_; uint8_t v___x_1901_; 
v___f_1900_ = lean_obj_once(&l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0, &l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once, _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0);
v___x_1901_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_1897_, v___f_1900_, v_m_u2081_1898_, v_m_u2082_1899_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_1902_, lean_object* v_m_u2081_1903_, lean_object* v_m_u2082_1904_){
_start:
{
uint8_t v_res_1905_; lean_object* v_r_1906_; 
v_res_1905_ = l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(v_cmp_1902_, v_m_u2081_1903_, v_m_u2082_1904_);
v_r_1906_ = lean_box(v_res_1905_);
return v_r_1906_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg(lean_object* v_cmp_1907_){
_start:
{
lean_object* v___f_1908_; 
v___f_1908_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1908_, 0, v_cmp_1907_);
return v___f_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp(lean_object* v_00_u03b1_1909_, lean_object* v_cmp_1910_, lean_object* v_inst_1911_){
_start:
{
lean_object* v___f_1912_; 
v___f_1912_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1912_, 0, v_cmp_1910_);
return v___f_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff___redArg(lean_object* v_cmp_1913_, lean_object* v_t_u2081_1914_, lean_object* v_t_u2082_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1913_, v_t_u2081_1914_, v_t_u2082_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff(lean_object* v_00_u03b1_1917_, lean_object* v_cmp_1918_, lean_object* v_inst_1919_, lean_object* v_t_u2081_1920_, lean_object* v_t_u2082_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1918_, v_t_u2081_1920_, v_t_u2082_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp___redArg(lean_object* v_cmp_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_diff), 5, 3);
lean_closure_set(v___x_1924_, 0, lean_box(0));
lean_closure_set(v___x_1924_, 1, v_cmp_1923_);
lean_closure_set(v___x_1924_, 2, lean_box(0));
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp(lean_object* v_00_u03b1_1925_, lean_object* v_cmp_1926_, lean_object* v_inst_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_diff), 5, 3);
lean_closure_set(v___x_1928_, 0, lean_box(0));
lean_closure_set(v___x_1928_, 1, v_cmp_1926_);
lean_closure_set(v___x_1928_, 2, lean_box(0));
return v___x_1928_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(lean_object* v_cmp_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_){
_start:
{
lean_object* v___f_1932_; uint8_t v___x_1933_; 
v___f_1932_ = lean_obj_once(&l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0, &l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once, _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0);
v___x_1933_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_1929_, v___f_1932_, v_x_1930_, v_x_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg___boxed(lean_object* v_cmp_1934_, lean_object* v_x_1935_, lean_object* v_x_1936_){
_start:
{
uint8_t v_res_1937_; lean_object* v_r_1938_; 
v_res_1937_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_1934_, v_x_1935_, v_x_1936_);
v_r_1938_ = lean_box(v_res_1937_);
return v_r_1938_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(lean_object* v_00_u03b1_1939_, lean_object* v_cmp_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_1940_, v_x_1943_, v_x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_cmp_1947_, lean_object* v_inst_1948_, lean_object* v_inst_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_){
_start:
{
uint8_t v_res_1952_; lean_object* v_r_1953_; 
v_res_1952_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(v_00_u03b1_1946_, v_cmp_1947_, v_inst_1948_, v_inst_1949_, v_x_1950_, v_x_1951_);
v_r_1953_ = lean_box(v_res_1952_);
return v_r_1953_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg___lam__0(lean_object* v_cmp_1954_, lean_object* v_a_1955_, lean_object* v_____s_1956_){
_start:
{
lean_object* v_acc_1957_; lean_object* v___x_1958_; 
v_acc_1957_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_1954_, v_a_1955_, v_____s_1956_);
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_acc_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg(lean_object* v_cmp_1959_, lean_object* v_inst_1960_, lean_object* v_t_1961_, lean_object* v_l_1962_){
_start:
{
lean_object* v___f_1963_; lean_object* v___x_1964_; 
v___f_1963_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1963_, 0, v_cmp_1959_);
v___x_1964_ = lean_apply_4(v_inst_1960_, lean_box(0), v_l_1962_, v_t_1961_, v___f_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany(lean_object* v_00_u03b1_1965_, lean_object* v_cmp_1966_, lean_object* v_inst_1967_, lean_object* v_00_u03c1_1968_, lean_object* v_inst_1969_, lean_object* v_t_1970_, lean_object* v_l_1971_){
_start:
{
lean_object* v___f_1972_; lean_object* v___x_1973_; 
v___f_1972_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1972_, 0, v_cmp_1966_);
v___x_1973_ = lean_apply_4(v_inst_1969_, lean_box(0), v_l_1971_, v_t_1970_, v___f_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_1977_, lean_object* v_inst_1978_, lean_object* v_m_1979_, lean_object* v_prec_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1981_ = ((lean_object*)(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_1982_ = lean_box(0);
v___x_1983_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1984_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1983_, v___f_1977_, v___x_1982_, v_m_1979_);
v___x_1985_ = l_List_repr___redArg(v_inst_1978_, v___x_1984_);
v___x_1986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1981_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = l_Repr_addAppParen(v___x_1986_, v_prec_1980_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_1988_, lean_object* v_inst_1989_, lean_object* v_m_1990_, lean_object* v_prec_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(v___f_1988_, v_inst_1989_, v_m_1990_, v_prec_1991_);
lean_dec(v_prec_1991_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg(lean_object* v_inst_1993_){
_start:
{
lean_object* v___f_1994_; lean_object* v___f_1995_; 
v___f_1994_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___f_1995_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1995_, 0, v___f_1994_);
lean_closure_set(v___f_1995_, 1, v_inst_1993_);
return v___f_1995_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp(lean_object* v_00_u03b1_1996_, lean_object* v_cmp_1997_, lean_object* v_inst_1998_, lean_object* v_inst_1999_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg(v_inst_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_2001_, lean_object* v_cmp_2002_, lean_object* v_inst_2003_, lean_object* v_inst_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Std_ExtTreeSet_instReprOfTransCmp(v_00_u03b1_2001_, v_cmp_2002_, v_inst_2003_, v_inst_2004_);
lean_dec_ref(v_cmp_2002_);
return v_res_2005_;
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
