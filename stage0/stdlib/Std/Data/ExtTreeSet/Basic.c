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
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___redArg(){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(1);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___redArg___boxed(lean_object* v___dummy_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_ExtTreeSet_empty___redArg();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty(lean_object* v_00_u03b1_79_, lean_object* v_cmp_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(1);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_empty___boxed(lean_object* v_00_u03b1_82_, lean_object* v_cmp_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_ExtTreeSet_empty(v_00_u03b1_82_, v_cmp_83_);
lean_dec_ref(v_cmp_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(1);
return v___x_86_;
}
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
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___redArg___boxed(lean_object* v___dummy_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_ExtTreeSet_instInhabited___redArg();
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited(lean_object* v_00_u03b1_99_, lean_object* v_cmp_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_box(1);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInhabited___boxed(lean_object* v_00_u03b1_102_, lean_object* v_cmp_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_ExtTreeSet_instInhabited(v_00_u03b1_102_, v_cmp_103_);
lean_dec_ref(v_cmp_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insert___redArg(lean_object* v_cmp_105_, lean_object* v_l_106_, lean_object* v_a_107_){
_start:
{
uint8_t v___x_108_; 
lean_inc(v_l_106_);
lean_inc(v_a_107_);
lean_inc_ref(v_cmp_105_);
v___x_108_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_105_, v_a_107_, v_l_106_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_box(0);
v___x_110_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_105_, v_a_107_, v___x_109_, v_l_106_);
return v___x_110_;
}
else
{
lean_dec(v_a_107_);
lean_dec_ref(v_cmp_105_);
return v_l_106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insert(lean_object* v_00_u03b1_111_, lean_object* v_cmp_112_, lean_object* v_inst_113_, lean_object* v_l_114_, lean_object* v_a_115_){
_start:
{
uint8_t v___x_116_; 
lean_inc(v_l_114_);
lean_inc(v_a_115_);
lean_inc_ref(v_cmp_112_);
v___x_116_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_112_, v_a_115_, v_l_114_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_box(0);
v___x_118_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_112_, v_a_115_, v___x_117_, v_l_114_);
return v___x_118_;
}
else
{
lean_dec(v_a_115_);
lean_dec_ref(v_cmp_112_);
return v_l_114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0(lean_object* v_cmp_119_, lean_object* v_e_120_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_box(1);
lean_inc(v_e_120_);
lean_inc_ref(v_cmp_119_);
v___x_122_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_119_, v_e_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_box(0);
v___x_124_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_119_, v_e_120_, v___x_123_, v___x_121_);
return v___x_124_;
}
else
{
lean_dec(v_e_120_);
lean_dec_ref(v_cmp_119_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg(lean_object* v_cmp_125_){
_start:
{
lean_object* v___f_126_; 
v___f_126_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_126_, 0, v_cmp_125_);
return v___f_126_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSingletonOfTransCmp(lean_object* v_00_u03b1_127_, lean_object* v_cmp_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v___f_130_; 
v___f_130_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_130_, 0, v_cmp_128_);
return v___f_130_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0(lean_object* v_cmp_131_, lean_object* v_e_132_, lean_object* v_s_133_){
_start:
{
uint8_t v___x_134_; 
lean_inc(v_s_133_);
lean_inc(v_e_132_);
lean_inc_ref(v_cmp_131_);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_131_, v_e_132_, v_s_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_box(0);
v___x_136_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_131_, v_e_132_, v___x_135_, v_s_133_);
return v___x_136_;
}
else
{
lean_dec(v_e_132_);
lean_dec_ref(v_cmp_131_);
return v_s_133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp___redArg(lean_object* v_cmp_137_){
_start:
{
lean_object* v___f_138_; 
v___f_138_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_138_, 0, v_cmp_137_);
return v___f_138_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInsertOfTransCmp(lean_object* v_00_u03b1_139_, lean_object* v_cmp_140_, lean_object* v_inst_141_){
_start:
{
lean_object* v___f_142_; 
v___f_142_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_142_, 0, v_cmp_140_);
return v___f_142_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_containsThenInsert___redArg(lean_object* v_cmp_143_, lean_object* v_t_144_, lean_object* v_a_145_){
_start:
{
uint8_t v___x_146_; 
lean_inc(v_t_144_);
lean_inc(v_a_145_);
lean_inc_ref(v_cmp_143_);
v___x_146_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_143_, v_a_145_, v_t_144_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_box(0);
v___x_148_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_143_, v_a_145_, v___x_147_, v_t_144_);
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
lean_dec_ref(v_cmp_143_);
v___x_151_ = lean_box(v___x_146_);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_t_144_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_containsThenInsert(lean_object* v_00_u03b1_153_, lean_object* v_cmp_154_, lean_object* v_inst_155_, lean_object* v_t_156_, lean_object* v_a_157_){
_start:
{
uint8_t v___x_158_; 
lean_inc(v_t_156_);
lean_inc(v_a_157_);
lean_inc_ref(v_cmp_154_);
v___x_158_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_154_, v_a_157_, v_t_156_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_159_ = lean_box(0);
v___x_160_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_154_, v_a_157_, v___x_159_, v_t_156_);
v___x_161_ = lean_box(v___x_158_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_a_157_);
lean_dec_ref(v_cmp_154_);
v___x_163_ = lean_box(v___x_158_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_t_156_);
return v___x_164_;
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_contains___redArg(lean_object* v_cmp_165_, lean_object* v_l_166_, lean_object* v_a_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_165_, v_a_167_, v_l_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_contains___redArg___boxed(lean_object* v_cmp_169_, lean_object* v_l_170_, lean_object* v_a_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Std_ExtTreeSet_contains___redArg(v_cmp_169_, v_l_170_, v_a_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_contains(lean_object* v_00_u03b1_174_, lean_object* v_cmp_175_, lean_object* v_inst_176_, lean_object* v_l_177_, lean_object* v_a_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_175_, v_a_178_, v_l_177_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_contains___boxed(lean_object* v_00_u03b1_180_, lean_object* v_cmp_181_, lean_object* v_inst_182_, lean_object* v_l_183_, lean_object* v_a_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Std_ExtTreeSet_contains(v_00_u03b1_180_, v_cmp_181_, v_inst_182_, v_l_183_, v_a_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg(){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(0);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg___boxed(lean_object* v___dummy_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_ExtTreeSet_instMembershipOfTransCmp___redArg();
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp(lean_object* v_00_u03b1_191_, lean_object* v_cmp_192_, lean_object* v_inst_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(0);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_195_, lean_object* v_cmp_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_ExtTreeSet_instMembershipOfTransCmp(v_00_u03b1_195_, v_cmp_196_, v_inst_197_);
lean_dec_ref(v_cmp_196_);
return v_res_198_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableMem___redArg(lean_object* v_cmp_199_, lean_object* v_m_200_, lean_object* v_a_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_199_, v_a_201_, v_m_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableMem___redArg___boxed(lean_object* v_cmp_203_, lean_object* v_m_204_, lean_object* v_a_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Std_ExtTreeSet_instDecidableMem___redArg(v_cmp_203_, v_m_204_, v_a_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableMem(lean_object* v_00_u03b1_208_, lean_object* v_cmp_209_, lean_object* v_inst_210_, lean_object* v_m_211_, lean_object* v_a_212_){
_start:
{
uint8_t v___x_213_; 
v___x_213_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_209_, v_a_212_, v_m_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableMem___boxed(lean_object* v_00_u03b1_214_, lean_object* v_cmp_215_, lean_object* v_inst_216_, lean_object* v_m_217_, lean_object* v_a_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_Std_ExtTreeSet_instDecidableMem(v_00_u03b1_214_, v_cmp_215_, v_inst_216_, v_m_217_, v_a_218_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___redArg(lean_object* v_t_221_){
_start:
{
if (lean_obj_tag(v_t_221_) == 0)
{
lean_object* v_size_222_; 
v_size_222_ = lean_ctor_get(v_t_221_, 0);
lean_inc(v_size_222_);
return v_size_222_;
}
else
{
lean_object* v___x_223_; 
v___x_223_ = lean_unsigned_to_nat(0u);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___redArg___boxed(lean_object* v_t_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_ExtTreeSet_size___redArg(v_t_224_);
lean_dec(v_t_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size(lean_object* v_00_u03b1_226_, lean_object* v_cmp_227_, lean_object* v_t_228_){
_start:
{
if (lean_obj_tag(v_t_228_) == 0)
{
lean_object* v_size_229_; 
v_size_229_ = lean_ctor_get(v_t_228_, 0);
lean_inc(v_size_229_);
return v_size_229_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = lean_unsigned_to_nat(0u);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_size___boxed(lean_object* v_00_u03b1_231_, lean_object* v_cmp_232_, lean_object* v_t_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_ExtTreeSet_size(v_00_u03b1_231_, v_cmp_232_, v_t_233_);
lean_dec(v_t_233_);
lean_dec_ref(v_cmp_232_);
return v_res_234_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_isEmpty___redArg(lean_object* v_t_235_){
_start:
{
if (lean_obj_tag(v_t_235_) == 0)
{
uint8_t v___x_236_; 
v___x_236_ = 0;
return v___x_236_;
}
else
{
uint8_t v___x_237_; 
v___x_237_ = 1;
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_isEmpty___redArg___boxed(lean_object* v_t_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Std_ExtTreeSet_isEmpty___redArg(v_t_238_);
lean_dec(v_t_238_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_isEmpty(lean_object* v_00_u03b1_241_, lean_object* v_cmp_242_, lean_object* v_t_243_){
_start:
{
if (lean_obj_tag(v_t_243_) == 0)
{
uint8_t v___x_244_; 
v___x_244_ = 0;
return v___x_244_;
}
else
{
uint8_t v___x_245_; 
v___x_245_ = 1;
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_isEmpty___boxed(lean_object* v_00_u03b1_246_, lean_object* v_cmp_247_, lean_object* v_t_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Std_ExtTreeSet_isEmpty(v_00_u03b1_246_, v_cmp_247_, v_t_248_);
lean_dec(v_t_248_);
lean_dec_ref(v_cmp_247_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_erase___redArg(lean_object* v_cmp_251_, lean_object* v_t_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_251_, v_a_253_, v_t_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_erase(lean_object* v_00_u03b1_255_, lean_object* v_cmp_256_, lean_object* v_inst_257_, lean_object* v_t_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_256_, v_a_259_, v_t_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x3f___redArg(lean_object* v_cmp_261_, lean_object* v_t_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_261_, v_t_262_, v_a_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x3f(lean_object* v_00_u03b1_265_, lean_object* v_cmp_266_, lean_object* v_inst_267_, lean_object* v_t_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_266_, v_t_268_, v_a_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get___redArg(lean_object* v_cmp_271_, lean_object* v_t_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_271_, v_t_272_, v_a_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get(lean_object* v_00_u03b1_275_, lean_object* v_cmp_276_, lean_object* v_inst_277_, lean_object* v_t_278_, lean_object* v_a_279_, lean_object* v_h_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_276_, v_t_278_, v_a_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___redArg(lean_object* v_cmp_282_, lean_object* v_inst_283_, lean_object* v_t_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_282_, v_t_284_, v_a_285_, v_inst_283_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___redArg___boxed(lean_object* v_cmp_287_, lean_object* v_inst_288_, lean_object* v_t_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_ExtTreeSet_get_x21___redArg(v_cmp_287_, v_inst_288_, v_t_289_, v_a_290_);
lean_dec(v_inst_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21(lean_object* v_00_u03b1_292_, lean_object* v_cmp_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_t_296_, lean_object* v_a_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_293_, v_t_296_, v_a_297_, v_inst_295_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_get_x21___boxed(lean_object* v_00_u03b1_299_, lean_object* v_cmp_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_t_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_ExtTreeSet_get_x21(v_00_u03b1_299_, v_cmp_300_, v_inst_301_, v_inst_302_, v_t_303_, v_a_304_);
lean_dec(v_inst_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg(lean_object* v_cmp_306_, lean_object* v_t_307_, lean_object* v_a_308_, lean_object* v_fallback_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_306_, v_t_307_, v_a_308_, v_fallback_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___redArg___boxed(lean_object* v_cmp_311_, lean_object* v_t_312_, lean_object* v_a_313_, lean_object* v_fallback_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_ExtTreeSet_getD___redArg(v_cmp_311_, v_t_312_, v_a_313_, v_fallback_314_);
lean_dec(v_fallback_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD(lean_object* v_00_u03b1_316_, lean_object* v_cmp_317_, lean_object* v_inst_318_, lean_object* v_t_319_, lean_object* v_a_320_, lean_object* v_fallback_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_317_, v_t_319_, v_a_320_, v_fallback_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getD___boxed(lean_object* v_00_u03b1_323_, lean_object* v_cmp_324_, lean_object* v_inst_325_, lean_object* v_t_326_, lean_object* v_a_327_, lean_object* v_fallback_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_ExtTreeSet_getD(v_00_u03b1_323_, v_cmp_324_, v_inst_325_, v_t_326_, v_a_327_, v_fallback_328_);
lean_dec(v_fallback_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg(lean_object* v_t_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___redArg___boxed(lean_object* v_t_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Std_ExtTreeSet_min_x3f___redArg(v_t_332_);
lean_dec(v_t_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f(lean_object* v_00_u03b1_334_, lean_object* v_cmp_335_, lean_object* v_inst_336_, lean_object* v_t_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x3f___boxed(lean_object* v_00_u03b1_339_, lean_object* v_cmp_340_, lean_object* v_inst_341_, lean_object* v_t_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_ExtTreeSet_min_x3f(v_00_u03b1_339_, v_cmp_340_, v_inst_341_, v_t_342_);
lean_dec(v_t_342_);
lean_dec_ref(v_cmp_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg(lean_object* v_t_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___redArg___boxed(lean_object* v_t_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_ExtTreeSet_min___redArg(v_t_346_);
lean_dec(v_t_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min(lean_object* v_00_u03b1_348_, lean_object* v_cmp_349_, lean_object* v_inst_350_, lean_object* v_t_351_, lean_object* v_h_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min___boxed(lean_object* v_00_u03b1_354_, lean_object* v_cmp_355_, lean_object* v_inst_356_, lean_object* v_t_357_, lean_object* v_h_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_ExtTreeSet_min(v_00_u03b1_354_, v_cmp_355_, v_inst_356_, v_t_357_, v_h_358_);
lean_dec(v_t_357_);
lean_dec_ref(v_cmp_355_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg(lean_object* v_inst_360_, lean_object* v_t_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_360_, v_t_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___redArg___boxed(lean_object* v_inst_363_, lean_object* v_t_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_ExtTreeSet_min_x21___redArg(v_inst_363_, v_t_364_);
lean_dec(v_t_364_);
lean_dec(v_inst_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21(lean_object* v_00_u03b1_366_, lean_object* v_cmp_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_t_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_369_, v_t_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_min_x21___boxed(lean_object* v_00_u03b1_372_, lean_object* v_cmp_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_t_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Std_ExtTreeSet_min_x21(v_00_u03b1_372_, v_cmp_373_, v_inst_374_, v_inst_375_, v_t_376_);
lean_dec(v_t_376_);
lean_dec(v_inst_375_);
lean_dec_ref(v_cmp_373_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg(lean_object* v_t_378_, lean_object* v_fallback_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_378_, v_fallback_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___redArg___boxed(lean_object* v_t_381_, lean_object* v_fallback_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_ExtTreeSet_minD___redArg(v_t_381_, v_fallback_382_);
lean_dec(v_fallback_382_);
lean_dec(v_t_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD(lean_object* v_00_u03b1_384_, lean_object* v_cmp_385_, lean_object* v_inst_386_, lean_object* v_t_387_, lean_object* v_fallback_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_387_, v_fallback_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_minD___boxed(lean_object* v_00_u03b1_390_, lean_object* v_cmp_391_, lean_object* v_inst_392_, lean_object* v_t_393_, lean_object* v_fallback_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_ExtTreeSet_minD(v_00_u03b1_390_, v_cmp_391_, v_inst_392_, v_t_393_, v_fallback_394_);
lean_dec(v_fallback_394_);
lean_dec(v_t_393_);
lean_dec_ref(v_cmp_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg(lean_object* v_t_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___redArg___boxed(lean_object* v_t_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_ExtTreeSet_max_x3f___redArg(v_t_398_);
lean_dec(v_t_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f(lean_object* v_00_u03b1_400_, lean_object* v_cmp_401_, lean_object* v_inst_402_, lean_object* v_t_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x3f___boxed(lean_object* v_00_u03b1_405_, lean_object* v_cmp_406_, lean_object* v_inst_407_, lean_object* v_t_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_ExtTreeSet_max_x3f(v_00_u03b1_405_, v_cmp_406_, v_inst_407_, v_t_408_);
lean_dec(v_t_408_);
lean_dec_ref(v_cmp_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg(lean_object* v_t_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___redArg___boxed(lean_object* v_t_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_ExtTreeSet_max___redArg(v_t_412_);
lean_dec(v_t_412_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max(lean_object* v_00_u03b1_414_, lean_object* v_cmp_415_, lean_object* v_inst_416_, lean_object* v_t_417_, lean_object* v_h_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max___boxed(lean_object* v_00_u03b1_420_, lean_object* v_cmp_421_, lean_object* v_inst_422_, lean_object* v_t_423_, lean_object* v_h_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_ExtTreeSet_max(v_00_u03b1_420_, v_cmp_421_, v_inst_422_, v_t_423_, v_h_424_);
lean_dec(v_t_423_);
lean_dec_ref(v_cmp_421_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg(lean_object* v_inst_426_, lean_object* v_t_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_426_, v_t_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___redArg___boxed(lean_object* v_inst_429_, lean_object* v_t_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_ExtTreeSet_max_x21___redArg(v_inst_429_, v_t_430_);
lean_dec(v_t_430_);
lean_dec(v_inst_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21(lean_object* v_00_u03b1_432_, lean_object* v_cmp_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_t_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_435_, v_t_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_max_x21___boxed(lean_object* v_00_u03b1_438_, lean_object* v_cmp_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_t_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Std_ExtTreeSet_max_x21(v_00_u03b1_438_, v_cmp_439_, v_inst_440_, v_inst_441_, v_t_442_);
lean_dec(v_t_442_);
lean_dec(v_inst_441_);
lean_dec_ref(v_cmp_439_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg(lean_object* v_t_444_, lean_object* v_fallback_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_444_, v_fallback_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___redArg___boxed(lean_object* v_t_447_, lean_object* v_fallback_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_ExtTreeSet_maxD___redArg(v_t_447_, v_fallback_448_);
lean_dec(v_fallback_448_);
lean_dec(v_t_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD(lean_object* v_00_u03b1_450_, lean_object* v_cmp_451_, lean_object* v_inst_452_, lean_object* v_t_453_, lean_object* v_fallback_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_453_, v_fallback_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_maxD___boxed(lean_object* v_00_u03b1_456_, lean_object* v_cmp_457_, lean_object* v_inst_458_, lean_object* v_t_459_, lean_object* v_fallback_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_ExtTreeSet_maxD(v_00_u03b1_456_, v_cmp_457_, v_inst_458_, v_t_459_, v_fallback_460_);
lean_dec(v_fallback_460_);
lean_dec(v_t_459_);
lean_dec_ref(v_cmp_457_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg(lean_object* v_t_462_, lean_object* v_n_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_462_, v_n_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___redArg___boxed(lean_object* v_t_465_, lean_object* v_n_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_ExtTreeSet_atIdx_x3f___redArg(v_t_465_, v_n_466_);
lean_dec(v_t_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f(lean_object* v_00_u03b1_468_, lean_object* v_cmp_469_, lean_object* v_inst_470_, lean_object* v_t_471_, lean_object* v_n_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_471_, v_n_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x3f___boxed(lean_object* v_00_u03b1_474_, lean_object* v_cmp_475_, lean_object* v_inst_476_, lean_object* v_t_477_, lean_object* v_n_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_ExtTreeSet_atIdx_x3f(v_00_u03b1_474_, v_cmp_475_, v_inst_476_, v_t_477_, v_n_478_);
lean_dec(v_t_477_);
lean_dec_ref(v_cmp_475_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg(lean_object* v_t_480_, lean_object* v_n_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_480_, v_n_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___redArg___boxed(lean_object* v_t_483_, lean_object* v_n_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_ExtTreeSet_atIdx___redArg(v_t_483_, v_n_484_);
lean_dec(v_t_483_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx(lean_object* v_00_u03b1_486_, lean_object* v_cmp_487_, lean_object* v_inst_488_, lean_object* v_t_489_, lean_object* v_n_490_, lean_object* v_h_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_489_, v_n_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx___boxed(lean_object* v_00_u03b1_493_, lean_object* v_cmp_494_, lean_object* v_inst_495_, lean_object* v_t_496_, lean_object* v_n_497_, lean_object* v_h_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_ExtTreeSet_atIdx(v_00_u03b1_493_, v_cmp_494_, v_inst_495_, v_t_496_, v_n_497_, v_h_498_);
lean_dec(v_t_496_);
lean_dec_ref(v_cmp_494_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg(lean_object* v_inst_500_, lean_object* v_t_501_, lean_object* v_n_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_500_, v_t_501_, v_n_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___redArg___boxed(lean_object* v_inst_504_, lean_object* v_t_505_, lean_object* v_n_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_ExtTreeSet_atIdx_x21___redArg(v_inst_504_, v_t_505_, v_n_506_);
lean_dec(v_t_505_);
lean_dec(v_inst_504_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21(lean_object* v_00_u03b1_508_, lean_object* v_cmp_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_t_512_, lean_object* v_n_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_511_, v_t_512_, v_n_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdx_x21___boxed(lean_object* v_00_u03b1_515_, lean_object* v_cmp_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_t_519_, lean_object* v_n_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_ExtTreeSet_atIdx_x21(v_00_u03b1_515_, v_cmp_516_, v_inst_517_, v_inst_518_, v_t_519_, v_n_520_);
lean_dec(v_t_519_);
lean_dec(v_inst_518_);
lean_dec_ref(v_cmp_516_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg(lean_object* v_t_522_, lean_object* v_n_523_, lean_object* v_fallback_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_522_, v_n_523_, v_fallback_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___redArg___boxed(lean_object* v_t_526_, lean_object* v_n_527_, lean_object* v_fallback_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_ExtTreeSet_atIdxD___redArg(v_t_526_, v_n_527_, v_fallback_528_);
lean_dec(v_fallback_528_);
lean_dec(v_t_526_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD(lean_object* v_00_u03b1_530_, lean_object* v_cmp_531_, lean_object* v_inst_532_, lean_object* v_t_533_, lean_object* v_n_534_, lean_object* v_fallback_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_533_, v_n_534_, v_fallback_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_atIdxD___boxed(lean_object* v_00_u03b1_537_, lean_object* v_cmp_538_, lean_object* v_inst_539_, lean_object* v_t_540_, lean_object* v_n_541_, lean_object* v_fallback_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_ExtTreeSet_atIdxD(v_00_u03b1_537_, v_cmp_538_, v_inst_539_, v_t_540_, v_n_541_, v_fallback_542_);
lean_dec(v_fallback_542_);
lean_dec(v_t_540_);
lean_dec_ref(v_cmp_538_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f___redArg(lean_object* v_cmp_544_, lean_object* v_t_545_, lean_object* v_k_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_box(0);
v___x_548_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_544_, v_k_546_, v___x_547_, v_t_545_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x3f(lean_object* v_00_u03b1_549_, lean_object* v_cmp_550_, lean_object* v_inst_551_, lean_object* v_t_552_, lean_object* v_k_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_box(0);
v___x_555_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_550_, v_k_553_, v___x_554_, v_t_552_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f___redArg(lean_object* v_cmp_556_, lean_object* v_t_557_, lean_object* v_k_558_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_box(0);
v___x_560_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_556_, v_k_558_, v___x_559_, v_t_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x3f(lean_object* v_00_u03b1_561_, lean_object* v_cmp_562_, lean_object* v_inst_563_, lean_object* v_t_564_, lean_object* v_k_565_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_box(0);
v___x_567_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_562_, v_k_565_, v___x_566_, v_t_564_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f___redArg(lean_object* v_cmp_568_, lean_object* v_t_569_, lean_object* v_k_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_box(0);
v___x_572_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_568_, v_k_570_, v___x_571_, v_t_569_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x3f(lean_object* v_00_u03b1_573_, lean_object* v_cmp_574_, lean_object* v_inst_575_, lean_object* v_t_576_, lean_object* v_k_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_box(0);
v___x_579_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_574_, v_k_577_, v___x_578_, v_t_576_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f___redArg(lean_object* v_cmp_580_, lean_object* v_t_581_, lean_object* v_k_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_box(0);
v___x_584_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_580_, v_k_582_, v___x_583_, v_t_581_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x3f(lean_object* v_00_u03b1_585_, lean_object* v_cmp_586_, lean_object* v_inst_587_, lean_object* v_t_588_, lean_object* v_k_589_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_box(0);
v___x_591_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_586_, v_k_589_, v___x_590_, v_t_588_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE___redArg(lean_object* v_cmp_592_, lean_object* v_t_593_, lean_object* v_k_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_592_, v_k_594_, v_t_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE(lean_object* v_00_u03b1_596_, lean_object* v_cmp_597_, lean_object* v_inst_598_, lean_object* v_t_599_, lean_object* v_k_600_, lean_object* v_h_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_597_, v_k_600_, v_t_599_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT___redArg(lean_object* v_cmp_603_, lean_object* v_t_604_, lean_object* v_k_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_603_, v_k_605_, v_t_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT(lean_object* v_00_u03b1_607_, lean_object* v_cmp_608_, lean_object* v_inst_609_, lean_object* v_t_610_, lean_object* v_k_611_, lean_object* v_h_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_608_, v_k_611_, v_t_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE___redArg(lean_object* v_cmp_614_, lean_object* v_t_615_, lean_object* v_k_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_614_, v_k_616_, v_t_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE(lean_object* v_00_u03b1_618_, lean_object* v_cmp_619_, lean_object* v_inst_620_, lean_object* v_t_621_, lean_object* v_k_622_, lean_object* v_h_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_619_, v_k_622_, v_t_621_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT___redArg(lean_object* v_cmp_625_, lean_object* v_t_626_, lean_object* v_k_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_625_, v_k_627_, v_t_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT(lean_object* v_00_u03b1_629_, lean_object* v_cmp_630_, lean_object* v_inst_631_, lean_object* v_t_632_, lean_object* v_k_633_, lean_object* v_h_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_630_, v_k_633_, v_t_632_);
return v___x_635_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_639_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__2));
v___x_640_ = lean_unsigned_to_nat(14u);
v___x_641_ = lean_unsigned_to_nat(22u);
v___x_642_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__1));
v___x_643_ = ((lean_object*)(l_Std_ExtTreeSet_getGE_x21___redArg___closed__0));
v___x_644_ = l_mkPanicMessageWithDecl(v___x_643_, v___x_642_, v___x_641_, v___x_640_, v___x_639_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___redArg(lean_object* v_cmp_645_, lean_object* v_inst_646_, lean_object* v_t_647_, lean_object* v_k_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_box(0);
v___x_650_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_645_, v_k_648_, v___x_649_, v_t_647_);
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
lean_dec_ref_known(v___x_650_, 1);
return v_val_653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___redArg___boxed(lean_object* v_cmp_654_, lean_object* v_inst_655_, lean_object* v_t_656_, lean_object* v_k_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_ExtTreeSet_getGE_x21___redArg(v_cmp_654_, v_inst_655_, v_t_656_, v_k_657_);
lean_dec(v_inst_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21(lean_object* v_00_u03b1_659_, lean_object* v_cmp_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_t_663_, lean_object* v_k_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_box(0);
v___x_666_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_660_, v_k_664_, v___x_665_, v_t_663_);
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
lean_dec_ref_known(v___x_666_, 1);
return v_val_669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGE_x21___boxed(lean_object* v_00_u03b1_670_, lean_object* v_cmp_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_t_674_, lean_object* v_k_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_ExtTreeSet_getGE_x21(v_00_u03b1_670_, v_cmp_671_, v_inst_672_, v_inst_673_, v_t_674_, v_k_675_);
lean_dec(v_inst_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg(lean_object* v_cmp_677_, lean_object* v_inst_678_, lean_object* v_t_679_, lean_object* v_k_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_box(0);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_677_, v_k_680_, v___x_681_, v_t_679_);
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
lean_dec_ref_known(v___x_682_, 1);
return v_val_685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___redArg___boxed(lean_object* v_cmp_686_, lean_object* v_inst_687_, lean_object* v_t_688_, lean_object* v_k_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_ExtTreeSet_getGT_x21___redArg(v_cmp_686_, v_inst_687_, v_t_688_, v_k_689_);
lean_dec(v_inst_687_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21(lean_object* v_00_u03b1_691_, lean_object* v_cmp_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_t_695_, lean_object* v_k_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_box(0);
v___x_698_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_692_, v_k_696_, v___x_697_, v_t_695_);
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
lean_dec_ref_known(v___x_698_, 1);
return v_val_701_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGT_x21___boxed(lean_object* v_00_u03b1_702_, lean_object* v_cmp_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_t_706_, lean_object* v_k_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_ExtTreeSet_getGT_x21(v_00_u03b1_702_, v_cmp_703_, v_inst_704_, v_inst_705_, v_t_706_, v_k_707_);
lean_dec(v_inst_705_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg(lean_object* v_cmp_709_, lean_object* v_inst_710_, lean_object* v_t_711_, lean_object* v_k_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_box(0);
v___x_714_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_709_, v_k_712_, v___x_713_, v_t_711_);
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
lean_dec_ref_known(v___x_714_, 1);
return v_val_717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___redArg___boxed(lean_object* v_cmp_718_, lean_object* v_inst_719_, lean_object* v_t_720_, lean_object* v_k_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_ExtTreeSet_getLE_x21___redArg(v_cmp_718_, v_inst_719_, v_t_720_, v_k_721_);
lean_dec(v_inst_719_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21(lean_object* v_00_u03b1_723_, lean_object* v_cmp_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_t_727_, lean_object* v_k_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_box(0);
v___x_730_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_724_, v_k_728_, v___x_729_, v_t_727_);
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
lean_dec_ref_known(v___x_730_, 1);
return v_val_733_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLE_x21___boxed(lean_object* v_00_u03b1_734_, lean_object* v_cmp_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_t_738_, lean_object* v_k_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_ExtTreeSet_getLE_x21(v_00_u03b1_734_, v_cmp_735_, v_inst_736_, v_inst_737_, v_t_738_, v_k_739_);
lean_dec(v_inst_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg(lean_object* v_cmp_741_, lean_object* v_inst_742_, lean_object* v_t_743_, lean_object* v_k_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_box(0);
v___x_746_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_741_, v_k_744_, v___x_745_, v_t_743_);
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
lean_dec_ref_known(v___x_746_, 1);
return v_val_749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___redArg___boxed(lean_object* v_cmp_750_, lean_object* v_inst_751_, lean_object* v_t_752_, lean_object* v_k_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_ExtTreeSet_getLT_x21___redArg(v_cmp_750_, v_inst_751_, v_t_752_, v_k_753_);
lean_dec(v_inst_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21(lean_object* v_00_u03b1_755_, lean_object* v_cmp_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_t_759_, lean_object* v_k_760_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_box(0);
v___x_762_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_756_, v_k_760_, v___x_761_, v_t_759_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_obj_once(&l_Std_ExtTreeSet_getGE_x21___redArg___closed__3, &l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3);
v___x_764_ = l_panic___redArg(v_inst_758_, v___x_763_);
return v___x_764_;
}
else
{
lean_object* v_val_765_; 
v_val_765_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_val_765_);
lean_dec_ref_known(v___x_762_, 1);
return v_val_765_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLT_x21___boxed(lean_object* v_00_u03b1_766_, lean_object* v_cmp_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_t_770_, lean_object* v_k_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_ExtTreeSet_getLT_x21(v_00_u03b1_766_, v_cmp_767_, v_inst_768_, v_inst_769_, v_t_770_, v_k_771_);
lean_dec(v_inst_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg(lean_object* v_cmp_773_, lean_object* v_t_774_, lean_object* v_k_775_, lean_object* v_fallback_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_box(0);
v___x_778_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_773_, v_k_775_, v___x_777_, v_t_774_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_inc(v_fallback_776_);
return v_fallback_776_;
}
else
{
lean_object* v_val_779_; 
v_val_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_val_779_);
lean_dec_ref_known(v___x_778_, 1);
return v_val_779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___redArg___boxed(lean_object* v_cmp_780_, lean_object* v_t_781_, lean_object* v_k_782_, lean_object* v_fallback_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_ExtTreeSet_getGED___redArg(v_cmp_780_, v_t_781_, v_k_782_, v_fallback_783_);
lean_dec(v_fallback_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED(lean_object* v_00_u03b1_785_, lean_object* v_cmp_786_, lean_object* v_inst_787_, lean_object* v_t_788_, lean_object* v_k_789_, lean_object* v_fallback_790_){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_box(0);
v___x_792_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_786_, v_k_789_, v___x_791_, v_t_788_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_inc(v_fallback_790_);
return v_fallback_790_;
}
else
{
lean_object* v_val_793_; 
v_val_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v___x_792_, 1);
return v_val_793_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGED___boxed(lean_object* v_00_u03b1_794_, lean_object* v_cmp_795_, lean_object* v_inst_796_, lean_object* v_t_797_, lean_object* v_k_798_, lean_object* v_fallback_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_ExtTreeSet_getGED(v_00_u03b1_794_, v_cmp_795_, v_inst_796_, v_t_797_, v_k_798_, v_fallback_799_);
lean_dec(v_fallback_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg(lean_object* v_cmp_801_, lean_object* v_t_802_, lean_object* v_k_803_, lean_object* v_fallback_804_){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_box(0);
v___x_806_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_801_, v_k_803_, v___x_805_, v_t_802_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_inc(v_fallback_804_);
return v_fallback_804_;
}
else
{
lean_object* v_val_807_; 
v_val_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_val_807_);
lean_dec_ref_known(v___x_806_, 1);
return v_val_807_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___redArg___boxed(lean_object* v_cmp_808_, lean_object* v_t_809_, lean_object* v_k_810_, lean_object* v_fallback_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_ExtTreeSet_getGTD___redArg(v_cmp_808_, v_t_809_, v_k_810_, v_fallback_811_);
lean_dec(v_fallback_811_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD(lean_object* v_00_u03b1_813_, lean_object* v_cmp_814_, lean_object* v_inst_815_, lean_object* v_t_816_, lean_object* v_k_817_, lean_object* v_fallback_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_box(0);
v___x_820_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_814_, v_k_817_, v___x_819_, v_t_816_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_inc(v_fallback_818_);
return v_fallback_818_;
}
else
{
lean_object* v_val_821_; 
v_val_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v___x_820_, 1);
return v_val_821_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getGTD___boxed(lean_object* v_00_u03b1_822_, lean_object* v_cmp_823_, lean_object* v_inst_824_, lean_object* v_t_825_, lean_object* v_k_826_, lean_object* v_fallback_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_ExtTreeSet_getGTD(v_00_u03b1_822_, v_cmp_823_, v_inst_824_, v_t_825_, v_k_826_, v_fallback_827_);
lean_dec(v_fallback_827_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg(lean_object* v_cmp_829_, lean_object* v_t_830_, lean_object* v_k_831_, lean_object* v_fallback_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_box(0);
v___x_834_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_829_, v_k_831_, v___x_833_, v_t_830_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_inc(v_fallback_832_);
return v_fallback_832_;
}
else
{
lean_object* v_val_835_; 
v_val_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v___x_834_, 1);
return v_val_835_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___redArg___boxed(lean_object* v_cmp_836_, lean_object* v_t_837_, lean_object* v_k_838_, lean_object* v_fallback_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_ExtTreeSet_getLED___redArg(v_cmp_836_, v_t_837_, v_k_838_, v_fallback_839_);
lean_dec(v_fallback_839_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED(lean_object* v_00_u03b1_841_, lean_object* v_cmp_842_, lean_object* v_inst_843_, lean_object* v_t_844_, lean_object* v_k_845_, lean_object* v_fallback_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_box(0);
v___x_848_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_842_, v_k_845_, v___x_847_, v_t_844_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_inc(v_fallback_846_);
return v_fallback_846_;
}
else
{
lean_object* v_val_849_; 
v_val_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_val_849_);
lean_dec_ref_known(v___x_848_, 1);
return v_val_849_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLED___boxed(lean_object* v_00_u03b1_850_, lean_object* v_cmp_851_, lean_object* v_inst_852_, lean_object* v_t_853_, lean_object* v_k_854_, lean_object* v_fallback_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_ExtTreeSet_getLED(v_00_u03b1_850_, v_cmp_851_, v_inst_852_, v_t_853_, v_k_854_, v_fallback_855_);
lean_dec(v_fallback_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg(lean_object* v_cmp_857_, lean_object* v_t_858_, lean_object* v_k_859_, lean_object* v_fallback_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_box(0);
v___x_862_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_857_, v_k_859_, v___x_861_, v_t_858_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_inc(v_fallback_860_);
return v_fallback_860_;
}
else
{
lean_object* v_val_863_; 
v_val_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v___x_862_, 1);
return v_val_863_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___redArg___boxed(lean_object* v_cmp_864_, lean_object* v_t_865_, lean_object* v_k_866_, lean_object* v_fallback_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_ExtTreeSet_getLTD___redArg(v_cmp_864_, v_t_865_, v_k_866_, v_fallback_867_);
lean_dec(v_fallback_867_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD(lean_object* v_00_u03b1_869_, lean_object* v_cmp_870_, lean_object* v_inst_871_, lean_object* v_t_872_, lean_object* v_k_873_, lean_object* v_fallback_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_box(0);
v___x_876_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_870_, v_k_873_, v___x_875_, v_t_872_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_inc(v_fallback_874_);
return v_fallback_874_;
}
else
{
lean_object* v_val_877_; 
v_val_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_val_877_);
lean_dec_ref_known(v___x_876_, 1);
return v_val_877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_getLTD___boxed(lean_object* v_00_u03b1_878_, lean_object* v_cmp_879_, lean_object* v_inst_880_, lean_object* v_t_881_, lean_object* v_k_882_, lean_object* v_fallback_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_ExtTreeSet_getLTD(v_00_u03b1_878_, v_cmp_879_, v_inst_880_, v_t_881_, v_k_882_, v_fallback_883_);
lean_dec(v_fallback_883_);
return v_res_884_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_filter___redArg___lam__0(lean_object* v_f_885_, lean_object* v_a_886_, lean_object* v_x_887_){
_start:
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_apply_1(v_f_885_, v_a_886_);
v___x_889_ = lean_unbox(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg___lam__0___boxed(lean_object* v_f_890_, lean_object* v_a_891_, lean_object* v_x_892_){
_start:
{
uint8_t v_res_893_; lean_object* v_r_894_; 
v_res_893_ = l_Std_ExtTreeSet_filter___redArg___lam__0(v_f_890_, v_a_891_, v_x_892_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___redArg(lean_object* v_f_895_, lean_object* v_m_896_){
_start:
{
lean_object* v___f_897_; lean_object* v___x_898_; 
v___f_897_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_897_, 0, v_f_895_);
v___x_898_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_897_, v_m_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter(lean_object* v_00_u03b1_899_, lean_object* v_cmp_900_, lean_object* v_f_901_, lean_object* v_m_902_){
_start:
{
lean_object* v___f_903_; lean_object* v___x_904_; 
v___f_903_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_903_, 0, v_f_901_);
v___x_904_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_903_, v_m_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_filter___boxed(lean_object* v_00_u03b1_905_, lean_object* v_cmp_906_, lean_object* v_f_907_, lean_object* v_m_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_ExtTreeSet_filter(v_00_u03b1_905_, v_cmp_906_, v_f_907_, v_m_908_);
lean_dec_ref(v_cmp_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg___lam__0(lean_object* v_f_910_, lean_object* v_c_911_, lean_object* v_a_912_, lean_object* v_x_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = lean_apply_2(v_f_910_, v_c_911_, v_a_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___redArg(lean_object* v_inst_915_, lean_object* v_f_916_, lean_object* v_init_917_, lean_object* v_t_918_){
_start:
{
lean_object* v___f_919_; lean_object* v___x_920_; 
v___f_919_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_919_, 0, v_f_916_);
v___x_920_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_915_, v___f_919_, v_init_917_, v_t_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM(lean_object* v_00_u03b1_921_, lean_object* v_cmp_922_, lean_object* v_00_u03b4_923_, lean_object* v_m_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_f_928_, lean_object* v_init_929_, lean_object* v_t_930_){
_start:
{
lean_object* v___f_931_; lean_object* v___x_932_; 
v___f_931_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_931_, 0, v_f_928_);
v___x_932_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_925_, v___f_931_, v_init_929_, v_t_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldlM___boxed(lean_object* v_00_u03b1_933_, lean_object* v_cmp_934_, lean_object* v_00_u03b4_935_, lean_object* v_m_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_f_940_, lean_object* v_init_941_, lean_object* v_t_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Std_ExtTreeSet_foldlM(v_00_u03b1_933_, v_cmp_934_, v_00_u03b4_935_, v_m_936_, v_inst_937_, v_inst_938_, v_inst_939_, v_f_940_, v_init_941_, v_t_942_);
lean_dec_ref(v_cmp_934_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___redArg(lean_object* v_f_944_, lean_object* v_init_945_, lean_object* v_t_946_){
_start:
{
lean_object* v___f_947_; lean_object* v___x_948_; 
v___f_947_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_947_, 0, v_f_944_);
v___x_948_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_947_, v_init_945_, v_t_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl(lean_object* v_00_u03b1_949_, lean_object* v_cmp_950_, lean_object* v_00_u03b4_951_, lean_object* v_inst_952_, lean_object* v_f_953_, lean_object* v_init_954_, lean_object* v_t_955_){
_start:
{
lean_object* v___f_956_; lean_object* v___x_957_; 
v___f_956_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_956_, 0, v_f_953_);
v___x_957_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_956_, v_init_954_, v_t_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldl___boxed(lean_object* v_00_u03b1_958_, lean_object* v_cmp_959_, lean_object* v_00_u03b4_960_, lean_object* v_inst_961_, lean_object* v_f_962_, lean_object* v_init_963_, lean_object* v_t_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_ExtTreeSet_foldl(v_00_u03b1_958_, v_cmp_959_, v_00_u03b4_960_, v_inst_961_, v_f_962_, v_init_963_, v_t_964_);
lean_dec_ref(v_cmp_959_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg___lam__0(lean_object* v_f_966_, lean_object* v_a_967_, lean_object* v_x_968_, lean_object* v_acc_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = lean_apply_2(v_f_966_, v_a_967_, v_acc_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___redArg(lean_object* v_inst_971_, lean_object* v_f_972_, lean_object* v_init_973_, lean_object* v_t_974_){
_start:
{
lean_object* v___f_975_; lean_object* v___x_976_; 
v___f_975_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_975_, 0, v_f_972_);
v___x_976_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_971_, v___f_975_, v_init_973_, v_t_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM(lean_object* v_00_u03b1_977_, lean_object* v_cmp_978_, lean_object* v_00_u03b4_979_, lean_object* v_m_980_, lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_f_984_, lean_object* v_init_985_, lean_object* v_t_986_){
_start:
{
lean_object* v___f_987_; lean_object* v___x_988_; 
v___f_987_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_987_, 0, v_f_984_);
v___x_988_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_981_, v___f_987_, v_init_985_, v_t_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldrM___boxed(lean_object* v_00_u03b1_989_, lean_object* v_cmp_990_, lean_object* v_00_u03b4_991_, lean_object* v_m_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_f_996_, lean_object* v_init_997_, lean_object* v_t_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Std_ExtTreeSet_foldrM(v_00_u03b1_989_, v_cmp_990_, v_00_u03b4_991_, v_m_992_, v_inst_993_, v_inst_994_, v_inst_995_, v_f_996_, v_init_997_, v_t_998_);
lean_dec_ref(v_cmp_990_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg___lam__0(lean_object* v_f_1000_, lean_object* v_x1_1001_, lean_object* v_x2_1002_, lean_object* v_x3_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_apply_2(v_f_1000_, v_x1_1001_, v_x3_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___redArg(lean_object* v_f_1024_, lean_object* v_init_1025_, lean_object* v_t_1026_){
_start:
{
lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___f_1027_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1027_, 0, v_f_1024_);
v___x_1028_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1029_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1028_, v___f_1027_, v_init_1025_, v_t_1026_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr(lean_object* v_00_u03b1_1030_, lean_object* v_cmp_1031_, lean_object* v_00_u03b4_1032_, lean_object* v_inst_1033_, lean_object* v_f_1034_, lean_object* v_init_1035_, lean_object* v_t_1036_){
_start:
{
lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___f_1037_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1037_, 0, v_f_1034_);
v___x_1038_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1039_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1038_, v___f_1037_, v_init_1035_, v_t_1036_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_foldr___boxed(lean_object* v_00_u03b1_1040_, lean_object* v_cmp_1041_, lean_object* v_00_u03b4_1042_, lean_object* v_inst_1043_, lean_object* v_f_1044_, lean_object* v_init_1045_, lean_object* v_t_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Std_ExtTreeSet_foldr(v_00_u03b1_1040_, v_cmp_1041_, v_00_u03b4_1042_, v_inst_1043_, v_f_1044_, v_init_1045_, v_t_1046_);
lean_dec_ref(v_cmp_1041_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg___lam__0(lean_object* v_f_1048_, lean_object* v_cmp_1049_, lean_object* v_x_1050_, lean_object* v_a_1051_, lean_object* v_b_1052_){
_start:
{
lean_object* v_fst_1053_; lean_object* v_snd_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1068_; 
v_fst_1053_ = lean_ctor_get(v_x_1050_, 0);
v_snd_1054_ = lean_ctor_get(v_x_1050_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_x_1050_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1056_ = v_x_1050_;
v_isShared_1057_ = v_isSharedCheck_1068_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_snd_1054_);
lean_inc(v_fst_1053_);
lean_dec(v_x_1050_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1068_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
lean_inc(v_a_1051_);
v___x_1058_ = lean_apply_1(v_f_1048_, v_a_1051_);
v___x_1059_ = lean_unbox(v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1049_, v_a_1051_, v_b_1052_, v_snd_1054_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1060_);
v___x_1062_ = v___x_1056_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_fst_1053_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1049_, v_a_1051_, v_b_1052_, v_fst_1053_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1064_);
v___x_1066_ = v___x_1056_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_snd_1054_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition___redArg(lean_object* v_cmp_1071_, lean_object* v_f_1072_, lean_object* v_t_1073_){
_start:
{
lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v_p_1076_; lean_object* v_fst_1077_; lean_object* v_snd_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v___f_1074_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1074_, 0, v_f_1072_);
lean_closure_set(v___f_1074_, 1, v_cmp_1071_);
v___x_1075_ = ((lean_object*)(l_Std_ExtTreeSet_partition___redArg___closed__0));
v_p_1076_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1074_, v___x_1075_, v_t_1073_);
v_fst_1077_ = lean_ctor_get(v_p_1076_, 0);
v_snd_1078_ = lean_ctor_get(v_p_1076_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_p_1076_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v_p_1076_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_snd_1078_);
lean_inc(v_fst_1077_);
lean_dec(v_p_1076_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_fst_1077_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_snd_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_partition(lean_object* v_00_u03b1_1086_, lean_object* v_cmp_1087_, lean_object* v_inst_1088_, lean_object* v_f_1089_, lean_object* v_t_1090_){
_start:
{
lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v_p_1093_; lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v___f_1091_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1091_, 0, v_f_1089_);
lean_closure_set(v___f_1091_, 1, v_cmp_1087_);
v___x_1092_ = ((lean_object*)(l_Std_ExtTreeSet_partition___redArg___closed__0));
v_p_1093_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1091_, v___x_1092_, v_t_1090_);
v_fst_1094_ = lean_ctor_get(v_p_1093_, 0);
v_snd_1095_ = lean_ctor_get(v_p_1093_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_p_1093_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v_p_1093_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_snd_1095_);
lean_inc(v_fst_1094_);
lean_dec(v_p_1093_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_fst_1094_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_snd_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg___lam__0(lean_object* v_f_1103_, lean_object* v_x_1104_, lean_object* v_k_1105_, lean_object* v_v_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_apply_1(v_f_1103_, v_k_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___redArg(lean_object* v_inst_1108_, lean_object* v_f_1109_, lean_object* v_t_1110_){
_start:
{
lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___f_1111_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1111_, 0, v_f_1109_);
v___x_1112_ = lean_box(0);
v___x_1113_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1108_, v___f_1111_, v___x_1112_, v_t_1110_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM(lean_object* v_00_u03b1_1114_, lean_object* v_cmp_1115_, lean_object* v_m_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_f_1120_, lean_object* v_t_1121_){
_start:
{
lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___f_1122_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1122_, 0, v_f_1120_);
v___x_1123_ = lean_box(0);
v___x_1124_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1117_, v___f_1122_, v___x_1123_, v_t_1121_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forM___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_cmp_1126_, lean_object* v_m_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_f_1131_, lean_object* v_t_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Std_ExtTreeSet_forM(v_00_u03b1_1125_, v_cmp_1126_, v_m_1127_, v_inst_1128_, v_inst_1129_, v_inst_1130_, v_f_1131_, v_t_1132_);
lean_dec_ref(v_cmp_1126_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__0(lean_object* v_f_1134_, lean_object* v_a_1135_, lean_object* v_b_1136_, lean_object* v_c_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_apply_2(v_f_1134_, v_a_1135_, v_c_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg___lam__1(lean_object* v_toPure_1139_, lean_object* v_____do__lift_1140_){
_start:
{
lean_object* v_a_1141_; lean_object* v___x_1142_; 
v_a_1141_ = lean_ctor_get(v_____do__lift_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref(v_____do__lift_1140_);
v___x_1142_ = lean_apply_2(v_toPure_1139_, lean_box(0), v_a_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___redArg(lean_object* v_inst_1143_, lean_object* v_f_1144_, lean_object* v_init_1145_, lean_object* v_t_1146_){
_start:
{
lean_object* v_toApplicative_1147_; lean_object* v_toBind_1148_; lean_object* v_toPure_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; lean_object* v___f_1152_; lean_object* v___x_1153_; 
v_toApplicative_1147_ = lean_ctor_get(v_inst_1143_, 0);
v_toBind_1148_ = lean_ctor_get(v_inst_1143_, 1);
lean_inc(v_toBind_1148_);
v_toPure_1149_ = lean_ctor_get(v_toApplicative_1147_, 1);
lean_inc(v_toPure_1149_);
v___f_1150_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1150_, 0, v_f_1144_);
v___x_1151_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1143_, v___f_1150_, v_init_1145_, v_t_1146_);
v___f_1152_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1152_, 0, v_toPure_1149_);
v___x_1153_ = lean_apply_4(v_toBind_1148_, lean_box(0), lean_box(0), v___x_1151_, v___f_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn(lean_object* v_00_u03b1_1154_, lean_object* v_cmp_1155_, lean_object* v_00_u03b4_1156_, lean_object* v_m_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_f_1161_, lean_object* v_init_1162_, lean_object* v_t_1163_){
_start:
{
lean_object* v_toApplicative_1164_; lean_object* v_toBind_1165_; lean_object* v_toPure_1166_; lean_object* v___f_1167_; lean_object* v___x_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; 
v_toApplicative_1164_ = lean_ctor_get(v_inst_1158_, 0);
v_toBind_1165_ = lean_ctor_get(v_inst_1158_, 1);
lean_inc(v_toBind_1165_);
v_toPure_1166_ = lean_ctor_get(v_toApplicative_1164_, 1);
lean_inc(v_toPure_1166_);
v___f_1167_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1167_, 0, v_f_1161_);
v___x_1168_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1158_, v___f_1167_, v_init_1162_, v_t_1163_);
v___f_1169_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1169_, 0, v_toPure_1166_);
v___x_1170_ = lean_apply_4(v_toBind_1165_, lean_box(0), lean_box(0), v___x_1168_, v___f_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_forIn___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_cmp_1172_, lean_object* v_00_u03b4_1173_, lean_object* v_m_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_f_1178_, lean_object* v_init_1179_, lean_object* v_t_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Std_ExtTreeSet_forIn(v_00_u03b1_1171_, v_cmp_1172_, v_00_u03b4_1173_, v_m_1174_, v_inst_1175_, v_inst_1176_, v_inst_1177_, v_f_1178_, v_init_1179_, v_t_1180_);
lean_dec_ref(v_cmp_1172_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_1182_, lean_object* v_t_1183_, lean_object* v_f_1184_){
_start:
{
lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___f_1185_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1185_, 0, v_f_1184_);
v___x_1186_ = lean_box(0);
v___x_1187_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1182_, v___f_1185_, v___x_1186_, v_t_1183_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1188_){
_start:
{
lean_object* v___f_1189_; 
v___f_1189_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1189_, 0, v_inst_1188_);
return v___f_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1190_, lean_object* v_cmp_1191_, lean_object* v_m_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_){
_start:
{
lean_object* v___f_1196_; 
v___f_1196_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1196_, 0, v_inst_1194_);
return v___f_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1197_, lean_object* v_cmp_1198_, lean_object* v_m_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(v_00_u03b1_1197_, v_cmp_1198_, v_m_1199_, v_inst_1200_, v_inst_1201_, v_inst_1202_);
lean_dec_ref(v_cmp_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_m_1206_, lean_object* v_init_1207_, lean_object* v_f_1208_){
_start:
{
lean_object* v_toApplicative_1209_; lean_object* v_toBind_1210_; lean_object* v_toPure_1211_; lean_object* v___f_1212_; lean_object* v___x_1213_; lean_object* v___f_1214_; lean_object* v___x_1215_; 
v_toApplicative_1209_ = lean_ctor_get(v_inst_1204_, 0);
v_toBind_1210_ = lean_ctor_get(v_inst_1204_, 1);
lean_inc(v_toBind_1210_);
v_toPure_1211_ = lean_ctor_get(v_toApplicative_1209_, 1);
lean_inc(v_toPure_1211_);
v___f_1212_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1212_, 0, v_f_1208_);
v___x_1213_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1204_, v___f_1212_, v_init_1207_, v_m_1206_);
v___f_1214_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1214_, 0, v_toPure_1211_);
v___x_1215_ = lean_apply_4(v_toBind_1210_, lean_box(0), lean_box(0), v___x_1213_, v___f_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1216_){
_start:
{
lean_object* v___f_1217_; 
v___f_1217_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1217_, 0, v_inst_1216_);
return v___f_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1218_, lean_object* v_cmp_1219_, lean_object* v_m_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_){
_start:
{
lean_object* v___f_1224_; 
v___f_1224_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1224_, 0, v_inst_1222_);
return v___f_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1225_, lean_object* v_cmp_1226_, lean_object* v_m_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(v_00_u03b1_1225_, v_cmp_1226_, v_m_1227_, v_inst_1228_, v_inst_1229_, v_inst_1230_);
lean_dec_ref(v_cmp_1226_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0(lean_object* v_p_1232_, lean_object* v___x_1233_, lean_object* v___x_1234_, lean_object* v_a_1235_, lean_object* v_b_1236_, lean_object* v_acc_1237_){
_start:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = lean_apply_1(v_p_1232_, v_a_1235_);
v___x_1239_ = lean_unbox(v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1233_);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref(v___x_1233_);
v___x_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1238_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v___x_1234_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___lam__0___boxed(lean_object* v_p_1244_, lean_object* v___x_1245_, lean_object* v___x_1246_, lean_object* v_a_1247_, lean_object* v_b_1248_, lean_object* v_acc_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Std_ExtTreeSet_any___redArg___lam__0(v_p_1244_, v___x_1245_, v___x_1246_, v_a_1247_, v_b_1248_, v_acc_1249_);
lean_dec_ref(v_acc_1249_);
return v_res_1250_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_any___redArg(lean_object* v_t_1254_, lean_object* v_p_1255_){
_start:
{
lean_object* v___y_1257_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v_a_1267_; 
v___x_1262_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1263_ = lean_box(0);
v___x_1264_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1265_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1265_, 0, v_p_1255_);
lean_closure_set(v___f_1265_, 1, v___x_1264_);
lean_closure_set(v___f_1265_, 2, v___x_1263_);
v___x_1266_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1262_, v___f_1265_, v___x_1264_, v_t_1254_);
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___y_1257_ = v_a_1267_;
goto v___jp_1256_;
v___jp_1256_:
{
lean_object* v_fst_1258_; 
v_fst_1258_ = lean_ctor_get(v___y_1257_, 0);
lean_inc(v_fst_1258_);
lean_dec_ref(v___y_1257_);
if (lean_obj_tag(v_fst_1258_) == 0)
{
uint8_t v___x_1259_; 
v___x_1259_ = 0;
return v___x_1259_;
}
else
{
lean_object* v_val_1260_; uint8_t v___x_1261_; 
v_val_1260_ = lean_ctor_get(v_fst_1258_, 0);
lean_inc(v_val_1260_);
lean_dec_ref_known(v_fst_1258_, 1);
v___x_1261_ = lean_unbox(v_val_1260_);
lean_dec(v_val_1260_);
return v___x_1261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___redArg___boxed(lean_object* v_t_1268_, lean_object* v_p_1269_){
_start:
{
uint8_t v_res_1270_; lean_object* v_r_1271_; 
v_res_1270_ = l_Std_ExtTreeSet_any___redArg(v_t_1268_, v_p_1269_);
v_r_1271_ = lean_box(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_any(lean_object* v_00_u03b1_1272_, lean_object* v_cmp_1273_, lean_object* v_inst_1274_, lean_object* v_t_1275_, lean_object* v_p_1276_){
_start:
{
lean_object* v___y_1278_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___f_1286_; lean_object* v___x_1287_; lean_object* v_a_1288_; 
v___x_1283_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1284_ = lean_box(0);
v___x_1285_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1286_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1286_, 0, v_p_1276_);
lean_closure_set(v___f_1286_, 1, v___x_1285_);
lean_closure_set(v___f_1286_, 2, v___x_1284_);
v___x_1287_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1283_, v___f_1286_, v___x_1285_, v_t_1275_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___y_1278_ = v_a_1288_;
goto v___jp_1277_;
v___jp_1277_:
{
lean_object* v_fst_1279_; 
v_fst_1279_ = lean_ctor_get(v___y_1278_, 0);
lean_inc(v_fst_1279_);
lean_dec_ref(v___y_1278_);
if (lean_obj_tag(v_fst_1279_) == 0)
{
uint8_t v___x_1280_; 
v___x_1280_ = 0;
return v___x_1280_;
}
else
{
lean_object* v_val_1281_; uint8_t v___x_1282_; 
v_val_1281_ = lean_ctor_get(v_fst_1279_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v_fst_1279_, 1);
v___x_1282_ = lean_unbox(v_val_1281_);
lean_dec(v_val_1281_);
return v___x_1282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_any___boxed(lean_object* v_00_u03b1_1289_, lean_object* v_cmp_1290_, lean_object* v_inst_1291_, lean_object* v_t_1292_, lean_object* v_p_1293_){
_start:
{
uint8_t v_res_1294_; lean_object* v_r_1295_; 
v_res_1294_ = l_Std_ExtTreeSet_any(v_00_u03b1_1289_, v_cmp_1290_, v_inst_1291_, v_t_1292_, v_p_1293_);
lean_dec_ref(v_cmp_1290_);
v_r_1295_ = lean_box(v_res_1294_);
return v_r_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0(lean_object* v_p_1296_, lean_object* v___x_1297_, lean_object* v___x_1298_, lean_object* v_a_1299_, lean_object* v_b_1300_, lean_object* v_acc_1301_){
_start:
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = lean_apply_1(v_p_1296_, v_a_1299_);
v___x_1303_ = lean_unbox(v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec_ref(v___x_1298_);
v___x_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___x_1297_);
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
else
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1298_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___lam__0___boxed(lean_object* v_p_1308_, lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v_a_1311_, lean_object* v_b_1312_, lean_object* v_acc_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Std_ExtTreeSet_all___redArg___lam__0(v_p_1308_, v___x_1309_, v___x_1310_, v_a_1311_, v_b_1312_, v_acc_1313_);
lean_dec_ref(v_acc_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_all___redArg(lean_object* v_t_1315_, lean_object* v_p_1316_){
_start:
{
lean_object* v___y_1318_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v_a_1328_; 
v___x_1323_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1324_ = lean_box(0);
v___x_1325_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1326_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1326_, 0, v_p_1316_);
lean_closure_set(v___f_1326_, 1, v___x_1324_);
lean_closure_set(v___f_1326_, 2, v___x_1325_);
v___x_1327_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1323_, v___f_1326_, v___x_1325_, v_t_1315_);
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___y_1318_ = v_a_1328_;
goto v___jp_1317_;
v___jp_1317_:
{
lean_object* v_fst_1319_; 
v_fst_1319_ = lean_ctor_get(v___y_1318_, 0);
lean_inc(v_fst_1319_);
lean_dec_ref(v___y_1318_);
if (lean_obj_tag(v_fst_1319_) == 0)
{
uint8_t v___x_1320_; 
v___x_1320_ = 1;
return v___x_1320_;
}
else
{
lean_object* v_val_1321_; uint8_t v___x_1322_; 
v_val_1321_ = lean_ctor_get(v_fst_1319_, 0);
lean_inc(v_val_1321_);
lean_dec_ref_known(v_fst_1319_, 1);
v___x_1322_ = lean_unbox(v_val_1321_);
lean_dec(v_val_1321_);
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___redArg___boxed(lean_object* v_t_1329_, lean_object* v_p_1330_){
_start:
{
uint8_t v_res_1331_; lean_object* v_r_1332_; 
v_res_1331_ = l_Std_ExtTreeSet_all___redArg(v_t_1329_, v_p_1330_);
v_r_1332_ = lean_box(v_res_1331_);
return v_r_1332_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_all(lean_object* v_00_u03b1_1333_, lean_object* v_cmp_1334_, lean_object* v_inst_1335_, lean_object* v_t_1336_, lean_object* v_p_1337_){
_start:
{
lean_object* v___y_1339_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; lean_object* v_a_1349_; 
v___x_1344_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1345_ = lean_box(0);
v___x_1346_ = ((lean_object*)(l_Std_ExtTreeSet_any___redArg___closed__0));
v___f_1347_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1347_, 0, v_p_1337_);
lean_closure_set(v___f_1347_, 1, v___x_1345_);
lean_closure_set(v___f_1347_, 2, v___x_1346_);
v___x_1348_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1344_, v___f_1347_, v___x_1346_, v_t_1336_);
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___y_1339_ = v_a_1349_;
goto v___jp_1338_;
v___jp_1338_:
{
lean_object* v_fst_1340_; 
v_fst_1340_ = lean_ctor_get(v___y_1339_, 0);
lean_inc(v_fst_1340_);
lean_dec_ref(v___y_1339_);
if (lean_obj_tag(v_fst_1340_) == 0)
{
uint8_t v___x_1341_; 
v___x_1341_ = 1;
return v___x_1341_;
}
else
{
lean_object* v_val_1342_; uint8_t v___x_1343_; 
v_val_1342_ = lean_ctor_get(v_fst_1340_, 0);
lean_inc(v_val_1342_);
lean_dec_ref_known(v_fst_1340_, 1);
v___x_1343_ = lean_unbox(v_val_1342_);
lean_dec(v_val_1342_);
return v___x_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_all___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_cmp_1351_, lean_object* v_inst_1352_, lean_object* v_t_1353_, lean_object* v_p_1354_){
_start:
{
uint8_t v_res_1355_; lean_object* v_r_1356_; 
v_res_1355_ = l_Std_ExtTreeSet_all(v_00_u03b1_1350_, v_cmp_1351_, v_inst_1352_, v_t_1353_, v_p_1354_);
lean_dec_ref(v_cmp_1351_);
v_r_1356_ = lean_box(v_res_1355_);
return v_r_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg___lam__0(lean_object* v_x1_1357_, lean_object* v_x2_1358_, lean_object* v_x3_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1360_, 0, v_x1_1357_);
lean_ctor_set(v___x_1360_, 1, v_x3_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___redArg(lean_object* v_t_1362_){
_start:
{
lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___f_1363_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___x_1364_ = lean_box(0);
v___x_1365_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1366_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1365_, v___f_1363_, v___x_1364_, v_t_1362_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList(lean_object* v_00_u03b1_1367_, lean_object* v_cmp_1368_, lean_object* v_inst_1369_, lean_object* v_t_1370_){
_start:
{
lean_object* v___f_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___f_1371_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___x_1372_ = lean_box(0);
v___x_1373_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_1374_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1373_, v___f_1371_, v___x_1372_, v_t_1370_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toList___boxed(lean_object* v_00_u03b1_1375_, lean_object* v_cmp_1376_, lean_object* v_inst_1377_, lean_object* v_t_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_ExtTreeSet_toList(v_00_u03b1_1375_, v_cmp_1376_, v_inst_1377_, v_t_1378_);
lean_dec_ref(v_cmp_1376_);
return v_res_1379_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_ofList___auto__1(void){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__26, &l_Std_ExtTreeSet___auto__1___closed__26_once, _init_l_Std_ExtTreeSet___auto__1___closed__26);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(lean_object* v_cmp_1381_, lean_object* v_k_1382_, lean_object* v_v_1383_, lean_object* v_t_1384_){
_start:
{
if (lean_obj_tag(v_t_1384_) == 0)
{
lean_object* v_size_1385_; lean_object* v_k_1386_; lean_object* v_v_1387_; lean_object* v_l_1388_; lean_object* v_r_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1670_; 
v_size_1385_ = lean_ctor_get(v_t_1384_, 0);
v_k_1386_ = lean_ctor_get(v_t_1384_, 1);
v_v_1387_ = lean_ctor_get(v_t_1384_, 2);
v_l_1388_ = lean_ctor_get(v_t_1384_, 3);
v_r_1389_ = lean_ctor_get(v_t_1384_, 4);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_t_1384_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1391_ = v_t_1384_;
v_isShared_1392_ = v_isSharedCheck_1670_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_r_1389_);
lean_inc(v_l_1388_);
lean_inc(v_v_1387_);
lean_inc(v_k_1386_);
lean_inc(v_size_1385_);
lean_dec(v_t_1384_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1670_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
lean_inc_ref(v_cmp_1381_);
lean_inc(v_k_1386_);
lean_inc(v_k_1382_);
v___x_1393_ = lean_apply_2(v_cmp_1381_, v_k_1382_, v_k_1386_);
v___x_1394_ = lean_unbox(v___x_1393_);
switch(v___x_1394_)
{
case 0:
{
lean_object* v_impl_1395_; lean_object* v___x_1396_; 
lean_dec(v_size_1385_);
v_impl_1395_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1381_, v_k_1382_, v_v_1383_, v_l_1388_);
v___x_1396_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1389_) == 0)
{
lean_object* v_size_1397_; lean_object* v_size_1398_; lean_object* v_k_1399_; lean_object* v_v_1400_; lean_object* v_l_1401_; lean_object* v_r_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_size_1397_ = lean_ctor_get(v_r_1389_, 0);
v_size_1398_ = lean_ctor_get(v_impl_1395_, 0);
lean_inc(v_size_1398_);
v_k_1399_ = lean_ctor_get(v_impl_1395_, 1);
lean_inc(v_k_1399_);
v_v_1400_ = lean_ctor_get(v_impl_1395_, 2);
lean_inc(v_v_1400_);
v_l_1401_ = lean_ctor_get(v_impl_1395_, 3);
lean_inc(v_l_1401_);
v_r_1402_ = lean_ctor_get(v_impl_1395_, 4);
lean_inc(v_r_1402_);
v___x_1403_ = lean_unsigned_to_nat(3u);
v___x_1404_ = lean_nat_mul(v___x_1403_, v_size_1397_);
v___x_1405_ = lean_nat_dec_lt(v___x_1404_, v_size_1398_);
lean_dec(v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_dec(v_r_1402_);
lean_dec(v_l_1401_);
lean_dec(v_v_1400_);
lean_dec(v_k_1399_);
v___x_1406_ = lean_nat_add(v___x_1396_, v_size_1398_);
lean_dec(v_size_1398_);
v___x_1407_ = lean_nat_add(v___x_1406_, v_size_1397_);
lean_dec(v___x_1406_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 3, v_impl_1395_);
lean_ctor_set(v___x_1391_, 0, v___x_1407_);
v___x_1409_ = v___x_1391_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_impl_1395_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_r_1389_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
else
{
lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1476_; 
v_isSharedCheck_1476_ = !lean_is_exclusive(v_impl_1395_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; lean_object* v_unused_1478_; lean_object* v_unused_1479_; lean_object* v_unused_1480_; lean_object* v_unused_1481_; 
v_unused_1477_ = lean_ctor_get(v_impl_1395_, 4);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_impl_1395_, 3);
lean_dec(v_unused_1478_);
v_unused_1479_ = lean_ctor_get(v_impl_1395_, 2);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_impl_1395_, 1);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_impl_1395_, 0);
lean_dec(v_unused_1481_);
v___x_1412_ = v_impl_1395_;
v_isShared_1413_ = v_isSharedCheck_1476_;
goto v_resetjp_1411_;
}
else
{
lean_dec(v_impl_1395_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1476_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_size_1414_; lean_object* v_size_1415_; lean_object* v_k_1416_; lean_object* v_v_1417_; lean_object* v_l_1418_; lean_object* v_r_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_size_1414_ = lean_ctor_get(v_l_1401_, 0);
v_size_1415_ = lean_ctor_get(v_r_1402_, 0);
v_k_1416_ = lean_ctor_get(v_r_1402_, 1);
v_v_1417_ = lean_ctor_get(v_r_1402_, 2);
v_l_1418_ = lean_ctor_get(v_r_1402_, 3);
v_r_1419_ = lean_ctor_get(v_r_1402_, 4);
v___x_1420_ = lean_unsigned_to_nat(2u);
v___x_1421_ = lean_nat_mul(v___x_1420_, v_size_1414_);
v___x_1422_ = lean_nat_dec_lt(v_size_1415_, v___x_1421_);
lean_dec(v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1451_; 
lean_inc(v_r_1419_);
lean_inc(v_l_1418_);
lean_inc(v_v_1417_);
lean_inc(v_k_1416_);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_r_1402_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; lean_object* v_unused_1455_; lean_object* v_unused_1456_; 
v_unused_1452_ = lean_ctor_get(v_r_1402_, 4);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_r_1402_, 3);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_r_1402_, 2);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_r_1402_, 1);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_r_1402_, 0);
lean_dec(v_unused_1456_);
v___x_1424_ = v_r_1402_;
v_isShared_1425_ = v_isSharedCheck_1451_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v_r_1402_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1451_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___x_1439_; lean_object* v___y_1441_; 
v___x_1426_ = lean_nat_add(v___x_1396_, v_size_1398_);
lean_dec(v_size_1398_);
v___x_1427_ = lean_nat_add(v___x_1426_, v_size_1397_);
lean_dec(v___x_1426_);
v___x_1439_ = lean_nat_add(v___x_1396_, v_size_1414_);
if (lean_obj_tag(v_l_1418_) == 0)
{
lean_object* v_size_1449_; 
v_size_1449_ = lean_ctor_get(v_l_1418_, 0);
lean_inc(v_size_1449_);
v___y_1441_ = v_size_1449_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_unsigned_to_nat(0u);
v___y_1441_ = v___x_1450_;
goto v___jp_1440_;
}
v___jp_1428_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_nat_add(v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec(v___y_1430_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v_r_1389_);
lean_ctor_set(v___x_1424_, 3, v_r_1419_);
lean_ctor_set(v___x_1424_, 2, v_v_1387_);
lean_ctor_set(v___x_1424_, 1, v_k_1386_);
lean_ctor_set(v___x_1424_, 0, v___x_1432_);
v___x_1434_ = v___x_1424_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v_r_1419_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v_r_1389_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1434_);
lean_ctor_set(v___x_1412_, 3, v___y_1429_);
lean_ctor_set(v___x_1412_, 2, v_v_1417_);
lean_ctor_set(v___x_1412_, 1, v_k_1416_);
lean_ctor_set(v___x_1412_, 0, v___x_1427_);
v___x_1436_ = v___x_1412_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_k_1416_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_v_1417_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v___y_1429_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
v___jp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = lean_nat_add(v___x_1439_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec(v___x_1439_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v_l_1418_);
lean_ctor_set(v___x_1391_, 3, v_l_1401_);
lean_ctor_set(v___x_1391_, 2, v_v_1400_);
lean_ctor_set(v___x_1391_, 1, v_k_1399_);
lean_ctor_set(v___x_1391_, 0, v___x_1442_);
v___x_1444_ = v___x_1391_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_l_1401_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v_l_1418_);
v___x_1444_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_nat_add(v___x_1396_, v_size_1397_);
if (lean_obj_tag(v_r_1419_) == 0)
{
lean_object* v_size_1446_; 
v_size_1446_ = lean_ctor_get(v_r_1419_, 0);
lean_inc(v_size_1446_);
v___y_1429_ = v___x_1444_;
v___y_1430_ = v___x_1445_;
v___y_1431_ = v_size_1446_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v___y_1429_ = v___x_1444_;
v___y_1430_ = v___x_1445_;
v___y_1431_ = v___x_1447_;
goto v___jp_1428_;
}
}
}
}
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_del_object(v___x_1391_);
v___x_1457_ = lean_nat_add(v___x_1396_, v_size_1398_);
lean_dec(v_size_1398_);
v___x_1458_ = lean_nat_add(v___x_1457_, v_size_1397_);
lean_dec(v___x_1457_);
v___x_1459_ = lean_nat_add(v___x_1396_, v_size_1397_);
v___x_1460_ = lean_nat_add(v___x_1459_, v_size_1415_);
lean_dec(v___x_1459_);
lean_inc_ref(v_r_1389_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v_r_1389_);
lean_ctor_set(v___x_1412_, 3, v_r_1402_);
lean_ctor_set(v___x_1412_, 2, v_v_1387_);
lean_ctor_set(v___x_1412_, 1, v_k_1386_);
lean_ctor_set(v___x_1412_, 0, v___x_1460_);
v___x_1462_ = v___x_1412_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_r_1402_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_r_1389_);
v___x_1462_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_isSharedCheck_1469_ = !lean_is_exclusive(v_r_1389_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; lean_object* v_unused_1473_; lean_object* v_unused_1474_; 
v_unused_1470_ = lean_ctor_get(v_r_1389_, 4);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_r_1389_, 3);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_r_1389_, 2);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_r_1389_, 1);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_r_1389_, 0);
lean_dec(v_unused_1474_);
v___x_1464_ = v_r_1389_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_dec(v_r_1389_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 4, v___x_1462_);
lean_ctor_set(v___x_1464_, 3, v_l_1401_);
lean_ctor_set(v___x_1464_, 2, v_v_1400_);
lean_ctor_set(v___x_1464_, 1, v_k_1399_);
lean_ctor_set(v___x_1464_, 0, v___x_1458_);
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_l_1401_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v___x_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1482_; 
v_l_1482_ = lean_ctor_get(v_impl_1395_, 3);
lean_inc(v_l_1482_);
if (lean_obj_tag(v_l_1482_) == 0)
{
lean_object* v_r_1483_; lean_object* v_k_1484_; lean_object* v_v_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1496_; 
v_r_1483_ = lean_ctor_get(v_impl_1395_, 4);
v_k_1484_ = lean_ctor_get(v_impl_1395_, 1);
v_v_1485_ = lean_ctor_get(v_impl_1395_, 2);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_impl_1395_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; 
v_unused_1497_ = lean_ctor_get(v_impl_1395_, 3);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_impl_1395_, 0);
lean_dec(v_unused_1498_);
v___x_1487_ = v_impl_1395_;
v_isShared_1488_ = v_isSharedCheck_1496_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_r_1483_);
lean_inc(v_v_1485_);
lean_inc(v_k_1484_);
lean_dec(v_impl_1395_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1496_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1483_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 3, v_r_1483_);
lean_ctor_set(v___x_1487_, 2, v_v_1387_);
lean_ctor_set(v___x_1487_, 1, v_k_1386_);
lean_ctor_set(v___x_1487_, 0, v___x_1396_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_r_1483_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_r_1483_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v___x_1491_);
lean_ctor_set(v___x_1391_, 3, v_l_1482_);
lean_ctor_set(v___x_1391_, 2, v_v_1485_);
lean_ctor_set(v___x_1391_, 1, v_k_1484_);
lean_ctor_set(v___x_1391_, 0, v___x_1489_);
v___x_1493_ = v___x_1391_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_k_1484_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_v_1485_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v_l_1482_);
lean_ctor_set(v_reuseFailAlloc_1494_, 4, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_r_1499_; 
v_r_1499_ = lean_ctor_get(v_impl_1395_, 4);
lean_inc(v_r_1499_);
if (lean_obj_tag(v_r_1499_) == 0)
{
lean_object* v_k_1500_; lean_object* v_v_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1524_; 
v_k_1500_ = lean_ctor_get(v_impl_1395_, 1);
v_v_1501_ = lean_ctor_get(v_impl_1395_, 2);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_impl_1395_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; lean_object* v_unused_1526_; lean_object* v_unused_1527_; 
v_unused_1525_ = lean_ctor_get(v_impl_1395_, 4);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_impl_1395_, 3);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v_impl_1395_, 0);
lean_dec(v_unused_1527_);
v___x_1503_ = v_impl_1395_;
v_isShared_1504_ = v_isSharedCheck_1524_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_v_1501_);
lean_inc(v_k_1500_);
lean_dec(v_impl_1395_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1524_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v_k_1505_; lean_object* v_v_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1520_; 
v_k_1505_ = lean_ctor_get(v_r_1499_, 1);
v_v_1506_ = lean_ctor_get(v_r_1499_, 2);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_r_1499_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; 
v_unused_1521_ = lean_ctor_get(v_r_1499_, 4);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_r_1499_, 3);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_r_1499_, 0);
lean_dec(v_unused_1523_);
v___x_1508_ = v_r_1499_;
v_isShared_1509_ = v_isSharedCheck_1520_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_v_1506_);
lean_inc(v_k_1505_);
lean_dec(v_r_1499_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1520_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = lean_unsigned_to_nat(3u);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v_l_1482_);
lean_ctor_set(v___x_1508_, 3, v_l_1482_);
lean_ctor_set(v___x_1508_, 2, v_v_1501_);
lean_ctor_set(v___x_1508_, 1, v_k_1500_);
lean_ctor_set(v___x_1508_, 0, v___x_1396_);
v___x_1512_ = v___x_1508_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_k_1500_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_v_1501_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_l_1482_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_l_1482_);
v___x_1512_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v_l_1482_);
lean_ctor_set(v___x_1503_, 2, v_v_1387_);
lean_ctor_set(v___x_1503_, 1, v_k_1386_);
lean_ctor_set(v___x_1503_, 0, v___x_1396_);
v___x_1514_ = v___x_1503_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_l_1482_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_l_1482_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v___x_1514_);
lean_ctor_set(v___x_1391_, 3, v___x_1512_);
lean_ctor_set(v___x_1391_, 2, v_v_1506_);
lean_ctor_set(v___x_1391_, 1, v_k_1505_);
lean_ctor_set(v___x_1391_, 0, v___x_1510_);
v___x_1516_ = v___x_1391_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1505_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1506_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1528_ = lean_unsigned_to_nat(2u);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v_r_1499_);
lean_ctor_set(v___x_1391_, 3, v_impl_1395_);
lean_ctor_set(v___x_1391_, 0, v___x_1528_);
v___x_1530_ = v___x_1391_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_impl_1395_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_r_1499_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1533_; 
lean_dec(v_v_1387_);
lean_dec(v_k_1386_);
lean_dec_ref(v_cmp_1381_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 2, v_v_1383_);
lean_ctor_set(v___x_1391_, 1, v_k_1382_);
v___x_1533_ = v___x_1391_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_size_1385_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_k_1382_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_v_1383_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v_l_1388_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v_r_1389_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
default: 
{
lean_object* v_impl_1535_; lean_object* v___x_1536_; 
lean_dec(v_size_1385_);
v_impl_1535_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1381_, v_k_1382_, v_v_1383_, v_r_1389_);
v___x_1536_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1388_) == 0)
{
lean_object* v_size_1537_; lean_object* v_size_1538_; lean_object* v_k_1539_; lean_object* v_v_1540_; lean_object* v_l_1541_; lean_object* v_r_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v_size_1537_ = lean_ctor_get(v_l_1388_, 0);
v_size_1538_ = lean_ctor_get(v_impl_1535_, 0);
lean_inc(v_size_1538_);
v_k_1539_ = lean_ctor_get(v_impl_1535_, 1);
lean_inc(v_k_1539_);
v_v_1540_ = lean_ctor_get(v_impl_1535_, 2);
lean_inc(v_v_1540_);
v_l_1541_ = lean_ctor_get(v_impl_1535_, 3);
lean_inc(v_l_1541_);
v_r_1542_ = lean_ctor_get(v_impl_1535_, 4);
lean_inc(v_r_1542_);
v___x_1543_ = lean_unsigned_to_nat(3u);
v___x_1544_ = lean_nat_mul(v___x_1543_, v_size_1537_);
v___x_1545_ = lean_nat_dec_lt(v___x_1544_, v_size_1538_);
lean_dec(v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
lean_dec(v_r_1542_);
lean_dec(v_l_1541_);
lean_dec(v_v_1540_);
lean_dec(v_k_1539_);
v___x_1546_ = lean_nat_add(v___x_1536_, v_size_1537_);
v___x_1547_ = lean_nat_add(v___x_1546_, v_size_1538_);
lean_dec(v_size_1538_);
lean_dec(v___x_1546_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v_impl_1535_);
lean_ctor_set(v___x_1391_, 0, v___x_1547_);
v___x_1549_ = v___x_1391_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_l_1388_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_impl_1535_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
else
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1614_; 
v_isSharedCheck_1614_ = !lean_is_exclusive(v_impl_1535_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; lean_object* v_unused_1616_; lean_object* v_unused_1617_; lean_object* v_unused_1618_; lean_object* v_unused_1619_; 
v_unused_1615_ = lean_ctor_get(v_impl_1535_, 4);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_impl_1535_, 3);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_impl_1535_, 2);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_impl_1535_, 1);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_impl_1535_, 0);
lean_dec(v_unused_1619_);
v___x_1552_ = v_impl_1535_;
v_isShared_1553_ = v_isSharedCheck_1614_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v_impl_1535_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1614_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v_size_1554_; lean_object* v_k_1555_; lean_object* v_v_1556_; lean_object* v_l_1557_; lean_object* v_r_1558_; lean_object* v_size_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v_size_1554_ = lean_ctor_get(v_l_1541_, 0);
v_k_1555_ = lean_ctor_get(v_l_1541_, 1);
v_v_1556_ = lean_ctor_get(v_l_1541_, 2);
v_l_1557_ = lean_ctor_get(v_l_1541_, 3);
v_r_1558_ = lean_ctor_get(v_l_1541_, 4);
v_size_1559_ = lean_ctor_get(v_r_1542_, 0);
v___x_1560_ = lean_unsigned_to_nat(2u);
v___x_1561_ = lean_nat_mul(v___x_1560_, v_size_1559_);
v___x_1562_ = lean_nat_dec_lt(v_size_1554_, v___x_1561_);
lean_dec(v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1590_; 
lean_inc(v_r_1558_);
lean_inc(v_l_1557_);
lean_inc(v_v_1556_);
lean_inc(v_k_1555_);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_l_1541_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1591_ = lean_ctor_get(v_l_1541_, 4);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_l_1541_, 3);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_l_1541_, 2);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_l_1541_, 1);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_l_1541_, 0);
lean_dec(v_unused_1595_);
v___x_1564_ = v_l_1541_;
v_isShared_1565_ = v_isSharedCheck_1590_;
goto v_resetjp_1563_;
}
else
{
lean_dec(v_l_1541_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1590_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1580_; 
v___x_1566_ = lean_nat_add(v___x_1536_, v_size_1537_);
v___x_1567_ = lean_nat_add(v___x_1566_, v_size_1538_);
lean_dec(v_size_1538_);
if (lean_obj_tag(v_l_1557_) == 0)
{
lean_object* v_size_1588_; 
v_size_1588_ = lean_ctor_get(v_l_1557_, 0);
lean_inc(v_size_1588_);
v___y_1580_ = v_size_1588_;
goto v___jp_1579_;
}
else
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_unsigned_to_nat(0u);
v___y_1580_ = v___x_1589_;
goto v___jp_1579_;
}
v___jp_1568_:
{
lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1572_ = lean_nat_add(v___y_1569_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec(v___y_1569_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 4, v_r_1542_);
lean_ctor_set(v___x_1564_, 3, v_r_1558_);
lean_ctor_set(v___x_1564_, 2, v_v_1540_);
lean_ctor_set(v___x_1564_, 1, v_k_1539_);
lean_ctor_set(v___x_1564_, 0, v___x_1572_);
v___x_1574_ = v___x_1564_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_k_1539_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_v_1540_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_r_1558_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v_r_1542_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 4, v___x_1574_);
lean_ctor_set(v___x_1552_, 3, v___y_1570_);
lean_ctor_set(v___x_1552_, 2, v_v_1556_);
lean_ctor_set(v___x_1552_, 1, v_k_1555_);
lean_ctor_set(v___x_1552_, 0, v___x_1567_);
v___x_1576_ = v___x_1552_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v___y_1570_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
v___jp_1579_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = lean_nat_add(v___x_1566_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec(v___x_1566_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v_l_1557_);
lean_ctor_set(v___x_1391_, 0, v___x_1581_);
v___x_1583_ = v___x_1391_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v_l_1388_);
lean_ctor_set(v_reuseFailAlloc_1587_, 4, v_l_1557_);
v___x_1583_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_nat_add(v___x_1536_, v_size_1559_);
if (lean_obj_tag(v_r_1558_) == 0)
{
lean_object* v_size_1585_; 
v_size_1585_ = lean_ctor_get(v_r_1558_, 0);
lean_inc(v_size_1585_);
v___y_1569_ = v___x_1584_;
v___y_1570_ = v___x_1583_;
v___y_1571_ = v_size_1585_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_unsigned_to_nat(0u);
v___y_1569_ = v___x_1584_;
v___y_1570_ = v___x_1583_;
v___y_1571_ = v___x_1586_;
goto v___jp_1568_;
}
}
}
}
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
lean_del_object(v___x_1391_);
v___x_1596_ = lean_nat_add(v___x_1536_, v_size_1537_);
v___x_1597_ = lean_nat_add(v___x_1596_, v_size_1538_);
lean_dec(v_size_1538_);
v___x_1598_ = lean_nat_add(v___x_1596_, v_size_1554_);
lean_dec(v___x_1596_);
lean_inc_ref(v_l_1388_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 4, v_l_1541_);
lean_ctor_set(v___x_1552_, 3, v_l_1388_);
lean_ctor_set(v___x_1552_, 2, v_v_1387_);
lean_ctor_set(v___x_1552_, 1, v_k_1386_);
lean_ctor_set(v___x_1552_, 0, v___x_1598_);
v___x_1600_ = v___x_1552_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_l_1388_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_l_1541_);
v___x_1600_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_isSharedCheck_1607_ = !lean_is_exclusive(v_l_1388_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; lean_object* v_unused_1609_; lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; 
v_unused_1608_ = lean_ctor_get(v_l_1388_, 4);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_l_1388_, 3);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_l_1388_, 2);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_l_1388_, 1);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_l_1388_, 0);
lean_dec(v_unused_1612_);
v___x_1602_ = v_l_1388_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_dec(v_l_1388_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 4, v_r_1542_);
lean_ctor_set(v___x_1602_, 3, v___x_1600_);
lean_ctor_set(v___x_1602_, 2, v_v_1540_);
lean_ctor_set(v___x_1602_, 1, v_k_1539_);
lean_ctor_set(v___x_1602_, 0, v___x_1597_);
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_k_1539_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_v_1540_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_r_1542_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1620_; 
v_l_1620_ = lean_ctor_get(v_impl_1535_, 3);
lean_inc(v_l_1620_);
if (lean_obj_tag(v_l_1620_) == 0)
{
lean_object* v_r_1621_; lean_object* v_k_1622_; lean_object* v_v_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1646_; 
v_r_1621_ = lean_ctor_get(v_impl_1535_, 4);
v_k_1622_ = lean_ctor_get(v_impl_1535_, 1);
v_v_1623_ = lean_ctor_get(v_impl_1535_, 2);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_impl_1535_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; lean_object* v_unused_1648_; 
v_unused_1647_ = lean_ctor_get(v_impl_1535_, 3);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_impl_1535_, 0);
lean_dec(v_unused_1648_);
v___x_1625_ = v_impl_1535_;
v_isShared_1626_ = v_isSharedCheck_1646_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_r_1621_);
lean_inc(v_v_1623_);
lean_inc(v_k_1622_);
lean_dec(v_impl_1535_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1646_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_k_1627_; lean_object* v_v_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1642_; 
v_k_1627_ = lean_ctor_get(v_l_1620_, 1);
v_v_1628_ = lean_ctor_get(v_l_1620_, 2);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_l_1620_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; lean_object* v_unused_1644_; lean_object* v_unused_1645_; 
v_unused_1643_ = lean_ctor_get(v_l_1620_, 4);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_l_1620_, 3);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_l_1620_, 0);
lean_dec(v_unused_1645_);
v___x_1630_ = v_l_1620_;
v_isShared_1631_ = v_isSharedCheck_1642_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_v_1628_);
lean_inc(v_k_1627_);
lean_dec(v_l_1620_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1642_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1632_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1621_, 2);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 4, v_r_1621_);
lean_ctor_set(v___x_1630_, 3, v_r_1621_);
lean_ctor_set(v___x_1630_, 2, v_v_1387_);
lean_ctor_set(v___x_1630_, 1, v_k_1386_);
lean_ctor_set(v___x_1630_, 0, v___x_1536_);
v___x_1634_ = v___x_1630_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_r_1621_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_r_1621_);
v___x_1634_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
lean_inc(v_r_1621_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 3, v_r_1621_);
lean_ctor_set(v___x_1625_, 0, v___x_1536_);
v___x_1636_ = v___x_1625_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_k_1622_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_v_1623_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_r_1621_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_r_1621_);
v___x_1636_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v___x_1636_);
lean_ctor_set(v___x_1391_, 3, v___x_1634_);
lean_ctor_set(v___x_1391_, 2, v_v_1628_);
lean_ctor_set(v___x_1391_, 1, v_k_1627_);
lean_ctor_set(v___x_1391_, 0, v___x_1632_);
v___x_1638_ = v___x_1391_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1627_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1628_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
else
{
lean_object* v_r_1649_; 
v_r_1649_ = lean_ctor_get(v_impl_1535_, 4);
lean_inc(v_r_1649_);
if (lean_obj_tag(v_r_1649_) == 0)
{
lean_object* v_k_1650_; lean_object* v_v_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1662_; 
v_k_1650_ = lean_ctor_get(v_impl_1535_, 1);
v_v_1651_ = lean_ctor_get(v_impl_1535_, 2);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_impl_1535_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; lean_object* v_unused_1664_; lean_object* v_unused_1665_; 
v_unused_1663_ = lean_ctor_get(v_impl_1535_, 4);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v_impl_1535_, 3);
lean_dec(v_unused_1664_);
v_unused_1665_ = lean_ctor_get(v_impl_1535_, 0);
lean_dec(v_unused_1665_);
v___x_1653_ = v_impl_1535_;
v_isShared_1654_ = v_isSharedCheck_1662_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_v_1651_);
lean_inc(v_k_1650_);
lean_dec(v_impl_1535_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1662_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_unsigned_to_nat(3u);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 4, v_l_1620_);
lean_ctor_set(v___x_1653_, 2, v_v_1387_);
lean_ctor_set(v___x_1653_, 1, v_k_1386_);
lean_ctor_set(v___x_1653_, 0, v___x_1536_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_l_1620_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_l_1620_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v_r_1649_);
lean_ctor_set(v___x_1391_, 3, v___x_1657_);
lean_ctor_set(v___x_1391_, 2, v_v_1651_);
lean_ctor_set(v___x_1391_, 1, v_k_1650_);
lean_ctor_set(v___x_1391_, 0, v___x_1655_);
v___x_1659_ = v___x_1391_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1650_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1651_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_r_1649_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = lean_unsigned_to_nat(2u);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v_impl_1535_);
lean_ctor_set(v___x_1391_, 3, v_r_1649_);
lean_ctor_set(v___x_1391_, 0, v___x_1666_);
v___x_1668_ = v___x_1391_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1386_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1387_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_r_1649_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v_impl_1535_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
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
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec_ref(v_cmp_1381_);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v_k_1382_);
lean_ctor_set(v___x_1672_, 2, v_v_1383_);
lean_ctor_set(v___x_1672_, 3, v_t_1384_);
lean_ctor_set(v___x_1672_, 4, v_t_1384_);
return v___x_1672_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(lean_object* v_cmp_1673_, lean_object* v_k_1674_, lean_object* v_t_1675_){
_start:
{
if (lean_obj_tag(v_t_1675_) == 0)
{
lean_object* v_k_1676_; lean_object* v_l_1677_; lean_object* v_r_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v_k_1676_ = lean_ctor_get(v_t_1675_, 1);
lean_inc(v_k_1676_);
v_l_1677_ = lean_ctor_get(v_t_1675_, 3);
lean_inc(v_l_1677_);
v_r_1678_ = lean_ctor_get(v_t_1675_, 4);
lean_inc(v_r_1678_);
lean_dec_ref_known(v_t_1675_, 5);
lean_inc_ref(v_cmp_1673_);
lean_inc(v_k_1674_);
v___x_1679_ = lean_apply_2(v_cmp_1673_, v_k_1674_, v_k_1676_);
v___x_1680_ = lean_unbox(v___x_1679_);
switch(v___x_1680_)
{
case 0:
{
lean_dec(v_r_1678_);
v_t_1675_ = v_l_1677_;
goto _start;
}
case 1:
{
uint8_t v___x_1682_; 
lean_dec(v_r_1678_);
lean_dec(v_l_1677_);
lean_dec(v_k_1674_);
lean_dec_ref(v_cmp_1673_);
v___x_1682_ = 1;
return v___x_1682_;
}
default: 
{
lean_dec(v_l_1677_);
v_t_1675_ = v_r_1678_;
goto _start;
}
}
}
else
{
uint8_t v___x_1684_; 
lean_dec(v_k_1674_);
lean_dec_ref(v_cmp_1673_);
v___x_1684_ = 0;
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg___boxed(lean_object* v_cmp_1685_, lean_object* v_k_1686_, lean_object* v_t_1687_){
_start:
{
uint8_t v_res_1688_; lean_object* v_r_1689_; 
v_res_1688_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1685_, v_k_1686_, v_t_1687_);
v_r_1689_ = lean_box(v_res_1688_);
return v_r_1689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(lean_object* v_cmp_1690_, lean_object* v_as_x27_1691_, lean_object* v_b_1692_){
_start:
{
if (lean_obj_tag(v_as_x27_1691_) == 0)
{
lean_dec_ref(v_cmp_1690_);
return v_b_1692_;
}
else
{
lean_object* v_head_1693_; lean_object* v_tail_1694_; uint8_t v___x_1695_; 
v_head_1693_ = lean_ctor_get(v_as_x27_1691_, 0);
v_tail_1694_ = lean_ctor_get(v_as_x27_1691_, 1);
lean_inc(v_b_1692_);
lean_inc(v_head_1693_);
lean_inc_ref(v_cmp_1690_);
v___x_1695_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1690_, v_head_1693_, v_b_1692_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_box(0);
lean_inc(v_head_1693_);
lean_inc_ref(v_cmp_1690_);
v___x_1697_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1690_, v_head_1693_, v___x_1696_, v_b_1692_);
v_as_x27_1691_ = v_tail_1694_;
v_b_1692_ = v___x_1697_;
goto _start;
}
else
{
v_as_x27_1691_ = v_tail_1694_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg___boxed(lean_object* v_cmp_1700_, lean_object* v_as_x27_1701_, lean_object* v_b_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1700_, v_as_x27_1701_, v_b_1702_);
lean_dec(v_as_x27_1701_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___redArg(lean_object* v_l_1704_, lean_object* v_cmp_1705_){
_start:
{
lean_object* v_r_1706_; lean_object* v___x_1707_; 
v_r_1706_ = lean_box(1);
v___x_1707_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1705_, v_l_1704_, v_r_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___redArg___boxed(lean_object* v_l_1708_, lean_object* v_cmp_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Std_ExtTreeSet_ofList___redArg(v_l_1708_, v_cmp_1709_);
lean_dec(v_l_1708_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList(lean_object* v_00_u03b1_1711_, lean_object* v_l_1712_, lean_object* v_cmp_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Std_ExtTreeSet_ofList___redArg(v_l_1712_, v_cmp_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofList___boxed(lean_object* v_00_u03b1_1715_, lean_object* v_l_1716_, lean_object* v_cmp_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Std_ExtTreeSet_ofList(v_00_u03b1_1715_, v_l_1716_, v_cmp_1717_);
lean_dec(v_l_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(lean_object* v_00_u03b1_1719_, lean_object* v_cmp_1720_, lean_object* v_00_u03b2_1721_, lean_object* v_k_1722_, lean_object* v_t_1723_){
_start:
{
uint8_t v___x_1724_; 
v___x_1724_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1720_, v_k_1722_, v_t_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___boxed(lean_object* v_00_u03b1_1725_, lean_object* v_cmp_1726_, lean_object* v_00_u03b2_1727_, lean_object* v_k_1728_, lean_object* v_t_1729_){
_start:
{
uint8_t v_res_1730_; lean_object* v_r_1731_; 
v_res_1730_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(v_00_u03b1_1725_, v_cmp_1726_, v_00_u03b2_1727_, v_k_1728_, v_t_1729_);
v_r_1731_ = lean_box(v_res_1730_);
return v_r_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1(lean_object* v_00_u03b1_1732_, lean_object* v_cmp_1733_, lean_object* v_00_u03b2_1734_, lean_object* v_k_1735_, lean_object* v_v_1736_, lean_object* v_t_1737_, lean_object* v_hl_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1733_, v_k_1735_, v_v_1736_, v_t_1737_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(lean_object* v_00_u03b1_1740_, lean_object* v_cmp_1741_, lean_object* v_as_1742_, lean_object* v_as_x27_1743_, lean_object* v_b_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(v_cmp_1741_, v_as_x27_1743_, v_b_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___boxed(lean_object* v_00_u03b1_1747_, lean_object* v_cmp_1748_, lean_object* v_as_1749_, lean_object* v_as_x27_1750_, lean_object* v_b_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(v_00_u03b1_1747_, v_cmp_1748_, v_as_1749_, v_as_x27_1750_, v_b_1751_, v_a_1752_);
lean_dec(v_as_x27_1750_);
lean_dec(v_as_1749_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg___lam__0(lean_object* v_l_1754_, lean_object* v_k_1755_, lean_object* v_x_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_array_push(v_l_1754_, v_k_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___redArg(lean_object* v_t_1759_){
_start:
{
lean_object* v___f_1760_; lean_object* v___y_1762_; 
v___f_1760_ = ((lean_object*)(l_Std_ExtTreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1759_) == 0)
{
lean_object* v_size_1765_; 
v_size_1765_ = lean_ctor_get(v_t_1759_, 0);
lean_inc(v_size_1765_);
v___y_1762_ = v_size_1765_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_unsigned_to_nat(0u);
v___y_1762_ = v___x_1766_;
goto v___jp_1761_;
}
v___jp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_mk_empty_array_with_capacity(v___y_1762_);
lean_dec(v___y_1762_);
v___x_1764_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1760_, v___x_1763_, v_t_1759_);
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray(lean_object* v_00_u03b1_1767_, lean_object* v_cmp_1768_, lean_object* v_inst_1769_, lean_object* v_t_1770_){
_start:
{
lean_object* v___f_1771_; lean_object* v___y_1773_; 
v___f_1771_ = ((lean_object*)(l_Std_ExtTreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1770_) == 0)
{
lean_object* v_size_1776_; 
v_size_1776_ = lean_ctor_get(v_t_1770_, 0);
lean_inc(v_size_1776_);
v___y_1773_ = v_size_1776_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_unsigned_to_nat(0u);
v___y_1773_ = v___x_1777_;
goto v___jp_1772_;
}
v___jp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_mk_empty_array_with_capacity(v___y_1773_);
lean_dec(v___y_1773_);
v___x_1775_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1771_, v___x_1774_, v_t_1770_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_toArray___boxed(lean_object* v_00_u03b1_1778_, lean_object* v_cmp_1779_, lean_object* v_inst_1780_, lean_object* v_t_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Std_ExtTreeSet_toArray(v_00_u03b1_1778_, v_cmp_1779_, v_inst_1780_, v_t_1781_);
lean_dec_ref(v_cmp_1779_);
return v_res_1782_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_obj_once(&l_Std_ExtTreeSet___auto__1___closed__26, &l_Std_ExtTreeSet___auto__1___closed__26_once, _init_l_Std_ExtTreeSet___auto__1___closed__26);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(lean_object* v_cmp_1784_, lean_object* v_as_1785_, size_t v_sz_1786_, size_t v_i_1787_, lean_object* v_b_1788_){
_start:
{
lean_object* v___y_1790_; uint8_t v___x_1794_; 
v___x_1794_ = lean_usize_dec_lt(v_i_1787_, v_sz_1786_);
if (v___x_1794_ == 0)
{
lean_dec_ref(v_cmp_1784_);
return v_b_1788_;
}
else
{
lean_object* v_a_1795_; uint8_t v___x_1796_; 
v_a_1795_ = lean_array_uget_borrowed(v_as_1785_, v_i_1787_);
lean_inc(v_b_1788_);
lean_inc(v_a_1795_);
lean_inc_ref(v_cmp_1784_);
v___x_1796_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_1784_, v_a_1795_, v_b_1788_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_box(0);
lean_inc(v_a_1795_);
lean_inc_ref(v_cmp_1784_);
v___x_1798_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_1784_, v_a_1795_, v___x_1797_, v_b_1788_);
v___y_1790_ = v___x_1798_;
goto v___jp_1789_;
}
else
{
v___y_1790_ = v_b_1788_;
goto v___jp_1789_;
}
}
v___jp_1789_:
{
size_t v___x_1791_; size_t v___x_1792_; 
v___x_1791_ = ((size_t)1ULL);
v___x_1792_ = lean_usize_add(v_i_1787_, v___x_1791_);
v_i_1787_ = v___x_1792_;
v_b_1788_ = v___y_1790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg___boxed(lean_object* v_cmp_1799_, lean_object* v_as_1800_, lean_object* v_sz_1801_, lean_object* v_i_1802_, lean_object* v_b_1803_){
_start:
{
size_t v_sz_boxed_1804_; size_t v_i_boxed_1805_; lean_object* v_res_1806_; 
v_sz_boxed_1804_ = lean_unbox_usize(v_sz_1801_);
lean_dec(v_sz_1801_);
v_i_boxed_1805_ = lean_unbox_usize(v_i_1802_);
lean_dec(v_i_1802_);
v_res_1806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1799_, v_as_1800_, v_sz_boxed_1804_, v_i_boxed_1805_, v_b_1803_);
lean_dec_ref(v_as_1800_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg(lean_object* v_a_1807_, lean_object* v_cmp_1808_){
_start:
{
lean_object* v_r_1809_; size_t v_sz_1810_; size_t v___x_1811_; lean_object* v___x_1812_; 
v_r_1809_ = lean_box(1);
v_sz_1810_ = lean_array_size(v_a_1807_);
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1808_, v_a_1807_, v_sz_1810_, v___x_1811_, v_r_1809_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___redArg___boxed(lean_object* v_a_1813_, lean_object* v_cmp_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_1813_, v_cmp_1814_);
lean_dec_ref(v_a_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray(lean_object* v_00_u03b1_1816_, lean_object* v_a_1817_, lean_object* v_cmp_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_1817_, v_cmp_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_ofArray___boxed(lean_object* v_00_u03b1_1820_, lean_object* v_a_1821_, lean_object* v_cmp_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Std_ExtTreeSet_ofArray(v_00_u03b1_1820_, v_a_1821_, v_cmp_1822_);
lean_dec_ref(v_a_1821_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(lean_object* v_00_u03b1_1824_, lean_object* v_cmp_1825_, lean_object* v_as_1826_, size_t v_sz_1827_, size_t v_i_1828_, lean_object* v_b_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_1825_, v_as_1826_, v_sz_1827_, v_i_1828_, v_b_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___boxed(lean_object* v_00_u03b1_1831_, lean_object* v_cmp_1832_, lean_object* v_as_1833_, lean_object* v_sz_1834_, lean_object* v_i_1835_, lean_object* v_b_1836_){
_start:
{
size_t v_sz_boxed_1837_; size_t v_i_boxed_1838_; lean_object* v_res_1839_; 
v_sz_boxed_1837_ = lean_unbox_usize(v_sz_1834_);
lean_dec(v_sz_1834_);
v_i_boxed_1838_ = lean_unbox_usize(v_i_1835_);
lean_dec(v_i_1835_);
v_res_1839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(v_00_u03b1_1831_, v_cmp_1832_, v_as_1833_, v_sz_boxed_1837_, v_i_boxed_1838_, v_b_1836_);
lean_dec_ref(v_as_1833_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0(lean_object* v_b_u2082_1842_, lean_object* v_x_1843_){
_start:
{
if (lean_obj_tag(v_x_1843_) == 0)
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v_b_u2082_1842_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; 
v___x_1845_ = ((lean_object*)(l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0));
return v___x_1845_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Std_ExtTreeSet_merge___redArg___lam__0(v_b_u2082_1846_, v_x_1847_);
lean_dec(v_x_1847_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg___lam__1(lean_object* v_cmp_1849_, lean_object* v_t_1850_, lean_object* v_a_1851_, lean_object* v_b_u2082_1852_){
_start:
{
lean_object* v___f_1853_; lean_object* v___x_1854_; 
v___f_1853_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1853_, 0, v_b_u2082_1852_);
v___x_1854_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_1849_, v_a_1851_, v___f_1853_, v_t_1850_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge___redArg(lean_object* v_cmp_1855_, lean_object* v_t_u2081_1856_, lean_object* v_t_u2082_1857_){
_start:
{
lean_object* v___f_1858_; lean_object* v___x_1859_; 
v___f_1858_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1858_, 0, v_cmp_1855_);
v___x_1859_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1858_, v_t_u2081_1856_, v_t_u2082_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_merge(lean_object* v_00_u03b1_1860_, lean_object* v_cmp_1861_, lean_object* v_inst_1862_, lean_object* v_t_u2081_1863_, lean_object* v_t_u2082_1864_){
_start:
{
lean_object* v___f_1865_; lean_object* v___x_1866_; 
v___f_1865_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1865_, 0, v_cmp_1861_);
v___x_1866_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1865_, v_t_u2081_1863_, v_t_u2082_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg___lam__0(lean_object* v_cmp_1867_, lean_object* v_a_1868_, lean_object* v_____s_1869_){
_start:
{
uint8_t v___x_1870_; 
lean_inc(v_____s_1869_);
lean_inc(v_a_1868_);
lean_inc_ref(v_cmp_1867_);
v___x_1870_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1867_, v_a_1868_, v_____s_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_box(0);
v___x_1872_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1867_, v_a_1868_, v___x_1871_, v_____s_1869_);
v___x_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
return v___x_1873_;
}
else
{
lean_object* v___x_1874_; 
lean_dec(v_a_1868_);
lean_dec_ref(v_cmp_1867_);
v___x_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1874_, 0, v_____s_1869_);
return v___x_1874_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany___redArg(lean_object* v_cmp_1875_, lean_object* v_inst_1876_, lean_object* v_t_1877_, lean_object* v_l_1878_){
_start:
{
lean_object* v___f_1879_; lean_object* v___x_1880_; 
v___f_1879_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1879_, 0, v_cmp_1875_);
v___x_1880_ = lean_apply_4(v_inst_1876_, lean_box(0), v_l_1878_, v_t_1877_, v___f_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_insertMany(lean_object* v_00_u03b1_1881_, lean_object* v_cmp_1882_, lean_object* v_inst_1883_, lean_object* v_00_u03c1_1884_, lean_object* v_inst_1885_, lean_object* v_t_1886_, lean_object* v_l_1887_){
_start:
{
lean_object* v___f_1888_; lean_object* v___x_1889_; 
v___f_1888_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1888_, 0, v_cmp_1882_);
v___x_1889_ = lean_apply_4(v_inst_1885_, lean_box(0), v_l_1887_, v_t_1886_, v___f_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union___redArg(lean_object* v_cmp_1890_, lean_object* v_t_u2081_1891_, lean_object* v_t_u2082_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1890_, v_t_u2081_1891_, v_t_u2082_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_union(lean_object* v_00_u03b1_1894_, lean_object* v_cmp_1895_, lean_object* v_inst_1896_, lean_object* v_t_u2081_1897_, lean_object* v_t_u2082_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1895_, v_t_u2081_1897_, v_t_u2082_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp___redArg(lean_object* v_cmp_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_union), 5, 3);
lean_closure_set(v___x_1901_, 0, lean_box(0));
lean_closure_set(v___x_1901_, 1, v_cmp_1900_);
lean_closure_set(v___x_1901_, 2, lean_box(0));
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instUnionOfTransCmp(lean_object* v_00_u03b1_1902_, lean_object* v_cmp_1903_, lean_object* v_inst_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_union), 5, 3);
lean_closure_set(v___x_1905_, 0, lean_box(0));
lean_closure_set(v___x_1905_, 1, v_cmp_1903_);
lean_closure_set(v___x_1905_, 2, lean_box(0));
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter___redArg(lean_object* v_cmp_1906_, lean_object* v_t_u2081_1907_, lean_object* v_t_u2082_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1906_, v_t_u2081_1907_, v_t_u2082_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_inter(lean_object* v_00_u03b1_1910_, lean_object* v_cmp_1911_, lean_object* v_inst_1912_, lean_object* v_t_u2081_1913_, lean_object* v_t_u2082_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1911_, v_t_u2081_1913_, v_t_u2082_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp___redArg(lean_object* v_cmp_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_inter), 5, 3);
lean_closure_set(v___x_1917_, 0, lean_box(0));
lean_closure_set(v___x_1917_, 1, v_cmp_1916_);
lean_closure_set(v___x_1917_, 2, lean_box(0));
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instInterOfTransCmp(lean_object* v_00_u03b1_1918_, lean_object* v_cmp_1919_, lean_object* v_inst_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_inter), 5, 3);
lean_closure_set(v___x_1921_, 0, lean_box(0));
lean_closure_set(v___x_1921_, 1, v_cmp_1919_);
lean_closure_set(v___x_1921_, 2, lean_box(0));
return v___x_1921_;
}
}
static lean_object* _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___f_1923_; 
v___x_1922_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1923_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1923_, 0, v___x_1922_);
return v___f_1923_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(lean_object* v_cmp_1924_, lean_object* v_m_u2081_1925_, lean_object* v_m_u2082_1926_){
_start:
{
lean_object* v___f_1927_; uint8_t v___x_1928_; 
v___f_1927_ = lean_obj_once(&l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0, &l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once, _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0);
v___x_1928_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_1924_, v___f_1927_, v_m_u2081_1925_, v_m_u2082_1926_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_1929_, lean_object* v_m_u2081_1930_, lean_object* v_m_u2082_1931_){
_start:
{
uint8_t v_res_1932_; lean_object* v_r_1933_; 
v_res_1932_ = l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(v_cmp_1929_, v_m_u2081_1930_, v_m_u2082_1931_);
v_r_1933_ = lean_box(v_res_1932_);
return v_r_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp___redArg(lean_object* v_cmp_1934_){
_start:
{
lean_object* v___f_1935_; 
v___f_1935_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1935_, 0, v_cmp_1934_);
return v___f_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instBEqOfTransCmp(lean_object* v_00_u03b1_1936_, lean_object* v_cmp_1937_, lean_object* v_inst_1938_){
_start:
{
lean_object* v___f_1939_; 
v___f_1939_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1939_, 0, v_cmp_1937_);
return v___f_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff___redArg(lean_object* v_cmp_1940_, lean_object* v_t_u2081_1941_, lean_object* v_t_u2082_1942_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1940_, v_t_u2081_1941_, v_t_u2082_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_diff(lean_object* v_00_u03b1_1944_, lean_object* v_cmp_1945_, lean_object* v_inst_1946_, lean_object* v_t_u2081_1947_, lean_object* v_t_u2082_1948_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1945_, v_t_u2081_1947_, v_t_u2082_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp___redArg(lean_object* v_cmp_1950_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_diff), 5, 3);
lean_closure_set(v___x_1951_, 0, lean_box(0));
lean_closure_set(v___x_1951_, 1, v_cmp_1950_);
lean_closure_set(v___x_1951_, 2, lean_box(0));
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instSDiffOfTransCmp(lean_object* v_00_u03b1_1952_, lean_object* v_cmp_1953_, lean_object* v_inst_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_diff), 5, 3);
lean_closure_set(v___x_1955_, 0, lean_box(0));
lean_closure_set(v___x_1955_, 1, v_cmp_1953_);
lean_closure_set(v___x_1955_, 2, lean_box(0));
return v___x_1955_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(lean_object* v_cmp_1956_, lean_object* v_x_1957_, lean_object* v_x_1958_){
_start:
{
lean_object* v___f_1959_; uint8_t v___x_1960_; 
v___f_1959_ = lean_obj_once(&l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0, &l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once, _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0);
v___x_1960_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_1956_, v___f_1959_, v_x_1957_, v_x_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg___boxed(lean_object* v_cmp_1961_, lean_object* v_x_1962_, lean_object* v_x_1963_){
_start:
{
uint8_t v_res_1964_; lean_object* v_r_1965_; 
v_res_1964_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_1961_, v_x_1962_, v_x_1963_);
v_r_1965_ = lean_box(v_res_1964_);
return v_r_1965_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(lean_object* v_00_u03b1_1966_, lean_object* v_cmp_1967_, lean_object* v_inst_1968_, lean_object* v_inst_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_){
_start:
{
uint8_t v___x_1972_; 
v___x_1972_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_1967_, v_x_1970_, v_x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___boxed(lean_object* v_00_u03b1_1973_, lean_object* v_cmp_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_){
_start:
{
uint8_t v_res_1979_; lean_object* v_r_1980_; 
v_res_1979_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(v_00_u03b1_1973_, v_cmp_1974_, v_inst_1975_, v_inst_1976_, v_x_1977_, v_x_1978_);
v_r_1980_ = lean_box(v_res_1979_);
return v_r_1980_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg___lam__0(lean_object* v_cmp_1981_, lean_object* v_a_1982_, lean_object* v_____s_1983_){
_start:
{
lean_object* v_acc_1984_; lean_object* v___x_1985_; 
v_acc_1984_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_1981_, v_a_1982_, v_____s_1983_);
v___x_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1985_, 0, v_acc_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany___redArg(lean_object* v_cmp_1986_, lean_object* v_inst_1987_, lean_object* v_t_1988_, lean_object* v_l_1989_){
_start:
{
lean_object* v___f_1990_; lean_object* v___x_1991_; 
v___f_1990_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1990_, 0, v_cmp_1986_);
v___x_1991_ = lean_apply_4(v_inst_1987_, lean_box(0), v_l_1989_, v_t_1988_, v___f_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_eraseMany(lean_object* v_00_u03b1_1992_, lean_object* v_cmp_1993_, lean_object* v_inst_1994_, lean_object* v_00_u03c1_1995_, lean_object* v_inst_1996_, lean_object* v_t_1997_, lean_object* v_l_1998_){
_start:
{
lean_object* v___f_1999_; lean_object* v___x_2000_; 
v___f_1999_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1999_, 0, v_cmp_1993_);
v___x_2000_ = lean_apply_4(v_inst_1996_, lean_box(0), v_l_1998_, v_t_1997_, v___f_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_2004_, lean_object* v_inst_2005_, lean_object* v_m_2006_, lean_object* v_prec_2007_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2008_ = ((lean_object*)(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_2009_ = lean_box(0);
v___x_2010_ = ((lean_object*)(l_Std_ExtTreeSet_foldr___redArg___closed__9));
v___x_2011_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2010_, v___f_2004_, v___x_2009_, v_m_2006_);
v___x_2012_ = l_List_repr___redArg(v_inst_2005_, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2008_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = l_Repr_addAppParen(v___x_2013_, v_prec_2007_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_2015_, lean_object* v_inst_2016_, lean_object* v_m_2017_, lean_object* v_prec_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(v___f_2015_, v_inst_2016_, v_m_2017_, v_prec_2018_);
lean_dec(v_prec_2018_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___redArg(lean_object* v_inst_2020_){
_start:
{
lean_object* v___f_2021_; lean_object* v___f_2022_; 
v___f_2021_ = ((lean_object*)(l_Std_ExtTreeSet_toList___redArg___closed__0));
v___f_2022_ = lean_alloc_closure((void*)(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2022_, 0, v___f_2021_);
lean_closure_set(v___f_2022_, 1, v_inst_2020_);
return v___f_2022_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp(lean_object* v_00_u03b1_2023_, lean_object* v_cmp_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg(v_inst_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeSet_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_2028_, lean_object* v_cmp_2029_, lean_object* v_inst_2030_, lean_object* v_inst_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Std_ExtTreeSet_instReprOfTransCmp(v_00_u03b1_2028_, v_cmp_2029_, v_inst_2030_, v_inst_2031_);
lean_dec_ref(v_cmp_2029_);
return v_res_2032_;
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
