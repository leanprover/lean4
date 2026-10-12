// Lean compiler output
// Module: Std.Data.TreeSet.Basic
// Imports: public import Std.Data.TreeMap.Basic
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
lean_object* l_Std_DTreeMap_Internal_Impl_filter___redArg(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeSet___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_TreeSet___auto__1___closed__0 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__0_value;
static const lean_string_object l_Std_TreeSet___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_TreeSet___auto__1___closed__1 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__1_value;
static const lean_string_object l_Std_TreeSet___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_TreeSet___auto__1___closed__2 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__2_value;
static const lean_string_object l_Std_TreeSet___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_TreeSet___auto__1___closed__3 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__3_value;
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_TreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_TreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_TreeSet___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_TreeSet___auto__1___closed__4 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__4_value;
static const lean_array_object l_Std_TreeSet___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_TreeSet___auto__1___closed__5 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__5_value;
static const lean_string_object l_Std_TreeSet___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_TreeSet___auto__1___closed__6 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__6_value;
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_TreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_TreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_TreeSet___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_TreeSet___auto__1___closed__7 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__7_value;
static const lean_string_object l_Std_TreeSet___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_TreeSet___auto__1___closed__8 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__8_value;
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_TreeSet___auto__1___closed__9 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__9_value;
static const lean_string_object l_Std_TreeSet___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_TreeSet___auto__1___closed__10 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__10_value;
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_TreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_TreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_TreeSet___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_TreeSet___auto__1___closed__11 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__11_value;
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__12;
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__13;
static const lean_string_object l_Std_TreeSet___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_TreeSet___auto__1___closed__14 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__14_value;
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeSet___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_TreeSet___auto__1___closed__15 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__15_value;
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_TreeSet___auto__1___closed__16 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__16_value;
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_TreeSet___auto__1___closed__15_value),((lean_object*)&l_Std_TreeSet___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeSet___auto__1___closed__17 = (const lean_object*)&l_Std_TreeSet___auto__1___closed__17_value;
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__18;
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__19;
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__20;
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__21;
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__22;
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__23;
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__24;
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__25;
LEAN_EXPORT lean_object* l_Std_TreeSet___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_TreeSet_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__0 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_TreeSet_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TreeSet"};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__1 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_TreeSet_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__2 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__2_value;
static const lean_ctor_object l_Std_TreeSet_term___x7em___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_TreeSet_term___x7em___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__3_value_aux_0),((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 231, 51, 117, 79, 92, 223, 2)}};
static const lean_ctor_object l_Std_TreeSet_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__3_value_aux_1),((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 2, 11, 18, 255, 172, 132, 253)}};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__3 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__3_value;
static const lean_string_object l_Std_TreeSet_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__4 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__4_value;
static const lean_ctor_object l_Std_TreeSet_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__5 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__5_value;
static const lean_string_object l_Std_TreeSet_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__6 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__6_value;
static const lean_ctor_object l_Std_TreeSet_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__6_value)}};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__7 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__7_value;
static const lean_string_object l_Std_TreeSet_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__8 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__8_value;
static const lean_ctor_object l_Std_TreeSet_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__9 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_TreeSet_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__9_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__10 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_TreeSet_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__5_value),((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__7_value),((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__10_value)}};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__11 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_TreeSet_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_TreeSet_term___x7em___00__closed__12 = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__12_value;
LEAN_EXPORT const lean_object* l_Std_TreeSet_term___x7em__ = (const lean_object*)&l_Std_TreeSet_term___x7em___00__closed__12_value;
static const lean_string_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1_value;
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_0),((lean_object*)&l_Std_TreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_1),((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_2),((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value;
static lean_once_cell_t l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4;
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5_value;
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_0),((lean_object*)&l_Std_TreeSet_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 231, 51, 117, 79, 92, 223, 2)}};
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_1),((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(209, 137, 51, 121, 82, 223, 84, 209)}};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value;
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value)}};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7_value),((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9_value)}};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10_value;
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1 = (const lean_object*)&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_contains(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_erase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_minD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeSet_getGE_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_TreeSet_getGE_x21___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_getGE_x21___redArg___closed__0_value;
static const lean_string_object l_Std_TreeSet_getGE_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_TreeSet_getGE_x21___redArg___closed__1 = (const lean_object*)&l_Std_TreeSet_getGE_x21___redArg___closed__1_value;
static const lean_string_object l_Std_TreeSet_getGE_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_TreeSet_getGE_x21___redArg___closed__2 = (const lean_object*)&l_Std_TreeSet_getGE_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_TreeSet_getGE_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_getGE_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_foldr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_foldr___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_foldr___redArg___closed__0_value;
static const lean_closure_object l_Std_TreeSet_foldr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_foldr___redArg___closed__1 = (const lean_object*)&l_Std_TreeSet_foldr___redArg___closed__1_value;
static const lean_closure_object l_Std_TreeSet_foldr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_foldr___redArg___closed__2 = (const lean_object*)&l_Std_TreeSet_foldr___redArg___closed__2_value;
static const lean_closure_object l_Std_TreeSet_foldr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_foldr___redArg___closed__3 = (const lean_object*)&l_Std_TreeSet_foldr___redArg___closed__3_value;
static const lean_closure_object l_Std_TreeSet_foldr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_foldr___redArg___closed__4 = (const lean_object*)&l_Std_TreeSet_foldr___redArg___closed__4_value;
static const lean_closure_object l_Std_TreeSet_foldr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_foldr___redArg___closed__5 = (const lean_object*)&l_Std_TreeSet_foldr___redArg___closed__5_value;
static const lean_closure_object l_Std_TreeSet_foldr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_foldr___redArg___closed__6 = (const lean_object*)&l_Std_TreeSet_foldr___redArg___closed__6_value;
static const lean_ctor_object l_Std_TreeSet_foldr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeSet_foldr___redArg___closed__0_value),((lean_object*)&l_Std_TreeSet_foldr___redArg___closed__1_value)}};
static const lean_object* l_Std_TreeSet_foldr___redArg___closed__7 = (const lean_object*)&l_Std_TreeSet_foldr___redArg___closed__7_value;
static const lean_ctor_object l_Std_TreeSet_foldr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeSet_foldr___redArg___closed__7_value),((lean_object*)&l_Std_TreeSet_foldr___redArg___closed__2_value),((lean_object*)&l_Std_TreeSet_foldr___redArg___closed__3_value),((lean_object*)&l_Std_TreeSet_foldr___redArg___closed__4_value),((lean_object*)&l_Std_TreeSet_foldr___redArg___closed__5_value)}};
static const lean_object* l_Std_TreeSet_foldr___redArg___closed__8 = (const lean_object*)&l_Std_TreeSet_foldr___redArg___closed__8_value;
static const lean_ctor_object l_Std_TreeSet_foldr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeSet_foldr___redArg___closed__8_value),((lean_object*)&l_Std_TreeSet_foldr___redArg___closed__6_value)}};
static const lean_object* l_Std_TreeSet_foldr___redArg___closed__9 = (const lean_object*)&l_Std_TreeSet_foldr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_TreeSet_partition___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_partition___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_partition___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_partition(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_TreeSet_any___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_any___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_any___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_TreeSet_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_toList___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_toArray___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_TreeSet_merge___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_merge___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_TreeSet_merge___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_merge(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_union(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_inter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_inter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_diff(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeSet_instRepr___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.TreeSet.ofList "};
static const lean_object* l_Std_TreeSet_instRepr___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_TreeSet_instRepr___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_TreeSet_instRepr___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_TreeSet_instRepr___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_TreeSet_instRepr___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_TreeSet_instRepr___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_TreeSet___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__12, &l_Std_TreeSet___auto__1___closed__12_once, _init_l_Std_TreeSet___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__17));
v___x_45_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__13, &l_Std_TreeSet___auto__1___closed__13_once, _init_l_Std_TreeSet___auto__1___closed__13);
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__18, &l_Std_TreeSet___auto__1___closed__18_once, _init_l_Std_TreeSet___auto__1___closed__18);
v___x_48_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__11));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__19, &l_Std_TreeSet___auto__1___closed__19_once, _init_l_Std_TreeSet___auto__1___closed__19);
v___x_52_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__20, &l_Std_TreeSet___auto__1___closed__20_once, _init_l_Std_TreeSet___auto__1___closed__20);
v___x_55_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__9));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__22(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__21, &l_Std_TreeSet___auto__1___closed__21_once, _init_l_Std_TreeSet___auto__1___closed__21);
v___x_59_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__23(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__22, &l_Std_TreeSet___auto__1___closed__22_once, _init_l_Std_TreeSet___auto__1___closed__22);
v___x_62_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__7));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__24(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__23, &l_Std_TreeSet___auto__1___closed__23_once, _init_l_Std_TreeSet___auto__1___closed__23);
v___x_66_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__25(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__24, &l_Std_TreeSet___auto__1___closed__24_once, _init_l_Std_TreeSet___auto__1___closed__24);
v___x_69_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__4));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__25, &l_Std_TreeSet___auto__1___closed__25_once, _init_l_Std_TreeSet___auto__1___closed__25);
return v___x_72_;
}
}
lean_object* l_Std_TreeSet_empty___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(1);
return v___x_74_;
}
}
LEAN_EXPORT void l_Std_TreeSet_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_75_;
v_res_75_ = l_Std_TreeSet_empty___redArg();
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___redArg___boxed(lean_object* v___dummy_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_TreeSet_empty___redArg();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_empty(lean_object* v_00_u03b1_78_, lean_object* v_cmp_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(1);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___boxed(lean_object* v_00_u03b1_81_, lean_object* v_cmp_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_TreeSet_empty(v_00_u03b1_81_, v_cmp_82_);
lean_dec_ref(v_cmp_82_);
return v_res_83_;
}
}
lean_object* l_Std_TreeSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_box(1);
return v___x_85_;
}
}
LEAN_EXPORT void l_Std_TreeSet_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_86_;
v_res_86_ = l_Std_TreeSet_instEmptyCollection___redArg();
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_TreeSet_instEmptyCollection___redArg();
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection(lean_object* v_00_u03b1_89_, lean_object* v_cmp_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(1);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_92_, lean_object* v_cmp_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_TreeSet_instEmptyCollection(v_00_u03b1_92_, v_cmp_93_);
lean_dec_ref(v_cmp_93_);
return v_res_94_;
}
}
lean_object* l_Std_TreeSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
LEAN_EXPORT void l_Std_TreeSet_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_97_;
v_res_97_ = l_Std_TreeSet_instInhabited___redArg();
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___redArg___boxed(lean_object* v___dummy_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_TreeSet_instInhabited___redArg();
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited(lean_object* v_00_u03b1_100_, lean_object* v_cmp_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(1);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___boxed(lean_object* v_00_u03b1_103_, lean_object* v_cmp_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_TreeSet_instInhabited(v_00_u03b1_103_, v_cmp_104_);
lean_dec_ref(v_cmp_104_);
return v_res_105_;
}
}
static lean_object* _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3));
v___x_144_ = l_String_toRawSubstring_x27(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(lean_object* v_x_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__3));
lean_inc(v_x_162_);
v___x_166_ = l_Lean_Syntax_isOfKind(v_x_162_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v_x_162_);
v___x_167_ = lean_box(1);
v___x_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v_a_164_);
return v___x_168_;
}
else
{
lean_object* v_quotContext_169_; lean_object* v_currMacroScope_170_; lean_object* v_ref_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_quotContext_169_ = lean_ctor_get(v_a_163_, 1);
v_currMacroScope_170_ = lean_ctor_get(v_a_163_, 2);
v_ref_171_ = lean_ctor_get(v_a_163_, 5);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = l_Lean_Syntax_getArg(v_x_162_, v___x_172_);
v___x_174_ = lean_unsigned_to_nat(2u);
v___x_175_ = l_Lean_Syntax_getArg(v_x_162_, v___x_174_);
lean_dec(v_x_162_);
v___x_176_ = 0;
v___x_177_ = l_Lean_SourceInfo_fromRef(v_ref_171_, v___x_176_);
v___x_178_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2));
v___x_179_ = lean_obj_once(&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4, &l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4_once, _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4);
v___x_180_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_170_);
lean_inc(v_quotContext_169_);
v___x_181_ = l_Lean_addMacroScope(v_quotContext_169_, v___x_180_, v_currMacroScope_170_);
v___x_182_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10));
lean_inc_n(v___x_177_, 2);
v___x_183_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_183_, 0, v___x_177_);
lean_ctor_set(v___x_183_, 1, v___x_179_);
lean_ctor_set(v___x_183_, 2, v___x_181_);
lean_ctor_set(v___x_183_, 3, v___x_182_);
v___x_184_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__9));
v___x_185_ = l_Lean_Syntax_node2(v___x_177_, v___x_184_, v___x_173_, v___x_175_);
v___x_186_ = l_Lean_Syntax_node2(v___x_177_, v___x_178_, v___x_183_, v___x_185_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_a_164_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___boxed(lean_object* v_x_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(v_x_188_, v_a_189_, v_a_190_);
lean_dec_ref(v_a_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(lean_object* v_x_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2));
lean_inc(v_x_195_);
v___x_199_ = l_Lean_Syntax_isOfKind(v_x_195_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v_x_195_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_a_197_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = l_Lean_Syntax_getArg(v_x_195_, v___x_202_);
v___x_204_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1));
lean_inc(v___x_203_);
v___x_205_ = l_Lean_Syntax_isOfKind(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v___x_203_);
lean_dec(v_x_195_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v_a_197_);
return v___x_207_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = l_Lean_Syntax_getArg(v_x_195_, v___x_208_);
lean_dec(v_x_195_);
v___x_210_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_209_);
v___x_211_ = l_Lean_Syntax_matchesNull(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v___x_209_);
lean_dec(v___x_203_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_a_197_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_ref_216_; uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_214_ = l_Lean_Syntax_getArg(v___x_209_, v___x_202_);
v___x_215_ = l_Lean_Syntax_getArg(v___x_209_, v___x_208_);
lean_dec(v___x_209_);
v_ref_216_ = l_Lean_replaceRef(v___x_203_, v_a_196_);
lean_dec(v___x_203_);
v___x_217_ = 0;
v___x_218_ = l_Lean_SourceInfo_fromRef(v_ref_216_, v___x_217_);
lean_dec(v_ref_216_);
v___x_219_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__3));
v___x_220_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__6));
lean_inc(v___x_218_);
v___x_221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_218_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = l_Lean_Syntax_node3(v___x_218_, v___x_219_, v___x_214_, v___x_221_, v___x_215_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v_a_197_);
return v___x_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___boxed(lean_object* v_x_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(v_x_224_, v_a_225_, v_a_226_);
lean_dec(v_a_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insert___redArg(lean_object* v_cmp_228_, lean_object* v_l_229_, lean_object* v_a_230_){
_start:
{
uint8_t v___x_231_; 
lean_inc(v_l_229_);
lean_inc(v_a_230_);
lean_inc_ref(v_cmp_228_);
v___x_231_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_228_, v_a_230_, v_l_229_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_box(0);
v___x_233_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_228_, v_a_230_, v___x_232_, v_l_229_);
return v___x_233_;
}
else
{
lean_dec(v_a_230_);
lean_dec_ref(v_cmp_228_);
return v_l_229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insert(lean_object* v_00_u03b1_234_, lean_object* v_cmp_235_, lean_object* v_l_236_, lean_object* v_a_237_){
_start:
{
uint8_t v___x_238_; 
lean_inc(v_l_236_);
lean_inc(v_a_237_);
lean_inc_ref(v_cmp_235_);
v___x_238_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_235_, v_a_237_, v_l_236_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_box(0);
v___x_240_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_235_, v_a_237_, v___x_239_, v_l_236_);
return v___x_240_;
}
else
{
lean_dec(v_a_237_);
lean_dec_ref(v_cmp_235_);
return v_l_236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg___lam__0(lean_object* v_cmp_241_, lean_object* v_e_242_){
_start:
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_box(1);
lean_inc(v_e_242_);
lean_inc_ref(v_cmp_241_);
v___x_244_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_241_, v_e_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_box(0);
v___x_246_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_241_, v_e_242_, v___x_245_, v___x_243_);
return v___x_246_;
}
else
{
lean_dec(v_e_242_);
lean_dec_ref(v_cmp_241_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg(lean_object* v_cmp_247_){
_start:
{
lean_object* v___f_248_; 
v___f_248_ = lean_alloc_closure((void*)(l_Std_TreeSet_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_248_, 0, v_cmp_247_);
return v___f_248_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton(lean_object* v_00_u03b1_249_, lean_object* v_cmp_250_){
_start:
{
lean_object* v___f_251_; 
v___f_251_ = lean_alloc_closure((void*)(l_Std_TreeSet_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_251_, 0, v_cmp_250_);
return v___f_251_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg___lam__0(lean_object* v_cmp_252_, lean_object* v_e_253_, lean_object* v_s_254_){
_start:
{
uint8_t v___x_255_; 
lean_inc(v_s_254_);
lean_inc(v_e_253_);
lean_inc_ref(v_cmp_252_);
v___x_255_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_252_, v_e_253_, v_s_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_box(0);
v___x_257_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_252_, v_e_253_, v___x_256_, v_s_254_);
return v___x_257_;
}
else
{
lean_dec(v_e_253_);
lean_dec_ref(v_cmp_252_);
return v_s_254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg(lean_object* v_cmp_258_){
_start:
{
lean_object* v___f_259_; 
v___f_259_ = lean_alloc_closure((void*)(l_Std_TreeSet_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_259_, 0, v_cmp_258_);
return v___f_259_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert(lean_object* v_00_u03b1_260_, lean_object* v_cmp_261_){
_start:
{
lean_object* v___f_262_; 
v___f_262_ = lean_alloc_closure((void*)(l_Std_TreeSet_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_262_, 0, v_cmp_261_);
return v___f_262_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert___redArg(lean_object* v_cmp_263_, lean_object* v_t_264_, lean_object* v_a_265_){
_start:
{
uint8_t v___x_266_; 
lean_inc(v_t_264_);
lean_inc(v_a_265_);
lean_inc_ref(v_cmp_263_);
v___x_266_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_263_, v_a_265_, v_t_264_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_267_ = lean_box(0);
v___x_268_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_263_, v_a_265_, v___x_267_, v_t_264_);
v___x_269_ = lean_box(v___x_266_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_268_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v_a_265_);
lean_dec_ref(v_cmp_263_);
v___x_271_ = lean_box(v___x_266_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_t_264_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert(lean_object* v_00_u03b1_273_, lean_object* v_cmp_274_, lean_object* v_t_275_, lean_object* v_a_276_){
_start:
{
uint8_t v___x_277_; 
lean_inc(v_t_275_);
lean_inc(v_a_276_);
lean_inc_ref(v_cmp_274_);
v___x_277_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_274_, v_a_276_, v_t_275_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_278_ = lean_box(0);
v___x_279_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_274_, v_a_276_, v___x_278_, v_t_275_);
v___x_280_ = lean_box(v___x_277_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v_a_276_);
lean_dec_ref(v_cmp_274_);
v___x_282_ = lean_box(v___x_277_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_t_275_);
return v___x_283_;
}
}
}
uint8_t l_Std_TreeSet_contains___redArg(lean_object* v_cmp_284_, lean_object* v_l_285_, lean_object* v_a_286_){
_start:
{
uint8_t v___x_287_; 
v___x_287_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_284_, v_a_286_, v_l_285_);
return v___x_287_;
}
}
LEAN_EXPORT void l_Std_TreeSet_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_284_ = stack[0].m_obj;
lean_object* v_l_285_ = stack[1].m_obj;
lean_object* v_a_286_ = stack[2].m_obj;
uint8_t v_res_288_;
v_res_288_ = l_Std_TreeSet_contains___redArg(v_cmp_284_, v_l_285_, v_a_286_);
stack->m_num = v_res_288_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___redArg___boxed(lean_object* v_cmp_289_, lean_object* v_l_290_, lean_object* v_a_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Std_TreeSet_contains___redArg(v_cmp_289_, v_l_290_, v_a_291_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
uint8_t l_Std_TreeSet_contains(lean_object* v_00_u03b1_294_, lean_object* v_cmp_295_, lean_object* v_l_296_, lean_object* v_a_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_295_, v_a_297_, v_l_296_);
return v___x_298_;
}
}
LEAN_EXPORT void l_Std_TreeSet_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_295_ = stack[1].m_obj;
lean_object* v_l_296_ = stack[2].m_obj;
lean_object* v_a_297_ = stack[3].m_obj;
uint8_t v_res_299_;
v_res_299_ = l_Std_TreeSet_contains(lean_box(0), v_cmp_295_, v_l_296_, v_a_297_);
stack->m_num = v_res_299_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___boxed(lean_object* v_00_u03b1_300_, lean_object* v_cmp_301_, lean_object* v_l_302_, lean_object* v_a_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Std_TreeSet_contains(v_00_u03b1_300_, v_cmp_301_, v_l_302_, v_a_303_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
lean_object* l_Std_TreeSet_instMembership___redArg(){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_box(0);
return v___x_307_;
}
}
LEAN_EXPORT void l_Std_TreeSet_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_308_;
v_res_308_ = l_Std_TreeSet_instMembership___redArg();
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___redArg___boxed(lean_object* v___dummy_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_TreeSet_instMembership___redArg();
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership(lean_object* v_00_u03b1_311_, lean_object* v_cmp_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_box(0);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___boxed(lean_object* v_00_u03b1_314_, lean_object* v_cmp_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_TreeSet_instMembership(v_00_u03b1_314_, v_cmp_315_);
lean_dec_ref(v_cmp_315_);
return v_res_316_;
}
}
uint8_t l_Std_TreeSet_instDecidableMem___redArg(lean_object* v_cmp_317_, lean_object* v_m_318_, lean_object* v_a_319_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_317_, v_a_319_, v_m_318_);
return v___x_320_;
}
}
LEAN_EXPORT void l_Std_TreeSet_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_317_ = stack[0].m_obj;
lean_object* v_m_318_ = stack[1].m_obj;
lean_object* v_a_319_ = stack[2].m_obj;
uint8_t v_res_321_;
v_res_321_ = l_Std_TreeSet_instDecidableMem___redArg(v_cmp_317_, v_m_318_, v_a_319_);
stack->m_num = v_res_321_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___redArg___boxed(lean_object* v_cmp_322_, lean_object* v_m_323_, lean_object* v_a_324_){
_start:
{
uint8_t v_res_325_; lean_object* v_r_326_; 
v_res_325_ = l_Std_TreeSet_instDecidableMem___redArg(v_cmp_322_, v_m_323_, v_a_324_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
uint8_t l_Std_TreeSet_instDecidableMem(lean_object* v_00_u03b1_327_, lean_object* v_cmp_328_, lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_328_, v_a_330_, v_m_329_);
return v___x_331_;
}
}
LEAN_EXPORT void l_Std_TreeSet_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_328_ = stack[1].m_obj;
lean_object* v_m_329_ = stack[2].m_obj;
lean_object* v_a_330_ = stack[3].m_obj;
uint8_t v_res_332_;
v_res_332_ = l_Std_TreeSet_instDecidableMem(lean_box(0), v_cmp_328_, v_m_329_, v_a_330_);
stack->m_num = v_res_332_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___boxed(lean_object* v_00_u03b1_333_, lean_object* v_cmp_334_, lean_object* v_m_335_, lean_object* v_a_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Std_TreeSet_instDecidableMem(v_00_u03b1_333_, v_cmp_334_, v_m_335_, v_a_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg(lean_object* v_t_339_){
_start:
{
if (lean_obj_tag(v_t_339_) == 0)
{
lean_object* v_size_340_; 
v_size_340_ = lean_ctor_get(v_t_339_, 0);
lean_inc(v_size_340_);
return v_size_340_;
}
else
{
lean_object* v___x_341_; 
v___x_341_ = lean_unsigned_to_nat(0u);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg___boxed(lean_object* v_t_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_TreeSet_size___redArg(v_t_342_);
lean_dec(v_t_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size(lean_object* v_00_u03b1_344_, lean_object* v_cmp_345_, lean_object* v_t_346_){
_start:
{
if (lean_obj_tag(v_t_346_) == 0)
{
lean_object* v_size_347_; 
v_size_347_ = lean_ctor_get(v_t_346_, 0);
lean_inc(v_size_347_);
return v_size_347_;
}
else
{
lean_object* v___x_348_; 
v___x_348_ = lean_unsigned_to_nat(0u);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___boxed(lean_object* v_00_u03b1_349_, lean_object* v_cmp_350_, lean_object* v_t_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_TreeSet_size(v_00_u03b1_349_, v_cmp_350_, v_t_351_);
lean_dec(v_t_351_);
lean_dec_ref(v_cmp_350_);
return v_res_352_;
}
}
uint8_t l_Std_TreeSet_isEmpty___redArg(lean_object* v_t_353_){
_start:
{
if (lean_obj_tag(v_t_353_) == 0)
{
uint8_t v___x_354_; 
v___x_354_ = 0;
return v___x_354_;
}
else
{
uint8_t v___x_355_; 
v___x_355_ = 1;
return v___x_355_;
}
}
}
LEAN_EXPORT void l_Std_TreeSet_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_353_ = stack[0].m_obj;
uint8_t v_res_356_;
v_res_356_ = l_Std_TreeSet_isEmpty___redArg(v_t_353_);
stack->m_num = v_res_356_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___redArg___boxed(lean_object* v_t_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Std_TreeSet_isEmpty___redArg(v_t_357_);
lean_dec(v_t_357_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
uint8_t l_Std_TreeSet_isEmpty(lean_object* v_00_u03b1_360_, lean_object* v_cmp_361_, lean_object* v_t_362_){
_start:
{
if (lean_obj_tag(v_t_362_) == 0)
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = 1;
return v___x_364_;
}
}
}
LEAN_EXPORT void l_Std_TreeSet_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_361_ = stack[1].m_obj;
lean_object* v_t_362_ = stack[2].m_obj;
uint8_t v_res_365_;
v_res_365_ = l_Std_TreeSet_isEmpty(lean_box(0), v_cmp_361_, v_t_362_);
stack->m_num = v_res_365_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___boxed(lean_object* v_00_u03b1_366_, lean_object* v_cmp_367_, lean_object* v_t_368_){
_start:
{
uint8_t v_res_369_; lean_object* v_r_370_; 
v_res_369_ = l_Std_TreeSet_isEmpty(v_00_u03b1_366_, v_cmp_367_, v_t_368_);
lean_dec(v_t_368_);
lean_dec_ref(v_cmp_367_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_erase___redArg(lean_object* v_cmp_371_, lean_object* v_t_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_371_, v_a_373_, v_t_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_erase(lean_object* v_00_u03b1_375_, lean_object* v_cmp_376_, lean_object* v_t_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_376_, v_a_378_, v_t_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f___redArg(lean_object* v_cmp_380_, lean_object* v_t_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_380_, v_t_381_, v_a_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f(lean_object* v_00_u03b1_384_, lean_object* v_cmp_385_, lean_object* v_t_386_, lean_object* v_a_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_385_, v_t_386_, v_a_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get___redArg(lean_object* v_cmp_389_, lean_object* v_t_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_389_, v_t_390_, v_a_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get(lean_object* v_00_u03b1_393_, lean_object* v_cmp_394_, lean_object* v_t_395_, lean_object* v_a_396_, lean_object* v_h_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_394_, v_t_395_, v_a_396_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___redArg(lean_object* v_cmp_399_, lean_object* v_inst_400_, lean_object* v_t_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_399_, v_t_401_, v_a_402_, v_inst_400_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___redArg___boxed(lean_object* v_cmp_404_, lean_object* v_inst_405_, lean_object* v_t_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_TreeSet_get_x21___redArg(v_cmp_404_, v_inst_405_, v_t_406_, v_a_407_);
lean_dec(v_inst_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21(lean_object* v_00_u03b1_409_, lean_object* v_cmp_410_, lean_object* v_inst_411_, lean_object* v_t_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_410_, v_t_412_, v_a_413_, v_inst_411_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___boxed(lean_object* v_00_u03b1_415_, lean_object* v_cmp_416_, lean_object* v_inst_417_, lean_object* v_t_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_TreeSet_get_x21(v_00_u03b1_415_, v_cmp_416_, v_inst_417_, v_t_418_, v_a_419_);
lean_dec(v_inst_417_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg(lean_object* v_cmp_421_, lean_object* v_t_422_, lean_object* v_a_423_, lean_object* v_fallback_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_421_, v_t_422_, v_a_423_, v_fallback_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg___boxed(lean_object* v_cmp_426_, lean_object* v_t_427_, lean_object* v_a_428_, lean_object* v_fallback_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_TreeSet_getD___redArg(v_cmp_426_, v_t_427_, v_a_428_, v_fallback_429_);
lean_dec(v_fallback_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD(lean_object* v_00_u03b1_431_, lean_object* v_cmp_432_, lean_object* v_t_433_, lean_object* v_a_434_, lean_object* v_fallback_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_432_, v_t_433_, v_a_434_, v_fallback_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___boxed(lean_object* v_00_u03b1_437_, lean_object* v_cmp_438_, lean_object* v_t_439_, lean_object* v_a_440_, lean_object* v_fallback_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_TreeSet_getD(v_00_u03b1_437_, v_cmp_438_, v_t_439_, v_a_440_, v_fallback_441_);
lean_dec(v_fallback_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg(lean_object* v_t_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg___boxed(lean_object* v_t_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_TreeSet_min_x3f___redArg(v_t_445_);
lean_dec(v_t_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f(lean_object* v_00_u03b1_447_, lean_object* v_cmp_448_, lean_object* v_t_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___boxed(lean_object* v_00_u03b1_451_, lean_object* v_cmp_452_, lean_object* v_t_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_TreeSet_min_x3f(v_00_u03b1_451_, v_cmp_452_, v_t_453_);
lean_dec(v_t_453_);
lean_dec_ref(v_cmp_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg(lean_object* v_t_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg___boxed(lean_object* v_t_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_TreeSet_min___redArg(v_t_457_);
lean_dec(v_t_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min(lean_object* v_00_u03b1_459_, lean_object* v_cmp_460_, lean_object* v_t_461_, lean_object* v_h_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___boxed(lean_object* v_00_u03b1_464_, lean_object* v_cmp_465_, lean_object* v_t_466_, lean_object* v_h_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_TreeSet_min(v_00_u03b1_464_, v_cmp_465_, v_t_466_, v_h_467_);
lean_dec(v_t_466_);
lean_dec_ref(v_cmp_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg(lean_object* v_inst_469_, lean_object* v_t_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_469_, v_t_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg___boxed(lean_object* v_inst_472_, lean_object* v_t_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_TreeSet_min_x21___redArg(v_inst_472_, v_t_473_);
lean_dec(v_t_473_);
lean_dec(v_inst_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21(lean_object* v_00_u03b1_475_, lean_object* v_cmp_476_, lean_object* v_inst_477_, lean_object* v_t_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_477_, v_t_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___boxed(lean_object* v_00_u03b1_480_, lean_object* v_cmp_481_, lean_object* v_inst_482_, lean_object* v_t_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_TreeSet_min_x21(v_00_u03b1_480_, v_cmp_481_, v_inst_482_, v_t_483_);
lean_dec(v_t_483_);
lean_dec(v_inst_482_);
lean_dec_ref(v_cmp_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg(lean_object* v_t_485_, lean_object* v_fallback_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_485_, v_fallback_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg___boxed(lean_object* v_t_488_, lean_object* v_fallback_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_TreeSet_minD___redArg(v_t_488_, v_fallback_489_);
lean_dec(v_fallback_489_);
lean_dec(v_t_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD(lean_object* v_00_u03b1_491_, lean_object* v_cmp_492_, lean_object* v_t_493_, lean_object* v_fallback_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_493_, v_fallback_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___boxed(lean_object* v_00_u03b1_496_, lean_object* v_cmp_497_, lean_object* v_t_498_, lean_object* v_fallback_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_TreeSet_minD(v_00_u03b1_496_, v_cmp_497_, v_t_498_, v_fallback_499_);
lean_dec(v_fallback_499_);
lean_dec(v_t_498_);
lean_dec_ref(v_cmp_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg(lean_object* v_t_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg___boxed(lean_object* v_t_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_TreeSet_max_x3f___redArg(v_t_503_);
lean_dec(v_t_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f(lean_object* v_00_u03b1_505_, lean_object* v_cmp_506_, lean_object* v_t_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___boxed(lean_object* v_00_u03b1_509_, lean_object* v_cmp_510_, lean_object* v_t_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_TreeSet_max_x3f(v_00_u03b1_509_, v_cmp_510_, v_t_511_);
lean_dec(v_t_511_);
lean_dec_ref(v_cmp_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg(lean_object* v_t_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg___boxed(lean_object* v_t_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_TreeSet_max___redArg(v_t_515_);
lean_dec(v_t_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max(lean_object* v_00_u03b1_517_, lean_object* v_cmp_518_, lean_object* v_t_519_, lean_object* v_h_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_519_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___boxed(lean_object* v_00_u03b1_522_, lean_object* v_cmp_523_, lean_object* v_t_524_, lean_object* v_h_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_TreeSet_max(v_00_u03b1_522_, v_cmp_523_, v_t_524_, v_h_525_);
lean_dec(v_t_524_);
lean_dec_ref(v_cmp_523_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg(lean_object* v_inst_527_, lean_object* v_t_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_527_, v_t_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg___boxed(lean_object* v_inst_530_, lean_object* v_t_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_TreeSet_max_x21___redArg(v_inst_530_, v_t_531_);
lean_dec(v_t_531_);
lean_dec(v_inst_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21(lean_object* v_00_u03b1_533_, lean_object* v_cmp_534_, lean_object* v_inst_535_, lean_object* v_t_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_535_, v_t_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___boxed(lean_object* v_00_u03b1_538_, lean_object* v_cmp_539_, lean_object* v_inst_540_, lean_object* v_t_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_TreeSet_max_x21(v_00_u03b1_538_, v_cmp_539_, v_inst_540_, v_t_541_);
lean_dec(v_t_541_);
lean_dec(v_inst_540_);
lean_dec_ref(v_cmp_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg(lean_object* v_t_543_, lean_object* v_fallback_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_543_, v_fallback_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg___boxed(lean_object* v_t_546_, lean_object* v_fallback_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_TreeSet_maxD___redArg(v_t_546_, v_fallback_547_);
lean_dec(v_fallback_547_);
lean_dec(v_t_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD(lean_object* v_00_u03b1_549_, lean_object* v_cmp_550_, lean_object* v_t_551_, lean_object* v_fallback_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_551_, v_fallback_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___boxed(lean_object* v_00_u03b1_554_, lean_object* v_cmp_555_, lean_object* v_t_556_, lean_object* v_fallback_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_TreeSet_maxD(v_00_u03b1_554_, v_cmp_555_, v_t_556_, v_fallback_557_);
lean_dec(v_fallback_557_);
lean_dec(v_t_556_);
lean_dec_ref(v_cmp_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg(lean_object* v_t_559_, lean_object* v_n_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_559_, v_n_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg___boxed(lean_object* v_t_562_, lean_object* v_n_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_TreeSet_atIdx_x3f___redArg(v_t_562_, v_n_563_);
lean_dec(v_t_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f(lean_object* v_00_u03b1_565_, lean_object* v_cmp_566_, lean_object* v_t_567_, lean_object* v_n_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_567_, v_n_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___boxed(lean_object* v_00_u03b1_570_, lean_object* v_cmp_571_, lean_object* v_t_572_, lean_object* v_n_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_TreeSet_atIdx_x3f(v_00_u03b1_570_, v_cmp_571_, v_t_572_, v_n_573_);
lean_dec(v_t_572_);
lean_dec_ref(v_cmp_571_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg(lean_object* v_t_575_, lean_object* v_n_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_575_, v_n_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg___boxed(lean_object* v_t_578_, lean_object* v_n_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_TreeSet_atIdx___redArg(v_t_578_, v_n_579_);
lean_dec(v_t_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx(lean_object* v_00_u03b1_581_, lean_object* v_cmp_582_, lean_object* v_t_583_, lean_object* v_n_584_, lean_object* v_h_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_583_, v_n_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___boxed(lean_object* v_00_u03b1_587_, lean_object* v_cmp_588_, lean_object* v_t_589_, lean_object* v_n_590_, lean_object* v_h_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Std_TreeSet_atIdx(v_00_u03b1_587_, v_cmp_588_, v_t_589_, v_n_590_, v_h_591_);
lean_dec(v_t_589_);
lean_dec_ref(v_cmp_588_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg(lean_object* v_inst_593_, lean_object* v_t_594_, lean_object* v_n_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_593_, v_t_594_, v_n_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg___boxed(lean_object* v_inst_597_, lean_object* v_t_598_, lean_object* v_n_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_TreeSet_atIdx_x21___redArg(v_inst_597_, v_t_598_, v_n_599_);
lean_dec(v_t_598_);
lean_dec(v_inst_597_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21(lean_object* v_00_u03b1_601_, lean_object* v_cmp_602_, lean_object* v_inst_603_, lean_object* v_t_604_, lean_object* v_n_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_603_, v_t_604_, v_n_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___boxed(lean_object* v_00_u03b1_607_, lean_object* v_cmp_608_, lean_object* v_inst_609_, lean_object* v_t_610_, lean_object* v_n_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_TreeSet_atIdx_x21(v_00_u03b1_607_, v_cmp_608_, v_inst_609_, v_t_610_, v_n_611_);
lean_dec(v_t_610_);
lean_dec(v_inst_609_);
lean_dec_ref(v_cmp_608_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg(lean_object* v_t_613_, lean_object* v_n_614_, lean_object* v_fallback_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_613_, v_n_614_, v_fallback_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg___boxed(lean_object* v_t_617_, lean_object* v_n_618_, lean_object* v_fallback_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_TreeSet_atIdxD___redArg(v_t_617_, v_n_618_, v_fallback_619_);
lean_dec(v_fallback_619_);
lean_dec(v_t_617_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD(lean_object* v_00_u03b1_621_, lean_object* v_cmp_622_, lean_object* v_t_623_, lean_object* v_n_624_, lean_object* v_fallback_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_623_, v_n_624_, v_fallback_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___boxed(lean_object* v_00_u03b1_627_, lean_object* v_cmp_628_, lean_object* v_t_629_, lean_object* v_n_630_, lean_object* v_fallback_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_TreeSet_atIdxD(v_00_u03b1_627_, v_cmp_628_, v_t_629_, v_n_630_, v_fallback_631_);
lean_dec(v_fallback_631_);
lean_dec(v_t_629_);
lean_dec_ref(v_cmp_628_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f___redArg(lean_object* v_cmp_633_, lean_object* v_t_634_, lean_object* v_k_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(0);
v___x_637_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_633_, v_k_635_, v___x_636_, v_t_634_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f(lean_object* v_00_u03b1_638_, lean_object* v_cmp_639_, lean_object* v_t_640_, lean_object* v_k_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_box(0);
v___x_643_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_639_, v_k_641_, v___x_642_, v_t_640_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f___redArg(lean_object* v_cmp_644_, lean_object* v_t_645_, lean_object* v_k_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_box(0);
v___x_648_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_644_, v_k_646_, v___x_647_, v_t_645_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f(lean_object* v_00_u03b1_649_, lean_object* v_cmp_650_, lean_object* v_t_651_, lean_object* v_k_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_box(0);
v___x_654_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_650_, v_k_652_, v___x_653_, v_t_651_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f___redArg(lean_object* v_cmp_655_, lean_object* v_t_656_, lean_object* v_k_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_box(0);
v___x_659_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_655_, v_k_657_, v___x_658_, v_t_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f(lean_object* v_00_u03b1_660_, lean_object* v_cmp_661_, lean_object* v_t_662_, lean_object* v_k_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_box(0);
v___x_665_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_661_, v_k_663_, v___x_664_, v_t_662_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f___redArg(lean_object* v_cmp_666_, lean_object* v_t_667_, lean_object* v_k_668_){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_box(0);
v___x_670_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_666_, v_k_668_, v___x_669_, v_t_667_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f(lean_object* v_00_u03b1_671_, lean_object* v_cmp_672_, lean_object* v_t_673_, lean_object* v_k_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_box(0);
v___x_676_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_672_, v_k_674_, v___x_675_, v_t_673_);
return v___x_676_;
}
}
static lean_object* _init_l_Std_TreeSet_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_680_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__2));
v___x_681_ = lean_unsigned_to_nat(14u);
v___x_682_ = lean_unsigned_to_nat(22u);
v___x_683_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__1));
v___x_684_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__0));
v___x_685_ = l_mkPanicMessageWithDecl(v___x_684_, v___x_683_, v___x_682_, v___x_681_, v___x_680_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___redArg(lean_object* v_cmp_686_, lean_object* v_inst_687_, lean_object* v_t_688_, lean_object* v_k_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_box(0);
v___x_691_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_686_, v_k_689_, v___x_690_, v_t_688_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_693_ = l_panic___redArg(v_inst_687_, v___x_692_);
return v___x_693_;
}
else
{
lean_object* v_val_694_; 
v_val_694_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v___x_691_, 1);
return v_val_694_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___redArg___boxed(lean_object* v_cmp_695_, lean_object* v_inst_696_, lean_object* v_t_697_, lean_object* v_k_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_TreeSet_getGE_x21___redArg(v_cmp_695_, v_inst_696_, v_t_697_, v_k_698_);
lean_dec(v_inst_696_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21(lean_object* v_00_u03b1_700_, lean_object* v_cmp_701_, lean_object* v_inst_702_, lean_object* v_t_703_, lean_object* v_k_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_box(0);
v___x_706_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_701_, v_k_704_, v___x_705_, v_t_703_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___boxed(lean_object* v_00_u03b1_710_, lean_object* v_cmp_711_, lean_object* v_inst_712_, lean_object* v_t_713_, lean_object* v_k_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_TreeSet_getGE_x21(v_00_u03b1_710_, v_cmp_711_, v_inst_712_, v_t_713_, v_k_714_);
lean_dec(v_inst_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg(lean_object* v_cmp_716_, lean_object* v_inst_717_, lean_object* v_t_718_, lean_object* v_k_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_box(0);
v___x_721_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_716_, v_k_719_, v___x_720_, v_t_718_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_723_ = l_panic___redArg(v_inst_717_, v___x_722_);
return v___x_723_;
}
else
{
lean_object* v_val_724_; 
v_val_724_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_val_724_);
lean_dec_ref_known(v___x_721_, 1);
return v_val_724_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg___boxed(lean_object* v_cmp_725_, lean_object* v_inst_726_, lean_object* v_t_727_, lean_object* v_k_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_TreeSet_getGT_x21___redArg(v_cmp_725_, v_inst_726_, v_t_727_, v_k_728_);
lean_dec(v_inst_726_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21(lean_object* v_00_u03b1_730_, lean_object* v_cmp_731_, lean_object* v_inst_732_, lean_object* v_t_733_, lean_object* v_k_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_box(0);
v___x_736_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_731_, v_k_734_, v___x_735_, v_t_733_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_738_ = l_panic___redArg(v_inst_732_, v___x_737_);
return v___x_738_;
}
else
{
lean_object* v_val_739_; 
v_val_739_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v___x_736_, 1);
return v_val_739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___boxed(lean_object* v_00_u03b1_740_, lean_object* v_cmp_741_, lean_object* v_inst_742_, lean_object* v_t_743_, lean_object* v_k_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Std_TreeSet_getGT_x21(v_00_u03b1_740_, v_cmp_741_, v_inst_742_, v_t_743_, v_k_744_);
lean_dec(v_inst_742_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg(lean_object* v_cmp_746_, lean_object* v_inst_747_, lean_object* v_t_748_, lean_object* v_k_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_box(0);
v___x_751_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_746_, v_k_749_, v___x_750_, v_t_748_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_753_ = l_panic___redArg(v_inst_747_, v___x_752_);
return v___x_753_;
}
else
{
lean_object* v_val_754_; 
v_val_754_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_val_754_);
lean_dec_ref_known(v___x_751_, 1);
return v_val_754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg___boxed(lean_object* v_cmp_755_, lean_object* v_inst_756_, lean_object* v_t_757_, lean_object* v_k_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_TreeSet_getLE_x21___redArg(v_cmp_755_, v_inst_756_, v_t_757_, v_k_758_);
lean_dec(v_inst_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21(lean_object* v_00_u03b1_760_, lean_object* v_cmp_761_, lean_object* v_inst_762_, lean_object* v_t_763_, lean_object* v_k_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_box(0);
v___x_766_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_761_, v_k_764_, v___x_765_, v_t_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_768_ = l_panic___redArg(v_inst_762_, v___x_767_);
return v___x_768_;
}
else
{
lean_object* v_val_769_; 
v_val_769_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v___x_766_, 1);
return v_val_769_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___boxed(lean_object* v_00_u03b1_770_, lean_object* v_cmp_771_, lean_object* v_inst_772_, lean_object* v_t_773_, lean_object* v_k_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_TreeSet_getLE_x21(v_00_u03b1_770_, v_cmp_771_, v_inst_772_, v_t_773_, v_k_774_);
lean_dec(v_inst_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg(lean_object* v_cmp_776_, lean_object* v_inst_777_, lean_object* v_t_778_, lean_object* v_k_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_box(0);
v___x_781_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_776_, v_k_779_, v___x_780_, v_t_778_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_783_ = l_panic___redArg(v_inst_777_, v___x_782_);
return v___x_783_;
}
else
{
lean_object* v_val_784_; 
v_val_784_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v___x_781_, 1);
return v_val_784_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg___boxed(lean_object* v_cmp_785_, lean_object* v_inst_786_, lean_object* v_t_787_, lean_object* v_k_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_TreeSet_getLT_x21___redArg(v_cmp_785_, v_inst_786_, v_t_787_, v_k_788_);
lean_dec(v_inst_786_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21(lean_object* v_00_u03b1_790_, lean_object* v_cmp_791_, lean_object* v_inst_792_, lean_object* v_t_793_, lean_object* v_k_794_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_box(0);
v___x_796_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_791_, v_k_794_, v___x_795_, v_t_793_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_798_ = l_panic___redArg(v_inst_792_, v___x_797_);
return v___x_798_;
}
else
{
lean_object* v_val_799_; 
v_val_799_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_796_, 1);
return v_val_799_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___boxed(lean_object* v_00_u03b1_800_, lean_object* v_cmp_801_, lean_object* v_inst_802_, lean_object* v_t_803_, lean_object* v_k_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_TreeSet_getLT_x21(v_00_u03b1_800_, v_cmp_801_, v_inst_802_, v_t_803_, v_k_804_);
lean_dec(v_inst_802_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg(lean_object* v_cmp_806_, lean_object* v_t_807_, lean_object* v_k_808_, lean_object* v_fallback_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_box(0);
v___x_811_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_806_, v_k_808_, v___x_810_, v_t_807_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_inc(v_fallback_809_);
return v_fallback_809_;
}
else
{
lean_object* v_val_812_; 
v_val_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v___x_811_, 1);
return v_val_812_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg___boxed(lean_object* v_cmp_813_, lean_object* v_t_814_, lean_object* v_k_815_, lean_object* v_fallback_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_TreeSet_getGED___redArg(v_cmp_813_, v_t_814_, v_k_815_, v_fallback_816_);
lean_dec(v_fallback_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED(lean_object* v_00_u03b1_818_, lean_object* v_cmp_819_, lean_object* v_t_820_, lean_object* v_k_821_, lean_object* v_fallback_822_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_box(0);
v___x_824_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_819_, v_k_821_, v___x_823_, v_t_820_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_inc(v_fallback_822_);
return v_fallback_822_;
}
else
{
lean_object* v_val_825_; 
v_val_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_val_825_);
lean_dec_ref_known(v___x_824_, 1);
return v_val_825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___boxed(lean_object* v_00_u03b1_826_, lean_object* v_cmp_827_, lean_object* v_t_828_, lean_object* v_k_829_, lean_object* v_fallback_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_TreeSet_getGED(v_00_u03b1_826_, v_cmp_827_, v_t_828_, v_k_829_, v_fallback_830_);
lean_dec(v_fallback_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg(lean_object* v_cmp_832_, lean_object* v_t_833_, lean_object* v_k_834_, lean_object* v_fallback_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_box(0);
v___x_837_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_832_, v_k_834_, v___x_836_, v_t_833_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_inc(v_fallback_835_);
return v_fallback_835_;
}
else
{
lean_object* v_val_838_; 
v_val_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_val_838_);
lean_dec_ref_known(v___x_837_, 1);
return v_val_838_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg___boxed(lean_object* v_cmp_839_, lean_object* v_t_840_, lean_object* v_k_841_, lean_object* v_fallback_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_TreeSet_getGTD___redArg(v_cmp_839_, v_t_840_, v_k_841_, v_fallback_842_);
lean_dec(v_fallback_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD(lean_object* v_00_u03b1_844_, lean_object* v_cmp_845_, lean_object* v_t_846_, lean_object* v_k_847_, lean_object* v_fallback_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_box(0);
v___x_850_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_845_, v_k_847_, v___x_849_, v_t_846_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_inc(v_fallback_848_);
return v_fallback_848_;
}
else
{
lean_object* v_val_851_; 
v_val_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v___x_850_, 1);
return v_val_851_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___boxed(lean_object* v_00_u03b1_852_, lean_object* v_cmp_853_, lean_object* v_t_854_, lean_object* v_k_855_, lean_object* v_fallback_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_TreeSet_getGTD(v_00_u03b1_852_, v_cmp_853_, v_t_854_, v_k_855_, v_fallback_856_);
lean_dec(v_fallback_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg(lean_object* v_cmp_858_, lean_object* v_t_859_, lean_object* v_k_860_, lean_object* v_fallback_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_box(0);
v___x_863_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_858_, v_k_860_, v___x_862_, v_t_859_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_inc(v_fallback_861_);
return v_fallback_861_;
}
else
{
lean_object* v_val_864_; 
v_val_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v___x_863_, 1);
return v_val_864_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg___boxed(lean_object* v_cmp_865_, lean_object* v_t_866_, lean_object* v_k_867_, lean_object* v_fallback_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_TreeSet_getLED___redArg(v_cmp_865_, v_t_866_, v_k_867_, v_fallback_868_);
lean_dec(v_fallback_868_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED(lean_object* v_00_u03b1_870_, lean_object* v_cmp_871_, lean_object* v_t_872_, lean_object* v_k_873_, lean_object* v_fallback_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_box(0);
v___x_876_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_871_, v_k_873_, v___x_875_, v_t_872_);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___boxed(lean_object* v_00_u03b1_878_, lean_object* v_cmp_879_, lean_object* v_t_880_, lean_object* v_k_881_, lean_object* v_fallback_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Std_TreeSet_getLED(v_00_u03b1_878_, v_cmp_879_, v_t_880_, v_k_881_, v_fallback_882_);
lean_dec(v_fallback_882_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg(lean_object* v_cmp_884_, lean_object* v_t_885_, lean_object* v_k_886_, lean_object* v_fallback_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_box(0);
v___x_889_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_884_, v_k_886_, v___x_888_, v_t_885_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_inc(v_fallback_887_);
return v_fallback_887_;
}
else
{
lean_object* v_val_890_; 
v_val_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v___x_889_, 1);
return v_val_890_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg___boxed(lean_object* v_cmp_891_, lean_object* v_t_892_, lean_object* v_k_893_, lean_object* v_fallback_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_TreeSet_getLTD___redArg(v_cmp_891_, v_t_892_, v_k_893_, v_fallback_894_);
lean_dec(v_fallback_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD(lean_object* v_00_u03b1_896_, lean_object* v_cmp_897_, lean_object* v_t_898_, lean_object* v_k_899_, lean_object* v_fallback_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_box(0);
v___x_902_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_897_, v_k_899_, v___x_901_, v_t_898_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_inc(v_fallback_900_);
return v_fallback_900_;
}
else
{
lean_object* v_val_903_; 
v_val_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_val_903_);
lean_dec_ref_known(v___x_902_, 1);
return v_val_903_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___boxed(lean_object* v_00_u03b1_904_, lean_object* v_cmp_905_, lean_object* v_t_906_, lean_object* v_k_907_, lean_object* v_fallback_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_TreeSet_getLTD(v_00_u03b1_904_, v_cmp_905_, v_t_906_, v_k_907_, v_fallback_908_);
lean_dec(v_fallback_908_);
return v_res_909_;
}
}
uint8_t l_Std_TreeSet_filter___redArg___lam__0(lean_object* v_f_910_, lean_object* v_a_911_, lean_object* v_x_912_){
_start:
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_apply_1(v_f_910_, v_a_911_);
v___x_914_ = lean_unbox(v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT void l_Std_TreeSet_filter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_910_ = stack[0].m_obj;
lean_object* v_a_911_ = stack[1].m_obj;
lean_object* v_x_912_ = stack[2].m_obj;
uint8_t v_res_915_;
v_res_915_ = l_Std_TreeSet_filter___redArg___lam__0(v_f_910_, v_a_911_, v_x_912_);
stack->m_num = v_res_915_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg___lam__0___boxed(lean_object* v_f_916_, lean_object* v_a_917_, lean_object* v_x_918_){
_start:
{
uint8_t v_res_919_; lean_object* v_r_920_; 
v_res_919_ = l_Std_TreeSet_filter___redArg___lam__0(v_f_916_, v_a_917_, v_x_918_);
v_r_920_ = lean_box(v_res_919_);
return v_r_920_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg(lean_object* v_f_921_, lean_object* v_m_922_){
_start:
{
lean_object* v___f_923_; lean_object* v___x_924_; 
v___f_923_ = lean_alloc_closure((void*)(l_Std_TreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_923_, 0, v_f_921_);
v___x_924_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_923_, v_m_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter(lean_object* v_00_u03b1_925_, lean_object* v_cmp_926_, lean_object* v_f_927_, lean_object* v_m_928_){
_start:
{
lean_object* v___f_929_; lean_object* v___x_930_; 
v___f_929_ = lean_alloc_closure((void*)(l_Std_TreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_929_, 0, v_f_927_);
v___x_930_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_929_, v_m_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___boxed(lean_object* v_00_u03b1_931_, lean_object* v_cmp_932_, lean_object* v_f_933_, lean_object* v_m_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_TreeSet_filter(v_00_u03b1_931_, v_cmp_932_, v_f_933_, v_m_934_);
lean_dec_ref(v_cmp_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg___lam__0(lean_object* v_f_936_, lean_object* v_c_937_, lean_object* v_a_938_, lean_object* v_x_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = lean_apply_2(v_f_936_, v_c_937_, v_a_938_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg(lean_object* v_inst_941_, lean_object* v_f_942_, lean_object* v_init_943_, lean_object* v_t_944_){
_start:
{
lean_object* v___f_945_; lean_object* v___x_946_; 
v___f_945_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_945_, 0, v_f_942_);
v___x_946_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_941_, v___f_945_, v_init_943_, v_t_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM(lean_object* v_00_u03b1_947_, lean_object* v_cmp_948_, lean_object* v_m_949_, lean_object* v_00_u03b4_950_, lean_object* v_inst_951_, lean_object* v_f_952_, lean_object* v_init_953_, lean_object* v_t_954_){
_start:
{
lean_object* v___f_955_; lean_object* v___x_956_; 
v___f_955_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_955_, 0, v_f_952_);
v___x_956_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_951_, v___f_955_, v_init_953_, v_t_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___boxed(lean_object* v_00_u03b1_957_, lean_object* v_cmp_958_, lean_object* v_m_959_, lean_object* v_00_u03b4_960_, lean_object* v_inst_961_, lean_object* v_f_962_, lean_object* v_init_963_, lean_object* v_t_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_TreeSet_foldlM(v_00_u03b1_957_, v_cmp_958_, v_m_959_, v_00_u03b4_960_, v_inst_961_, v_f_962_, v_init_963_, v_t_964_);
lean_dec_ref(v_cmp_958_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___redArg(lean_object* v_f_966_, lean_object* v_init_967_, lean_object* v_t_968_){
_start:
{
lean_object* v___f_969_; lean_object* v___x_970_; 
v___f_969_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_969_, 0, v_f_966_);
v___x_970_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_969_, v_init_967_, v_t_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl(lean_object* v_00_u03b1_971_, lean_object* v_cmp_972_, lean_object* v_00_u03b4_973_, lean_object* v_f_974_, lean_object* v_init_975_, lean_object* v_t_976_){
_start:
{
lean_object* v___f_977_; lean_object* v___x_978_; 
v___f_977_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_977_, 0, v_f_974_);
v___x_978_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_977_, v_init_975_, v_t_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___boxed(lean_object* v_00_u03b1_979_, lean_object* v_cmp_980_, lean_object* v_00_u03b4_981_, lean_object* v_f_982_, lean_object* v_init_983_, lean_object* v_t_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_TreeSet_foldl(v_00_u03b1_979_, v_cmp_980_, v_00_u03b4_981_, v_f_982_, v_init_983_, v_t_984_);
lean_dec_ref(v_cmp_980_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg___lam__0(lean_object* v_f_986_, lean_object* v_a_987_, lean_object* v_x_988_, lean_object* v_acc_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = lean_apply_2(v_f_986_, v_a_987_, v_acc_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg(lean_object* v_inst_991_, lean_object* v_f_992_, lean_object* v_init_993_, lean_object* v_t_994_){
_start:
{
lean_object* v___f_995_; lean_object* v___x_996_; 
v___f_995_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_995_, 0, v_f_992_);
v___x_996_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_991_, v___f_995_, v_init_993_, v_t_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM(lean_object* v_00_u03b1_997_, lean_object* v_cmp_998_, lean_object* v_m_999_, lean_object* v_00_u03b4_1000_, lean_object* v_inst_1001_, lean_object* v_f_1002_, lean_object* v_init_1003_, lean_object* v_t_1004_){
_start:
{
lean_object* v___f_1005_; lean_object* v___x_1006_; 
v___f_1005_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1005_, 0, v_f_1002_);
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1001_, v___f_1005_, v_init_1003_, v_t_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___boxed(lean_object* v_00_u03b1_1007_, lean_object* v_cmp_1008_, lean_object* v_m_1009_, lean_object* v_00_u03b4_1010_, lean_object* v_inst_1011_, lean_object* v_f_1012_, lean_object* v_init_1013_, lean_object* v_t_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std_TreeSet_foldrM(v_00_u03b1_1007_, v_cmp_1008_, v_m_1009_, v_00_u03b4_1010_, v_inst_1011_, v_f_1012_, v_init_1013_, v_t_1014_);
lean_dec_ref(v_cmp_1008_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg___lam__0(lean_object* v_f_1016_, lean_object* v_x1_1017_, lean_object* v_x2_1018_, lean_object* v_x3_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_apply_2(v_f_1016_, v_x1_1017_, v_x3_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg(lean_object* v_f_1040_, lean_object* v_init_1041_, lean_object* v_t_1042_){
_start:
{
lean_object* v___f_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___f_1043_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1043_, 0, v_f_1040_);
v___x_1044_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1044_, v___f_1043_, v_init_1041_, v_t_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr(lean_object* v_00_u03b1_1046_, lean_object* v_cmp_1047_, lean_object* v_00_u03b4_1048_, lean_object* v_f_1049_, lean_object* v_init_1050_, lean_object* v_t_1051_){
_start:
{
lean_object* v___f_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___f_1052_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1052_, 0, v_f_1049_);
v___x_1053_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1054_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1053_, v___f_1052_, v_init_1050_, v_t_1051_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___boxed(lean_object* v_00_u03b1_1055_, lean_object* v_cmp_1056_, lean_object* v_00_u03b4_1057_, lean_object* v_f_1058_, lean_object* v_init_1059_, lean_object* v_t_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Std_TreeSet_foldr(v_00_u03b1_1055_, v_cmp_1056_, v_00_u03b4_1057_, v_f_1058_, v_init_1059_, v_t_1060_);
lean_dec_ref(v_cmp_1056_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg___lam__0(lean_object* v_f_1062_, lean_object* v_cmp_1063_, lean_object* v_x_1064_, lean_object* v_a_1065_, lean_object* v_b_1066_){
_start:
{
lean_object* v_fst_1067_; lean_object* v_snd_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1082_; 
v_fst_1067_ = lean_ctor_get(v_x_1064_, 0);
v_snd_1068_ = lean_ctor_get(v_x_1064_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_x_1064_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1070_ = v_x_1064_;
v_isShared_1071_ = v_isSharedCheck_1082_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_snd_1068_);
lean_inc(v_fst_1067_);
lean_dec(v_x_1064_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1082_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
lean_inc(v_a_1065_);
v___x_1072_ = lean_apply_1(v_f_1062_, v_a_1065_);
v___x_1073_ = lean_unbox(v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1063_, v_a_1065_, v_b_1066_, v_snd_1068_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v___x_1074_);
v___x_1076_ = v___x_1070_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_fst_1067_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1063_, v_a_1065_, v_b_1066_, v_fst_1067_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1078_);
v___x_1080_ = v___x_1070_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_snd_1068_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg(lean_object* v_cmp_1085_, lean_object* v_f_1086_, lean_object* v_t_1087_){
_start:
{
lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v_p_1090_; lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v___f_1088_ = lean_alloc_closure((void*)(l_Std_TreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1088_, 0, v_f_1086_);
lean_closure_set(v___f_1088_, 1, v_cmp_1085_);
v___x_1089_ = ((lean_object*)(l_Std_TreeSet_partition___redArg___closed__0));
v_p_1090_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1088_, v___x_1089_, v_t_1087_);
v_fst_1091_ = lean_ctor_get(v_p_1090_, 0);
v_snd_1092_ = lean_ctor_get(v_p_1090_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_p_1090_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v_p_1090_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_snd_1092_);
lean_inc(v_fst_1091_);
lean_dec(v_p_1090_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_fst_1091_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_snd_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition(lean_object* v_00_u03b1_1100_, lean_object* v_cmp_1101_, lean_object* v_f_1102_, lean_object* v_t_1103_){
_start:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v_p_1106_; lean_object* v_fst_1107_; lean_object* v_snd_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v___f_1104_ = lean_alloc_closure((void*)(l_Std_TreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1104_, 0, v_f_1102_);
lean_closure_set(v___f_1104_, 1, v_cmp_1101_);
v___x_1105_ = ((lean_object*)(l_Std_TreeSet_partition___redArg___closed__0));
v_p_1106_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1104_, v___x_1105_, v_t_1103_);
v_fst_1107_ = lean_ctor_get(v_p_1106_, 0);
v_snd_1108_ = lean_ctor_get(v_p_1106_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_p_1106_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v_p_1106_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_snd_1108_);
lean_inc(v_fst_1107_);
lean_dec(v_p_1106_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_fst_1107_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_snd_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg___lam__0(lean_object* v_f_1116_, lean_object* v_x_1117_, lean_object* v_k_1118_, lean_object* v_v_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_apply_1(v_f_1116_, v_k_1118_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg(lean_object* v_inst_1121_, lean_object* v_f_1122_, lean_object* v_t_1123_){
_start:
{
lean_object* v___f_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___f_1124_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1124_, 0, v_f_1122_);
v___x_1125_ = lean_box(0);
v___x_1126_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1121_, v___f_1124_, v___x_1125_, v_t_1123_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM(lean_object* v_00_u03b1_1127_, lean_object* v_cmp_1128_, lean_object* v_m_1129_, lean_object* v_inst_1130_, lean_object* v_f_1131_, lean_object* v_t_1132_){
_start:
{
lean_object* v___f_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___f_1133_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1133_, 0, v_f_1131_);
v___x_1134_ = lean_box(0);
v___x_1135_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1130_, v___f_1133_, v___x_1134_, v_t_1132_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_cmp_1137_, lean_object* v_m_1138_, lean_object* v_inst_1139_, lean_object* v_f_1140_, lean_object* v_t_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_TreeSet_forM(v_00_u03b1_1136_, v_cmp_1137_, v_m_1138_, v_inst_1139_, v_f_1140_, v_t_1141_);
lean_dec_ref(v_cmp_1137_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__0(lean_object* v_f_1143_, lean_object* v_a_1144_, lean_object* v_b_1145_, lean_object* v_c_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_apply_2(v_f_1143_, v_a_1144_, v_c_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__1(lean_object* v_toPure_1148_, lean_object* v_____do__lift_1149_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg(lean_object* v_inst_1152_, lean_object* v_f_1153_, lean_object* v_init_1154_, lean_object* v_t_1155_){
_start:
{
lean_object* v_toApplicative_1156_; lean_object* v_toBind_1157_; lean_object* v_toPure_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; lean_object* v___f_1161_; lean_object* v___x_1162_; 
v_toApplicative_1156_ = lean_ctor_get(v_inst_1152_, 0);
v_toBind_1157_ = lean_ctor_get(v_inst_1152_, 1);
lean_inc(v_toBind_1157_);
v_toPure_1158_ = lean_ctor_get(v_toApplicative_1156_, 1);
lean_inc(v_toPure_1158_);
v___f_1159_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1159_, 0, v_f_1153_);
v___x_1160_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1152_, v___f_1159_, v_init_1154_, v_t_1155_);
v___f_1161_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1161_, 0, v_toPure_1158_);
v___x_1162_ = lean_apply_4(v_toBind_1157_, lean_box(0), lean_box(0), v___x_1160_, v___f_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn(lean_object* v_00_u03b1_1163_, lean_object* v_cmp_1164_, lean_object* v_00_u03b4_1165_, lean_object* v_m_1166_, lean_object* v_inst_1167_, lean_object* v_f_1168_, lean_object* v_init_1169_, lean_object* v_t_1170_){
_start:
{
lean_object* v_toApplicative_1171_; lean_object* v_toBind_1172_; lean_object* v_toPure_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; 
v_toApplicative_1171_ = lean_ctor_get(v_inst_1167_, 0);
v_toBind_1172_ = lean_ctor_get(v_inst_1167_, 1);
lean_inc(v_toBind_1172_);
v_toPure_1173_ = lean_ctor_get(v_toApplicative_1171_, 1);
lean_inc(v_toPure_1173_);
v___f_1174_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1174_, 0, v_f_1168_);
v___x_1175_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1167_, v___f_1174_, v_init_1169_, v_t_1170_);
v___f_1176_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1176_, 0, v_toPure_1173_);
v___x_1177_ = lean_apply_4(v_toBind_1172_, lean_box(0), lean_box(0), v___x_1175_, v___f_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___boxed(lean_object* v_00_u03b1_1178_, lean_object* v_cmp_1179_, lean_object* v_00_u03b4_1180_, lean_object* v_m_1181_, lean_object* v_inst_1182_, lean_object* v_f_1183_, lean_object* v_init_1184_, lean_object* v_t_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Std_TreeSet_forIn(v_00_u03b1_1178_, v_cmp_1179_, v_00_u03b4_1180_, v_m_1181_, v_inst_1182_, v_f_1183_, v_init_1184_, v_t_1185_);
lean_dec_ref(v_cmp_1179_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg___lam__1(lean_object* v_inst_1187_, lean_object* v_t_1188_, lean_object* v_f_1189_){
_start:
{
lean_object* v___f_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___f_1190_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1190_, 0, v_f_1189_);
v___x_1191_ = lean_box(0);
v___x_1192_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1187_, v___f_1190_, v___x_1191_, v_t_1188_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg(lean_object* v_inst_1193_){
_start:
{
lean_object* v___f_1194_; 
v___f_1194_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1194_, 0, v_inst_1193_);
return v___f_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad(lean_object* v_00_u03b1_1195_, lean_object* v_cmp_1196_, lean_object* v_m_1197_, lean_object* v_inst_1198_){
_start:
{
lean_object* v___f_1199_; 
v___f_1199_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1199_, 0, v_inst_1198_);
return v___f_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___boxed(lean_object* v_00_u03b1_1200_, lean_object* v_cmp_1201_, lean_object* v_m_1202_, lean_object* v_inst_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Std_TreeSet_instForMOfMonad(v_00_u03b1_1200_, v_cmp_1201_, v_m_1202_, v_inst_1203_);
lean_dec_ref(v_cmp_1201_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg___lam__2(lean_object* v_inst_1205_, lean_object* v_00_u03b2_1206_, lean_object* v_m_1207_, lean_object* v_init_1208_, lean_object* v_f_1209_){
_start:
{
lean_object* v_toApplicative_1210_; lean_object* v_toBind_1211_; lean_object* v_toPure_1212_; lean_object* v___f_1213_; lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; 
v_toApplicative_1210_ = lean_ctor_get(v_inst_1205_, 0);
v_toBind_1211_ = lean_ctor_get(v_inst_1205_, 1);
lean_inc(v_toBind_1211_);
v_toPure_1212_ = lean_ctor_get(v_toApplicative_1210_, 1);
lean_inc(v_toPure_1212_);
v___f_1213_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1213_, 0, v_f_1209_);
v___x_1214_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1205_, v___f_1213_, v_init_1208_, v_m_1207_);
v___f_1215_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1215_, 0, v_toPure_1212_);
v___x_1216_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1214_, v___f_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg(lean_object* v_inst_1217_){
_start:
{
lean_object* v___f_1218_; 
v___f_1218_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1218_, 0, v_inst_1217_);
return v___f_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad(lean_object* v_00_u03b1_1219_, lean_object* v_cmp_1220_, lean_object* v_m_1221_, lean_object* v_inst_1222_){
_start:
{
lean_object* v___f_1223_; 
v___f_1223_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1223_, 0, v_inst_1222_);
return v___f_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_1224_, lean_object* v_cmp_1225_, lean_object* v_m_1226_, lean_object* v_inst_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Std_TreeSet_instForInOfMonad(v_00_u03b1_1224_, v_cmp_1225_, v_m_1226_, v_inst_1227_);
lean_dec_ref(v_cmp_1225_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0(lean_object* v_p_1229_, lean_object* v___x_1230_, lean_object* v___x_1231_, lean_object* v_a_1232_, lean_object* v_b_1233_, lean_object* v_acc_1234_){
_start:
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = lean_apply_1(v_p_1229_, v_a_1232_);
v___x_1236_ = lean_unbox(v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1230_);
return v___x_1237_;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec_ref(v___x_1230_);
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1235_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
lean_ctor_set(v___x_1239_, 1, v___x_1231_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0___boxed(lean_object* v_p_1241_, lean_object* v___x_1242_, lean_object* v___x_1243_, lean_object* v_a_1244_, lean_object* v_b_1245_, lean_object* v_acc_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Std_TreeSet_any___redArg___lam__0(v_p_1241_, v___x_1242_, v___x_1243_, v_a_1244_, v_b_1245_, v_acc_1246_);
lean_dec_ref(v_acc_1246_);
return v_res_1247_;
}
}
uint8_t l_Std_TreeSet_any___redArg(lean_object* v_t_1251_, lean_object* v_p_1252_){
_start:
{
lean_object* v___y_1254_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; lean_object* v_a_1264_; 
v___x_1259_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1260_ = lean_box(0);
v___x_1261_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1262_ = lean_alloc_closure((void*)(l_Std_TreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1262_, 0, v_p_1252_);
lean_closure_set(v___f_1262_, 1, v___x_1261_);
lean_closure_set(v___f_1262_, 2, v___x_1260_);
v___x_1263_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1259_, v___f_1262_, v___x_1261_, v_t_1251_);
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___y_1254_ = v_a_1264_;
goto v___jp_1253_;
v___jp_1253_:
{
lean_object* v_fst_1255_; 
v_fst_1255_ = lean_ctor_get(v___y_1254_, 0);
lean_inc(v_fst_1255_);
lean_dec_ref(v___y_1254_);
if (lean_obj_tag(v_fst_1255_) == 0)
{
uint8_t v___x_1256_; 
v___x_1256_ = 0;
return v___x_1256_;
}
else
{
lean_object* v_val_1257_; uint8_t v___x_1258_; 
v_val_1257_ = lean_ctor_get(v_fst_1255_, 0);
lean_inc(v_val_1257_);
lean_dec_ref_known(v_fst_1255_, 1);
v___x_1258_ = lean_unbox(v_val_1257_);
lean_dec(v_val_1257_);
return v___x_1258_;
}
}
}
}
LEAN_EXPORT void l_Std_TreeSet_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1251_ = stack[0].m_obj;
lean_object* v_p_1252_ = stack[1].m_obj;
uint8_t v_res_1265_;
v_res_1265_ = l_Std_TreeSet_any___redArg(v_t_1251_, v_p_1252_);
stack->m_num = v_res_1265_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___boxed(lean_object* v_t_1266_, lean_object* v_p_1267_){
_start:
{
uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l_Std_TreeSet_any___redArg(v_t_1266_, v_p_1267_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
uint8_t l_Std_TreeSet_any(lean_object* v_00_u03b1_1270_, lean_object* v_cmp_1271_, lean_object* v_t_1272_, lean_object* v_p_1273_){
_start:
{
lean_object* v___y_1275_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; lean_object* v_a_1285_; 
v___x_1280_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1281_ = lean_box(0);
v___x_1282_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1283_ = lean_alloc_closure((void*)(l_Std_TreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1283_, 0, v_p_1273_);
lean_closure_set(v___f_1283_, 1, v___x_1282_);
lean_closure_set(v___f_1283_, 2, v___x_1281_);
v___x_1284_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1280_, v___f_1283_, v___x_1282_, v_t_1272_);
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___y_1275_ = v_a_1285_;
goto v___jp_1274_;
v___jp_1274_:
{
lean_object* v_fst_1276_; 
v_fst_1276_ = lean_ctor_get(v___y_1275_, 0);
lean_inc(v_fst_1276_);
lean_dec_ref(v___y_1275_);
if (lean_obj_tag(v_fst_1276_) == 0)
{
uint8_t v___x_1277_; 
v___x_1277_ = 0;
return v___x_1277_;
}
else
{
lean_object* v_val_1278_; uint8_t v___x_1279_; 
v_val_1278_ = lean_ctor_get(v_fst_1276_, 0);
lean_inc(v_val_1278_);
lean_dec_ref_known(v_fst_1276_, 1);
v___x_1279_ = lean_unbox(v_val_1278_);
lean_dec(v_val_1278_);
return v___x_1279_;
}
}
}
}
LEAN_EXPORT void l_Std_TreeSet_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1271_ = stack[1].m_obj;
lean_object* v_t_1272_ = stack[2].m_obj;
lean_object* v_p_1273_ = stack[3].m_obj;
uint8_t v_res_1286_;
v_res_1286_ = l_Std_TreeSet_any(lean_box(0), v_cmp_1271_, v_t_1272_, v_p_1273_);
stack->m_num = v_res_1286_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___boxed(lean_object* v_00_u03b1_1287_, lean_object* v_cmp_1288_, lean_object* v_t_1289_, lean_object* v_p_1290_){
_start:
{
uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_res_1291_ = l_Std_TreeSet_any(v_00_u03b1_1287_, v_cmp_1288_, v_t_1289_, v_p_1290_);
lean_dec_ref(v_cmp_1288_);
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0(lean_object* v_p_1293_, lean_object* v___x_1294_, lean_object* v___x_1295_, lean_object* v_a_1296_, lean_object* v_b_1297_, lean_object* v_acc_1298_){
_start:
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = lean_apply_1(v_p_1293_, v_a_1296_);
v___x_1300_ = lean_unbox(v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec_ref(v___x_1295_);
v___x_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1294_);
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1295_);
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0___boxed(lean_object* v_p_1305_, lean_object* v___x_1306_, lean_object* v___x_1307_, lean_object* v_a_1308_, lean_object* v_b_1309_, lean_object* v_acc_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Std_TreeSet_all___redArg___lam__0(v_p_1305_, v___x_1306_, v___x_1307_, v_a_1308_, v_b_1309_, v_acc_1310_);
lean_dec_ref(v_acc_1310_);
return v_res_1311_;
}
}
uint8_t l_Std_TreeSet_all___redArg(lean_object* v_t_1312_, lean_object* v_p_1313_){
_start:
{
lean_object* v___y_1315_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___f_1323_; lean_object* v___x_1324_; lean_object* v_a_1325_; 
v___x_1320_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1321_ = lean_box(0);
v___x_1322_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1323_ = lean_alloc_closure((void*)(l_Std_TreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1323_, 0, v_p_1313_);
lean_closure_set(v___f_1323_, 1, v___x_1321_);
lean_closure_set(v___f_1323_, 2, v___x_1322_);
v___x_1324_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1320_, v___f_1323_, v___x_1322_, v_t_1312_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___y_1315_ = v_a_1325_;
goto v___jp_1314_;
v___jp_1314_:
{
lean_object* v_fst_1316_; 
v_fst_1316_ = lean_ctor_get(v___y_1315_, 0);
lean_inc(v_fst_1316_);
lean_dec_ref(v___y_1315_);
if (lean_obj_tag(v_fst_1316_) == 0)
{
uint8_t v___x_1317_; 
v___x_1317_ = 1;
return v___x_1317_;
}
else
{
lean_object* v_val_1318_; uint8_t v___x_1319_; 
v_val_1318_ = lean_ctor_get(v_fst_1316_, 0);
lean_inc(v_val_1318_);
lean_dec_ref_known(v_fst_1316_, 1);
v___x_1319_ = lean_unbox(v_val_1318_);
lean_dec(v_val_1318_);
return v___x_1319_;
}
}
}
}
LEAN_EXPORT void l_Std_TreeSet_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1312_ = stack[0].m_obj;
lean_object* v_p_1313_ = stack[1].m_obj;
uint8_t v_res_1326_;
v_res_1326_ = l_Std_TreeSet_all___redArg(v_t_1312_, v_p_1313_);
stack->m_num = v_res_1326_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___boxed(lean_object* v_t_1327_, lean_object* v_p_1328_){
_start:
{
uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_res_1329_ = l_Std_TreeSet_all___redArg(v_t_1327_, v_p_1328_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
uint8_t l_Std_TreeSet_all(lean_object* v_00_u03b1_1331_, lean_object* v_cmp_1332_, lean_object* v_t_1333_, lean_object* v_p_1334_){
_start:
{
lean_object* v___y_1336_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; lean_object* v_a_1346_; 
v___x_1341_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1342_ = lean_box(0);
v___x_1343_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1344_ = lean_alloc_closure((void*)(l_Std_TreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1344_, 0, v_p_1334_);
lean_closure_set(v___f_1344_, 1, v___x_1342_);
lean_closure_set(v___f_1344_, 2, v___x_1343_);
v___x_1345_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1341_, v___f_1344_, v___x_1343_, v_t_1333_);
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___y_1336_ = v_a_1346_;
goto v___jp_1335_;
v___jp_1335_:
{
lean_object* v_fst_1337_; 
v_fst_1337_ = lean_ctor_get(v___y_1336_, 0);
lean_inc(v_fst_1337_);
lean_dec_ref(v___y_1336_);
if (lean_obj_tag(v_fst_1337_) == 0)
{
uint8_t v___x_1338_; 
v___x_1338_ = 1;
return v___x_1338_;
}
else
{
lean_object* v_val_1339_; uint8_t v___x_1340_; 
v_val_1339_ = lean_ctor_get(v_fst_1337_, 0);
lean_inc(v_val_1339_);
lean_dec_ref_known(v_fst_1337_, 1);
v___x_1340_ = lean_unbox(v_val_1339_);
lean_dec(v_val_1339_);
return v___x_1340_;
}
}
}
}
LEAN_EXPORT void l_Std_TreeSet_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1332_ = stack[1].m_obj;
lean_object* v_t_1333_ = stack[2].m_obj;
lean_object* v_p_1334_ = stack[3].m_obj;
uint8_t v_res_1347_;
v_res_1347_ = l_Std_TreeSet_all(lean_box(0), v_cmp_1332_, v_t_1333_, v_p_1334_);
stack->m_num = v_res_1347_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___boxed(lean_object* v_00_u03b1_1348_, lean_object* v_cmp_1349_, lean_object* v_t_1350_, lean_object* v_p_1351_){
_start:
{
uint8_t v_res_1352_; lean_object* v_r_1353_; 
v_res_1352_ = l_Std_TreeSet_all(v_00_u03b1_1348_, v_cmp_1349_, v_t_1350_, v_p_1351_);
lean_dec_ref(v_cmp_1349_);
v_r_1353_ = lean_box(v_res_1352_);
return v_r_1353_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg___lam__0(lean_object* v_x1_1354_, lean_object* v_x2_1355_, lean_object* v_x3_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_x1_1354_);
lean_ctor_set(v___x_1357_, 1, v_x3_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg(lean_object* v_t_1359_){
_start:
{
lean_object* v___f_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___f_1360_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___x_1361_ = lean_box(0);
v___x_1362_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1363_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1362_, v___f_1360_, v___x_1361_, v_t_1359_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList(lean_object* v_00_u03b1_1364_, lean_object* v_cmp_1365_, lean_object* v_t_1366_){
_start:
{
lean_object* v___f_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___f_1367_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___x_1368_ = lean_box(0);
v___x_1369_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1370_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1369_, v___f_1367_, v___x_1368_, v_t_1366_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___boxed(lean_object* v_00_u03b1_1371_, lean_object* v_cmp_1372_, lean_object* v_t_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Std_TreeSet_toList(v_00_u03b1_1371_, v_cmp_1372_, v_t_1373_);
lean_dec_ref(v_cmp_1372_);
return v_res_1374_;
}
}
static lean_object* _init_l_Std_TreeSet_ofList___auto__1(void){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__25, &l_Std_TreeSet___auto__1___closed__25_once, _init_l_Std_TreeSet___auto__1___closed__25);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(lean_object* v_cmp_1376_, lean_object* v_k_1377_, lean_object* v_v_1378_, lean_object* v_t_1379_){
_start:
{
if (lean_obj_tag(v_t_1379_) == 0)
{
lean_object* v_size_1380_; lean_object* v_k_1381_; lean_object* v_v_1382_; lean_object* v_l_1383_; lean_object* v_r_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1665_; 
v_size_1380_ = lean_ctor_get(v_t_1379_, 0);
v_k_1381_ = lean_ctor_get(v_t_1379_, 1);
v_v_1382_ = lean_ctor_get(v_t_1379_, 2);
v_l_1383_ = lean_ctor_get(v_t_1379_, 3);
v_r_1384_ = lean_ctor_get(v_t_1379_, 4);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_t_1379_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1386_ = v_t_1379_;
v_isShared_1387_ = v_isSharedCheck_1665_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_r_1384_);
lean_inc(v_l_1383_);
lean_inc(v_v_1382_);
lean_inc(v_k_1381_);
lean_inc(v_size_1380_);
lean_dec(v_t_1379_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1665_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; uint8_t v___x_1389_; 
lean_inc_ref(v_cmp_1376_);
lean_inc(v_k_1381_);
lean_inc(v_k_1377_);
v___x_1388_ = lean_apply_2(v_cmp_1376_, v_k_1377_, v_k_1381_);
v___x_1389_ = lean_unbox(v___x_1388_);
switch(v___x_1389_)
{
case 0:
{
lean_object* v_impl_1390_; lean_object* v___x_1391_; 
lean_dec(v_size_1380_);
v_impl_1390_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1376_, v_k_1377_, v_v_1378_, v_l_1383_);
v___x_1391_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1384_) == 0)
{
lean_object* v_size_1392_; lean_object* v_size_1393_; lean_object* v_k_1394_; lean_object* v_v_1395_; lean_object* v_l_1396_; lean_object* v_r_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_size_1392_ = lean_ctor_get(v_r_1384_, 0);
v_size_1393_ = lean_ctor_get(v_impl_1390_, 0);
v_k_1394_ = lean_ctor_get(v_impl_1390_, 1);
v_v_1395_ = lean_ctor_get(v_impl_1390_, 2);
v_l_1396_ = lean_ctor_get(v_impl_1390_, 3);
v_r_1397_ = lean_ctor_get(v_impl_1390_, 4);
lean_inc(v_r_1397_);
v___x_1398_ = lean_unsigned_to_nat(3u);
v___x_1399_ = lean_nat_mul(v___x_1398_, v_size_1392_);
v___x_1400_ = lean_nat_dec_lt(v___x_1399_, v_size_1393_);
lean_dec(v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_dec(v_r_1397_);
v___x_1401_ = lean_nat_add(v___x_1391_, v_size_1393_);
v___x_1402_ = lean_nat_add(v___x_1401_, v_size_1392_);
lean_dec(v___x_1401_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 3, v_impl_1390_);
lean_ctor_set(v___x_1386_, 0, v___x_1402_);
v___x_1404_ = v___x_1386_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1405_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1405_, 3, v_impl_1390_);
lean_ctor_set(v_reuseFailAlloc_1405_, 4, v_r_1384_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
else
{
lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1471_; 
lean_inc(v_l_1396_);
lean_inc(v_v_1395_);
lean_inc(v_k_1394_);
lean_inc(v_size_1393_);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_impl_1390_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; lean_object* v_unused_1473_; lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; 
v_unused_1472_ = lean_ctor_get(v_impl_1390_, 4);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_impl_1390_, 3);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_impl_1390_, 2);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_impl_1390_, 1);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_impl_1390_, 0);
lean_dec(v_unused_1476_);
v___x_1407_ = v_impl_1390_;
v_isShared_1408_ = v_isSharedCheck_1471_;
goto v_resetjp_1406_;
}
else
{
lean_dec(v_impl_1390_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1471_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_size_1409_; lean_object* v_size_1410_; lean_object* v_k_1411_; lean_object* v_v_1412_; lean_object* v_l_1413_; lean_object* v_r_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v_size_1409_ = lean_ctor_get(v_l_1396_, 0);
v_size_1410_ = lean_ctor_get(v_r_1397_, 0);
v_k_1411_ = lean_ctor_get(v_r_1397_, 1);
v_v_1412_ = lean_ctor_get(v_r_1397_, 2);
v_l_1413_ = lean_ctor_get(v_r_1397_, 3);
v_r_1414_ = lean_ctor_get(v_r_1397_, 4);
v___x_1415_ = lean_unsigned_to_nat(2u);
v___x_1416_ = lean_nat_mul(v___x_1415_, v_size_1409_);
v___x_1417_ = lean_nat_dec_lt(v_size_1410_, v___x_1416_);
lean_dec(v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1446_; 
lean_inc(v_r_1414_);
lean_inc(v_l_1413_);
lean_inc(v_v_1412_);
lean_inc(v_k_1411_);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_r_1397_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; 
v_unused_1447_ = lean_ctor_get(v_r_1397_, 4);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_r_1397_, 3);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_r_1397_, 2);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_r_1397_, 1);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_r_1397_, 0);
lean_dec(v_unused_1451_);
v___x_1419_ = v_r_1397_;
v_isShared_1420_ = v_isSharedCheck_1446_;
goto v_resetjp_1418_;
}
else
{
lean_dec(v_r_1397_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1446_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___x_1434_; lean_object* v___y_1436_; 
v___x_1421_ = lean_nat_add(v___x_1391_, v_size_1393_);
lean_dec(v_size_1393_);
v___x_1422_ = lean_nat_add(v___x_1421_, v_size_1392_);
lean_dec(v___x_1421_);
v___x_1434_ = lean_nat_add(v___x_1391_, v_size_1409_);
if (lean_obj_tag(v_l_1413_) == 0)
{
lean_object* v_size_1444_; 
v_size_1444_ = lean_ctor_get(v_l_1413_, 0);
lean_inc(v_size_1444_);
v___y_1436_ = v_size_1444_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_unsigned_to_nat(0u);
v___y_1436_ = v___x_1445_;
goto v___jp_1435_;
}
v___jp_1423_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = lean_nat_add(v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec(v___y_1425_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 4, v_r_1384_);
lean_ctor_set(v___x_1419_, 3, v_r_1414_);
lean_ctor_set(v___x_1419_, 2, v_v_1382_);
lean_ctor_set(v___x_1419_, 1, v_k_1381_);
lean_ctor_set(v___x_1419_, 0, v___x_1427_);
v___x_1429_ = v___x_1419_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1433_, 3, v_r_1414_);
lean_ctor_set(v_reuseFailAlloc_1433_, 4, v_r_1384_);
v___x_1429_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1431_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 4, v___x_1429_);
lean_ctor_set(v___x_1407_, 3, v___y_1424_);
lean_ctor_set(v___x_1407_, 2, v_v_1412_);
lean_ctor_set(v___x_1407_, 1, v_k_1411_);
lean_ctor_set(v___x_1407_, 0, v___x_1422_);
v___x_1431_ = v___x_1407_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_k_1411_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_v_1412_);
lean_ctor_set(v_reuseFailAlloc_1432_, 3, v___y_1424_);
lean_ctor_set(v_reuseFailAlloc_1432_, 4, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
v___jp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1437_ = lean_nat_add(v___x_1434_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec(v___x_1434_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_l_1413_);
lean_ctor_set(v___x_1386_, 3, v_l_1396_);
lean_ctor_set(v___x_1386_, 2, v_v_1395_);
lean_ctor_set(v___x_1386_, 1, v_k_1394_);
lean_ctor_set(v___x_1386_, 0, v___x_1437_);
v___x_1439_ = v___x_1386_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_k_1394_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_v_1395_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_l_1396_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_l_1413_);
v___x_1439_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_nat_add(v___x_1391_, v_size_1392_);
if (lean_obj_tag(v_r_1414_) == 0)
{
lean_object* v_size_1441_; 
v_size_1441_ = lean_ctor_get(v_r_1414_, 0);
lean_inc(v_size_1441_);
v___y_1424_ = v___x_1439_;
v___y_1425_ = v___x_1440_;
v___y_1426_ = v_size_1441_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_unsigned_to_nat(0u);
v___y_1424_ = v___x_1439_;
v___y_1425_ = v___x_1440_;
v___y_1426_ = v___x_1442_;
goto v___jp_1423_;
}
}
}
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
lean_del_object(v___x_1386_);
v___x_1452_ = lean_nat_add(v___x_1391_, v_size_1393_);
lean_dec(v_size_1393_);
v___x_1453_ = lean_nat_add(v___x_1452_, v_size_1392_);
lean_dec(v___x_1452_);
v___x_1454_ = lean_nat_add(v___x_1391_, v_size_1392_);
v___x_1455_ = lean_nat_add(v___x_1454_, v_size_1410_);
lean_dec(v___x_1454_);
lean_inc_ref(v_r_1384_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 4, v_r_1384_);
lean_ctor_set(v___x_1407_, 3, v_r_1397_);
lean_ctor_set(v___x_1407_, 2, v_v_1382_);
lean_ctor_set(v___x_1407_, 1, v_k_1381_);
lean_ctor_set(v___x_1407_, 0, v___x_1455_);
v___x_1457_ = v___x_1407_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1470_, 3, v_r_1397_);
lean_ctor_set(v_reuseFailAlloc_1470_, 4, v_r_1384_);
v___x_1457_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_isSharedCheck_1464_ = !lean_is_exclusive(v_r_1384_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; 
v_unused_1465_ = lean_ctor_get(v_r_1384_, 4);
lean_dec(v_unused_1465_);
v_unused_1466_ = lean_ctor_get(v_r_1384_, 3);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_r_1384_, 2);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_r_1384_, 1);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_r_1384_, 0);
lean_dec(v_unused_1469_);
v___x_1459_ = v_r_1384_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v_r_1384_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v___x_1457_);
lean_ctor_set(v___x_1459_, 3, v_l_1396_);
lean_ctor_set(v___x_1459_, 2, v_v_1395_);
lean_ctor_set(v___x_1459_, 1, v_k_1394_);
lean_ctor_set(v___x_1459_, 0, v___x_1453_);
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_k_1394_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_v_1395_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v_l_1396_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v___x_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1477_; 
v_l_1477_ = lean_ctor_get(v_impl_1390_, 3);
if (lean_obj_tag(v_l_1477_) == 0)
{
lean_object* v_r_1478_; lean_object* v_k_1479_; lean_object* v_v_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1491_; 
lean_inc_ref(v_l_1477_);
v_r_1478_ = lean_ctor_get(v_impl_1390_, 4);
v_k_1479_ = lean_ctor_get(v_impl_1390_, 1);
v_v_1480_ = lean_ctor_get(v_impl_1390_, 2);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_impl_1390_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; lean_object* v_unused_1493_; 
v_unused_1492_ = lean_ctor_get(v_impl_1390_, 3);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_impl_1390_, 0);
lean_dec(v_unused_1493_);
v___x_1482_ = v_impl_1390_;
v_isShared_1483_ = v_isSharedCheck_1491_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_r_1478_);
lean_inc(v_v_1480_);
lean_inc(v_k_1479_);
lean_dec(v_impl_1390_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1491_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1478_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 3, v_r_1478_);
lean_ctor_set(v___x_1482_, 2, v_v_1382_);
lean_ctor_set(v___x_1482_, 1, v_k_1381_);
lean_ctor_set(v___x_1482_, 0, v___x_1391_);
v___x_1486_ = v___x_1482_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_r_1478_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_r_1478_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1488_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v___x_1486_);
lean_ctor_set(v___x_1386_, 3, v_l_1477_);
lean_ctor_set(v___x_1386_, 2, v_v_1480_);
lean_ctor_set(v___x_1386_, 1, v_k_1479_);
lean_ctor_set(v___x_1386_, 0, v___x_1484_);
v___x_1488_ = v___x_1386_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_l_1477_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_object* v_r_1494_; 
v_r_1494_ = lean_ctor_get(v_impl_1390_, 4);
lean_inc(v_r_1494_);
if (lean_obj_tag(v_r_1494_) == 0)
{
lean_object* v_k_1495_; lean_object* v_v_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1519_; 
lean_inc(v_l_1477_);
v_k_1495_ = lean_ctor_get(v_impl_1390_, 1);
v_v_1496_ = lean_ctor_get(v_impl_1390_, 2);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_impl_1390_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; lean_object* v_unused_1521_; lean_object* v_unused_1522_; 
v_unused_1520_ = lean_ctor_get(v_impl_1390_, 4);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_impl_1390_, 3);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_impl_1390_, 0);
lean_dec(v_unused_1522_);
v___x_1498_ = v_impl_1390_;
v_isShared_1499_ = v_isSharedCheck_1519_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_v_1496_);
lean_inc(v_k_1495_);
lean_dec(v_impl_1390_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1519_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_k_1500_; lean_object* v_v_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1515_; 
v_k_1500_ = lean_ctor_get(v_r_1494_, 1);
v_v_1501_ = lean_ctor_get(v_r_1494_, 2);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_r_1494_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; 
v_unused_1516_ = lean_ctor_get(v_r_1494_, 4);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_r_1494_, 3);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_r_1494_, 0);
lean_dec(v_unused_1518_);
v___x_1503_ = v_r_1494_;
v_isShared_1504_ = v_isSharedCheck_1515_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_v_1501_);
lean_inc(v_k_1500_);
lean_dec(v_r_1494_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1515_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_unsigned_to_nat(3u);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v_l_1477_);
lean_ctor_set(v___x_1503_, 3, v_l_1477_);
lean_ctor_set(v___x_1503_, 2, v_v_1496_);
lean_ctor_set(v___x_1503_, 1, v_k_1495_);
lean_ctor_set(v___x_1503_, 0, v___x_1391_);
v___x_1507_ = v___x_1503_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_k_1495_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1496_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_l_1477_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_l_1477_);
v___x_1507_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 4, v_l_1477_);
lean_ctor_set(v___x_1498_, 2, v_v_1382_);
lean_ctor_set(v___x_1498_, 1, v_k_1381_);
lean_ctor_set(v___x_1498_, 0, v___x_1391_);
v___x_1509_ = v___x_1498_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v_l_1477_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v_l_1477_);
v___x_1509_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1511_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v___x_1509_);
lean_ctor_set(v___x_1386_, 3, v___x_1507_);
lean_ctor_set(v___x_1386_, 2, v_v_1501_);
lean_ctor_set(v___x_1386_, 1, v_k_1500_);
lean_ctor_set(v___x_1386_, 0, v___x_1505_);
v___x_1511_ = v___x_1386_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_k_1500_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_v_1501_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_unsigned_to_nat(2u);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_r_1494_);
lean_ctor_set(v___x_1386_, 3, v_impl_1390_);
lean_ctor_set(v___x_1386_, 0, v___x_1523_);
v___x_1525_ = v___x_1386_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_impl_1390_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_r_1494_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1528_; 
lean_dec(v_v_1382_);
lean_dec(v_k_1381_);
lean_dec_ref(v_cmp_1376_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 2, v_v_1378_);
lean_ctor_set(v___x_1386_, 1, v_k_1377_);
v___x_1528_ = v___x_1386_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_size_1380_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1377_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1378_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_l_1383_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_r_1384_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
default: 
{
lean_object* v_impl_1530_; lean_object* v___x_1531_; 
lean_dec(v_size_1380_);
v_impl_1530_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1376_, v_k_1377_, v_v_1378_, v_r_1384_);
v___x_1531_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1383_) == 0)
{
lean_object* v_size_1532_; lean_object* v_size_1533_; lean_object* v_k_1534_; lean_object* v_v_1535_; lean_object* v_l_1536_; lean_object* v_r_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v_size_1532_ = lean_ctor_get(v_l_1383_, 0);
v_size_1533_ = lean_ctor_get(v_impl_1530_, 0);
v_k_1534_ = lean_ctor_get(v_impl_1530_, 1);
v_v_1535_ = lean_ctor_get(v_impl_1530_, 2);
v_l_1536_ = lean_ctor_get(v_impl_1530_, 3);
lean_inc(v_l_1536_);
v_r_1537_ = lean_ctor_get(v_impl_1530_, 4);
v___x_1538_ = lean_unsigned_to_nat(3u);
v___x_1539_ = lean_nat_mul(v___x_1538_, v_size_1532_);
v___x_1540_ = lean_nat_dec_lt(v___x_1539_, v_size_1533_);
lean_dec(v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
lean_dec(v_l_1536_);
v___x_1541_ = lean_nat_add(v___x_1531_, v_size_1532_);
v___x_1542_ = lean_nat_add(v___x_1541_, v_size_1533_);
lean_dec(v___x_1541_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_impl_1530_);
lean_ctor_set(v___x_1386_, 0, v___x_1542_);
v___x_1544_ = v___x_1386_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_l_1383_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_impl_1530_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
else
{
lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1609_; 
lean_inc(v_r_1537_);
lean_inc(v_v_1535_);
lean_inc(v_k_1534_);
lean_inc(v_size_1533_);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_impl_1530_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; lean_object* v_unused_1613_; lean_object* v_unused_1614_; 
v_unused_1610_ = lean_ctor_get(v_impl_1530_, 4);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_impl_1530_, 3);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_impl_1530_, 2);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_impl_1530_, 1);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_impl_1530_, 0);
lean_dec(v_unused_1614_);
v___x_1547_ = v_impl_1530_;
v_isShared_1548_ = v_isSharedCheck_1609_;
goto v_resetjp_1546_;
}
else
{
lean_dec(v_impl_1530_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1609_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v_size_1549_; lean_object* v_k_1550_; lean_object* v_v_1551_; lean_object* v_l_1552_; lean_object* v_r_1553_; lean_object* v_size_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v_size_1549_ = lean_ctor_get(v_l_1536_, 0);
v_k_1550_ = lean_ctor_get(v_l_1536_, 1);
v_v_1551_ = lean_ctor_get(v_l_1536_, 2);
v_l_1552_ = lean_ctor_get(v_l_1536_, 3);
v_r_1553_ = lean_ctor_get(v_l_1536_, 4);
v_size_1554_ = lean_ctor_get(v_r_1537_, 0);
v___x_1555_ = lean_unsigned_to_nat(2u);
v___x_1556_ = lean_nat_mul(v___x_1555_, v_size_1554_);
v___x_1557_ = lean_nat_dec_lt(v_size_1549_, v___x_1556_);
lean_dec(v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1585_; 
lean_inc(v_r_1553_);
lean_inc(v_l_1552_);
lean_inc(v_v_1551_);
lean_inc(v_k_1550_);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_l_1536_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; lean_object* v_unused_1587_; lean_object* v_unused_1588_; lean_object* v_unused_1589_; lean_object* v_unused_1590_; 
v_unused_1586_ = lean_ctor_get(v_l_1536_, 4);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v_l_1536_, 3);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_l_1536_, 2);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_l_1536_, 1);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_l_1536_, 0);
lean_dec(v_unused_1590_);
v___x_1559_ = v_l_1536_;
v_isShared_1560_ = v_isSharedCheck_1585_;
goto v_resetjp_1558_;
}
else
{
lean_dec(v_l_1536_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1585_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1575_; 
v___x_1561_ = lean_nat_add(v___x_1531_, v_size_1532_);
v___x_1562_ = lean_nat_add(v___x_1561_, v_size_1533_);
lean_dec(v_size_1533_);
if (lean_obj_tag(v_l_1552_) == 0)
{
lean_object* v_size_1583_; 
v_size_1583_ = lean_ctor_get(v_l_1552_, 0);
lean_inc(v_size_1583_);
v___y_1575_ = v_size_1583_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_unsigned_to_nat(0u);
v___y_1575_ = v___x_1584_;
goto v___jp_1574_;
}
v___jp_1563_:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = lean_nat_add(v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec(v___y_1565_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 4, v_r_1537_);
lean_ctor_set(v___x_1559_, 3, v_r_1553_);
lean_ctor_set(v___x_1559_, 2, v_v_1535_);
lean_ctor_set(v___x_1559_, 1, v_k_1534_);
lean_ctor_set(v___x_1559_, 0, v___x_1567_);
v___x_1569_ = v___x_1559_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_k_1534_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_v_1535_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v_r_1553_);
lean_ctor_set(v_reuseFailAlloc_1573_, 4, v_r_1537_);
v___x_1569_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1571_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 4, v___x_1569_);
lean_ctor_set(v___x_1547_, 3, v___y_1564_);
lean_ctor_set(v___x_1547_, 2, v_v_1551_);
lean_ctor_set(v___x_1547_, 1, v_k_1550_);
lean_ctor_set(v___x_1547_, 0, v___x_1562_);
v___x_1571_ = v___x_1547_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_k_1550_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_v_1551_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v___y_1564_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
v___jp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = lean_nat_add(v___x_1561_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec(v___x_1561_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_l_1552_);
lean_ctor_set(v___x_1386_, 0, v___x_1576_);
v___x_1578_ = v___x_1386_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v_l_1383_);
lean_ctor_set(v_reuseFailAlloc_1582_, 4, v_l_1552_);
v___x_1578_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_nat_add(v___x_1531_, v_size_1554_);
if (lean_obj_tag(v_r_1553_) == 0)
{
lean_object* v_size_1580_; 
v_size_1580_ = lean_ctor_get(v_r_1553_, 0);
lean_inc(v_size_1580_);
v___y_1564_ = v___x_1578_;
v___y_1565_ = v___x_1579_;
v___y_1566_ = v_size_1580_;
goto v___jp_1563_;
}
else
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_unsigned_to_nat(0u);
v___y_1564_ = v___x_1578_;
v___y_1565_ = v___x_1579_;
v___y_1566_ = v___x_1581_;
goto v___jp_1563_;
}
}
}
}
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_del_object(v___x_1386_);
v___x_1591_ = lean_nat_add(v___x_1531_, v_size_1532_);
v___x_1592_ = lean_nat_add(v___x_1591_, v_size_1533_);
lean_dec(v_size_1533_);
v___x_1593_ = lean_nat_add(v___x_1591_, v_size_1549_);
lean_dec(v___x_1591_);
lean_inc_ref(v_l_1383_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 4, v_l_1536_);
lean_ctor_set(v___x_1547_, 3, v_l_1383_);
lean_ctor_set(v___x_1547_, 2, v_v_1382_);
lean_ctor_set(v___x_1547_, 1, v_k_1381_);
lean_ctor_set(v___x_1547_, 0, v___x_1593_);
v___x_1595_ = v___x_1547_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v_l_1383_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v_l_1536_);
v___x_1595_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
v_isSharedCheck_1602_ = !lean_is_exclusive(v_l_1383_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; 
v_unused_1603_ = lean_ctor_get(v_l_1383_, 4);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_l_1383_, 3);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_l_1383_, 2);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_l_1383_, 1);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_l_1383_, 0);
lean_dec(v_unused_1607_);
v___x_1597_ = v_l_1383_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_dec(v_l_1383_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 4, v_r_1537_);
lean_ctor_set(v___x_1597_, 3, v___x_1595_);
lean_ctor_set(v___x_1597_, 2, v_v_1535_);
lean_ctor_set(v___x_1597_, 1, v_k_1534_);
lean_ctor_set(v___x_1597_, 0, v___x_1592_);
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1534_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1535_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_r_1537_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1615_; 
v_l_1615_ = lean_ctor_get(v_impl_1530_, 3);
lean_inc(v_l_1615_);
if (lean_obj_tag(v_l_1615_) == 0)
{
lean_object* v_r_1616_; lean_object* v_k_1617_; lean_object* v_v_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1641_; 
v_r_1616_ = lean_ctor_get(v_impl_1530_, 4);
v_k_1617_ = lean_ctor_get(v_impl_1530_, 1);
v_v_1618_ = lean_ctor_get(v_impl_1530_, 2);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_impl_1530_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; lean_object* v_unused_1643_; 
v_unused_1642_ = lean_ctor_get(v_impl_1530_, 3);
lean_dec(v_unused_1642_);
v_unused_1643_ = lean_ctor_get(v_impl_1530_, 0);
lean_dec(v_unused_1643_);
v___x_1620_ = v_impl_1530_;
v_isShared_1621_ = v_isSharedCheck_1641_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_r_1616_);
lean_inc(v_v_1618_);
lean_inc(v_k_1617_);
lean_dec(v_impl_1530_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1641_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_k_1622_; lean_object* v_v_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1637_; 
v_k_1622_ = lean_ctor_get(v_l_1615_, 1);
v_v_1623_ = lean_ctor_get(v_l_1615_, 2);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_l_1615_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; lean_object* v_unused_1639_; lean_object* v_unused_1640_; 
v_unused_1638_ = lean_ctor_get(v_l_1615_, 4);
lean_dec(v_unused_1638_);
v_unused_1639_ = lean_ctor_get(v_l_1615_, 3);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_l_1615_, 0);
lean_dec(v_unused_1640_);
v___x_1625_ = v_l_1615_;
v_isShared_1626_ = v_isSharedCheck_1637_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_v_1623_);
lean_inc(v_k_1622_);
lean_dec(v_l_1615_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1637_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1616_, 2);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 4, v_r_1616_);
lean_ctor_set(v___x_1625_, 3, v_r_1616_);
lean_ctor_set(v___x_1625_, 2, v_v_1382_);
lean_ctor_set(v___x_1625_, 1, v_k_1381_);
lean_ctor_set(v___x_1625_, 0, v___x_1531_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_r_1616_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v_r_1616_);
v___x_1629_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1631_; 
lean_inc(v_r_1616_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 3, v_r_1616_);
lean_ctor_set(v___x_1620_, 0, v___x_1531_);
v___x_1631_ = v___x_1620_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_k_1617_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_v_1618_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v_r_1616_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v_r_1616_);
v___x_1631_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1633_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v___x_1631_);
lean_ctor_set(v___x_1386_, 3, v___x_1629_);
lean_ctor_set(v___x_1386_, 2, v_v_1623_);
lean_ctor_set(v___x_1386_, 1, v_k_1622_);
lean_ctor_set(v___x_1386_, 0, v___x_1627_);
v___x_1633_ = v___x_1386_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_k_1622_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_v_1623_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1634_, 4, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
}
else
{
lean_object* v_r_1644_; 
v_r_1644_ = lean_ctor_get(v_impl_1530_, 4);
lean_inc(v_r_1644_);
if (lean_obj_tag(v_r_1644_) == 0)
{
lean_object* v_k_1645_; lean_object* v_v_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1657_; 
v_k_1645_ = lean_ctor_get(v_impl_1530_, 1);
v_v_1646_ = lean_ctor_get(v_impl_1530_, 2);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_impl_1530_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; lean_object* v_unused_1659_; lean_object* v_unused_1660_; 
v_unused_1658_ = lean_ctor_get(v_impl_1530_, 4);
lean_dec(v_unused_1658_);
v_unused_1659_ = lean_ctor_get(v_impl_1530_, 3);
lean_dec(v_unused_1659_);
v_unused_1660_ = lean_ctor_get(v_impl_1530_, 0);
lean_dec(v_unused_1660_);
v___x_1648_ = v_impl_1530_;
v_isShared_1649_ = v_isSharedCheck_1657_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_v_1646_);
lean_inc(v_k_1645_);
lean_dec(v_impl_1530_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1657_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_unsigned_to_nat(3u);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 4, v_l_1615_);
lean_ctor_set(v___x_1648_, 2, v_v_1382_);
lean_ctor_set(v___x_1648_, 1, v_k_1381_);
lean_ctor_set(v___x_1648_, 0, v___x_1531_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_l_1615_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v_l_1615_);
v___x_1652_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1654_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_r_1644_);
lean_ctor_set(v___x_1386_, 3, v___x_1652_);
lean_ctor_set(v___x_1386_, 2, v_v_1646_);
lean_ctor_set(v___x_1386_, 1, v_k_1645_);
lean_ctor_set(v___x_1386_, 0, v___x_1650_);
v___x_1654_ = v___x_1386_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_k_1645_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_v_1646_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_r_1644_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_unsigned_to_nat(2u);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_impl_1530_);
lean_ctor_set(v___x_1386_, 3, v_r_1644_);
lean_ctor_set(v___x_1386_, 0, v___x_1661_);
v___x_1663_ = v___x_1386_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_r_1644_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_impl_1530_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
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
lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec_ref(v_cmp_1376_);
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_k_1377_);
lean_ctor_set(v___x_1667_, 2, v_v_1378_);
lean_ctor_set(v___x_1667_, 3, v_t_1379_);
lean_ctor_set(v___x_1667_, 4, v_t_1379_);
return v___x_1667_;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(lean_object* v_cmp_1668_, lean_object* v_k_1669_, lean_object* v_t_1670_){
_start:
{
if (lean_obj_tag(v_t_1670_) == 0)
{
lean_object* v_k_1671_; lean_object* v_l_1672_; lean_object* v_r_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v_k_1671_ = lean_ctor_get(v_t_1670_, 1);
lean_inc(v_k_1671_);
v_l_1672_ = lean_ctor_get(v_t_1670_, 3);
lean_inc(v_l_1672_);
v_r_1673_ = lean_ctor_get(v_t_1670_, 4);
lean_inc(v_r_1673_);
lean_dec_ref_known(v_t_1670_, 5);
lean_inc_ref(v_cmp_1668_);
lean_inc(v_k_1669_);
v___x_1674_ = lean_apply_2(v_cmp_1668_, v_k_1669_, v_k_1671_);
v___x_1675_ = lean_unbox(v___x_1674_);
switch(v___x_1675_)
{
case 0:
{
lean_dec(v_r_1673_);
v_t_1670_ = v_l_1672_;
goto _start;
}
case 1:
{
uint8_t v___x_1677_; 
lean_dec(v_r_1673_);
lean_dec(v_l_1672_);
lean_dec(v_k_1669_);
lean_dec_ref(v_cmp_1668_);
v___x_1677_ = 1;
return v___x_1677_;
}
default: 
{
lean_dec(v_l_1672_);
v_t_1670_ = v_r_1673_;
goto _start;
}
}
}
else
{
uint8_t v___x_1679_; 
lean_dec(v_k_1669_);
lean_dec_ref(v_cmp_1668_);
v___x_1679_ = 0;
return v___x_1679_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1668_ = stack[0].m_obj;
lean_object* v_k_1669_ = stack[1].m_obj;
lean_object* v_t_1670_ = stack[2].m_obj;
uint8_t v_res_1680_;
v_res_1680_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1668_, v_k_1669_, v_t_1670_);
stack->m_num = v_res_1680_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg___boxed(lean_object* v_cmp_1681_, lean_object* v_k_1682_, lean_object* v_t_1683_){
_start:
{
uint8_t v_res_1684_; lean_object* v_r_1685_; 
v_res_1684_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1681_, v_k_1682_, v_t_1683_);
v_r_1685_ = lean_box(v_res_1684_);
return v_r_1685_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(lean_object* v_cmp_1686_, lean_object* v_as_x27_1687_, lean_object* v_b_1688_){
_start:
{
if (lean_obj_tag(v_as_x27_1687_) == 0)
{
lean_dec_ref(v_cmp_1686_);
return v_b_1688_;
}
else
{
lean_object* v_head_1689_; lean_object* v_tail_1690_; uint8_t v___x_1691_; 
v_head_1689_ = lean_ctor_get(v_as_x27_1687_, 0);
v_tail_1690_ = lean_ctor_get(v_as_x27_1687_, 1);
lean_inc(v_b_1688_);
lean_inc(v_head_1689_);
lean_inc_ref(v_cmp_1686_);
v___x_1691_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1686_, v_head_1689_, v_b_1688_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_box(0);
lean_inc(v_head_1689_);
lean_inc_ref(v_cmp_1686_);
v___x_1693_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1686_, v_head_1689_, v___x_1692_, v_b_1688_);
v_as_x27_1687_ = v_tail_1690_;
v_b_1688_ = v___x_1693_;
goto _start;
}
else
{
v_as_x27_1687_ = v_tail_1690_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg___boxed(lean_object* v_cmp_1696_, lean_object* v_as_x27_1697_, lean_object* v_b_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1696_, v_as_x27_1697_, v_b_1698_);
lean_dec(v_as_x27_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___redArg(lean_object* v_l_1700_, lean_object* v_cmp_1701_){
_start:
{
lean_object* v_r_1702_; lean_object* v___x_1703_; 
v_r_1702_ = lean_box(1);
v___x_1703_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1701_, v_l_1700_, v_r_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___redArg___boxed(lean_object* v_l_1704_, lean_object* v_cmp_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Std_TreeSet_ofList___redArg(v_l_1704_, v_cmp_1705_);
lean_dec(v_l_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList(lean_object* v_00_u03b1_1707_, lean_object* v_l_1708_, lean_object* v_cmp_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Std_TreeSet_ofList___redArg(v_l_1708_, v_cmp_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___boxed(lean_object* v_00_u03b1_1711_, lean_object* v_l_1712_, lean_object* v_cmp_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Std_TreeSet_ofList(v_00_u03b1_1711_, v_l_1712_, v_cmp_1713_);
lean_dec(v_l_1712_);
return v_res_1714_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(lean_object* v_00_u03b1_1715_, lean_object* v_cmp_1716_, lean_object* v_00_u03b2_1717_, lean_object* v_k_1718_, lean_object* v_t_1719_){
_start:
{
uint8_t v___x_1720_; 
v___x_1720_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1716_, v_k_1718_, v_t_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1716_ = stack[1].m_obj;
lean_object* v_k_1718_ = stack[3].m_obj;
lean_object* v_t_1719_ = stack[4].m_obj;
uint8_t v_res_1721_;
v_res_1721_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(lean_box(0), v_cmp_1716_, lean_box(0), v_k_1718_, v_t_1719_);
stack->m_num = v_res_1721_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_cmp_1723_, lean_object* v_00_u03b2_1724_, lean_object* v_k_1725_, lean_object* v_t_1726_){
_start:
{
uint8_t v_res_1727_; lean_object* v_r_1728_; 
v_res_1727_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(v_00_u03b1_1722_, v_cmp_1723_, v_00_u03b2_1724_, v_k_1725_, v_t_1726_);
v_r_1728_ = lean_box(v_res_1727_);
return v_r_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1(lean_object* v_00_u03b1_1729_, lean_object* v_cmp_1730_, lean_object* v_00_u03b2_1731_, lean_object* v_k_1732_, lean_object* v_v_1733_, lean_object* v_t_1734_, lean_object* v_hl_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1730_, v_k_1732_, v_v_1733_, v_t_1734_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(lean_object* v_00_u03b1_1737_, lean_object* v_cmp_1738_, lean_object* v_as_1739_, lean_object* v_as_x27_1740_, lean_object* v_b_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1738_, v_as_x27_1740_, v_b_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___boxed(lean_object* v_00_u03b1_1744_, lean_object* v_cmp_1745_, lean_object* v_as_1746_, lean_object* v_as_x27_1747_, lean_object* v_b_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(v_00_u03b1_1744_, v_cmp_1745_, v_as_1746_, v_as_x27_1747_, v_b_1748_, v_a_1749_);
lean_dec(v_as_x27_1747_);
lean_dec(v_as_1746_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg___lam__0(lean_object* v_l_1751_, lean_object* v_k_1752_, lean_object* v_x_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_array_push(v_l_1751_, v_k_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg(lean_object* v_t_1756_){
_start:
{
lean_object* v___f_1757_; lean_object* v___y_1759_; 
v___f_1757_ = ((lean_object*)(l_Std_TreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1756_) == 0)
{
lean_object* v_size_1762_; 
v_size_1762_ = lean_ctor_get(v_t_1756_, 0);
lean_inc(v_size_1762_);
v___y_1759_ = v_size_1762_;
goto v___jp_1758_;
}
else
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_unsigned_to_nat(0u);
v___y_1759_ = v___x_1763_;
goto v___jp_1758_;
}
v___jp_1758_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_mk_empty_array_with_capacity(v___y_1759_);
lean_dec(v___y_1759_);
v___x_1761_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1757_, v___x_1760_, v_t_1756_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray(lean_object* v_00_u03b1_1764_, lean_object* v_cmp_1765_, lean_object* v_t_1766_){
_start:
{
lean_object* v___f_1767_; lean_object* v___y_1769_; 
v___f_1767_ = ((lean_object*)(l_Std_TreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1766_) == 0)
{
lean_object* v_size_1772_; 
v_size_1772_ = lean_ctor_get(v_t_1766_, 0);
lean_inc(v_size_1772_);
v___y_1769_ = v_size_1772_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_unsigned_to_nat(0u);
v___y_1769_ = v___x_1773_;
goto v___jp_1768_;
}
v___jp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_mk_empty_array_with_capacity(v___y_1769_);
lean_dec(v___y_1769_);
v___x_1771_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1767_, v___x_1770_, v_t_1766_);
return v___x_1771_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_cmp_1775_, lean_object* v_t_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Std_TreeSet_toArray(v_00_u03b1_1774_, v_cmp_1775_, v_t_1776_);
lean_dec_ref(v_cmp_1775_);
return v_res_1777_;
}
}
static lean_object* _init_l_Std_TreeSet_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__25, &l_Std_TreeSet___auto__1___closed__25_once, _init_l_Std_TreeSet___auto__1___closed__25);
return v___x_1778_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(lean_object* v_cmp_1779_, lean_object* v_as_1780_, size_t v_sz_1781_, size_t v_i_1782_, lean_object* v_b_1783_){
_start:
{
lean_object* v___y_1785_; uint8_t v___x_1789_; 
v___x_1789_ = lean_usize_dec_lt(v_i_1782_, v_sz_1781_);
if (v___x_1789_ == 0)
{
lean_dec_ref(v_cmp_1779_);
return v_b_1783_;
}
else
{
lean_object* v_a_1790_; uint8_t v___x_1791_; 
v_a_1790_ = lean_array_uget_borrowed(v_as_1780_, v_i_1782_);
lean_inc(v_b_1783_);
lean_inc(v_a_1790_);
lean_inc_ref(v_cmp_1779_);
v___x_1791_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1779_, v_a_1790_, v_b_1783_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_box(0);
lean_inc(v_a_1790_);
lean_inc_ref(v_cmp_1779_);
v___x_1793_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1779_, v_a_1790_, v___x_1792_, v_b_1783_);
v___y_1785_ = v___x_1793_;
goto v___jp_1784_;
}
else
{
v___y_1785_ = v_b_1783_;
goto v___jp_1784_;
}
}
v___jp_1784_:
{
size_t v___x_1786_; size_t v___x_1787_; 
v___x_1786_ = ((size_t)1ULL);
v___x_1787_ = lean_usize_add(v_i_1782_, v___x_1786_);
v_i_1782_ = v___x_1787_;
v_b_1783_ = v___y_1785_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1779_ = stack[0].m_obj;
lean_object* v_as_1780_ = stack[1].m_obj;
size_t v_sz_1781_ = stack[2].m_num;
size_t v_i_1782_ = stack[3].m_num;
lean_object* v_b_1783_ = stack[4].m_obj;
lean_object* v_res_1794_;
v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1779_, v_as_1780_, v_sz_1781_, v_i_1782_, v_b_1783_);
stack->m_obj
 = v_res_1794_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg___boxed(lean_object* v_cmp_1795_, lean_object* v_as_1796_, lean_object* v_sz_1797_, lean_object* v_i_1798_, lean_object* v_b_1799_){
_start:
{
size_t v_sz_boxed_1800_; size_t v_i_boxed_1801_; lean_object* v_res_1802_; 
v_sz_boxed_1800_ = lean_unbox_usize(v_sz_1797_);
lean_dec(v_sz_1797_);
v_i_boxed_1801_ = lean_unbox_usize(v_i_1798_);
lean_dec(v_i_1798_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1795_, v_as_1796_, v_sz_boxed_1800_, v_i_boxed_1801_, v_b_1799_);
lean_dec_ref(v_as_1796_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg(lean_object* v_a_1803_, lean_object* v_cmp_1804_){
_start:
{
lean_object* v_r_1805_; size_t v_sz_1806_; size_t v___x_1807_; lean_object* v___x_1808_; 
v_r_1805_ = lean_box(1);
v_sz_1806_ = lean_array_size(v_a_1803_);
v___x_1807_ = ((size_t)0ULL);
v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1804_, v_a_1803_, v_sz_1806_, v___x_1807_, v_r_1805_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg___boxed(lean_object* v_a_1809_, lean_object* v_cmp_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Std_TreeSet_ofArray___redArg(v_a_1809_, v_cmp_1810_);
lean_dec_ref(v_a_1809_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray(lean_object* v_00_u03b1_1812_, lean_object* v_a_1813_, lean_object* v_cmp_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Std_TreeSet_ofArray___redArg(v_a_1813_, v_cmp_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___boxed(lean_object* v_00_u03b1_1816_, lean_object* v_a_1817_, lean_object* v_cmp_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Std_TreeSet_ofArray(v_00_u03b1_1816_, v_a_1817_, v_cmp_1818_);
lean_dec_ref(v_a_1817_);
return v_res_1819_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(lean_object* v_00_u03b1_1820_, lean_object* v_cmp_1821_, lean_object* v_as_1822_, size_t v_sz_1823_, size_t v_i_1824_, lean_object* v_b_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1821_, v_as_1822_, v_sz_1823_, v_i_1824_, v_b_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1821_ = stack[1].m_obj;
lean_object* v_as_1822_ = stack[2].m_obj;
size_t v_sz_1823_ = stack[3].m_num;
size_t v_i_1824_ = stack[4].m_num;
lean_object* v_b_1825_ = stack[5].m_obj;
lean_object* v_res_1827_;
v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(lean_box(0), v_cmp_1821_, v_as_1822_, v_sz_1823_, v_i_1824_, v_b_1825_);
stack->m_obj
 = v_res_1827_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___boxed(lean_object* v_00_u03b1_1828_, lean_object* v_cmp_1829_, lean_object* v_as_1830_, lean_object* v_sz_1831_, lean_object* v_i_1832_, lean_object* v_b_1833_){
_start:
{
size_t v_sz_boxed_1834_; size_t v_i_boxed_1835_; lean_object* v_res_1836_; 
v_sz_boxed_1834_ = lean_unbox_usize(v_sz_1831_);
lean_dec(v_sz_1831_);
v_i_boxed_1835_ = lean_unbox_usize(v_i_1832_);
lean_dec(v_i_1832_);
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(v_00_u03b1_1828_, v_cmp_1829_, v_as_1830_, v_sz_boxed_1834_, v_i_boxed_1835_, v_b_1833_);
lean_dec_ref(v_as_1830_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0(lean_object* v_b_u2082_1839_, lean_object* v_x_1840_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_b_u2082_1839_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; 
v___x_1842_ = ((lean_object*)(l_Std_TreeSet_merge___redArg___lam__0___closed__0));
return v___x_1842_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1843_, lean_object* v_x_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Std_TreeSet_merge___redArg___lam__0(v_b_u2082_1843_, v_x_1844_);
lean_dec(v_x_1844_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__1(lean_object* v_cmp_1846_, lean_object* v_t_1847_, lean_object* v_a_1848_, lean_object* v_b_u2082_1849_){
_start:
{
lean_object* v___f_1850_; lean_object* v___x_1851_; 
v___f_1850_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1850_, 0, v_b_u2082_1849_);
v___x_1851_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_1846_, v_a_1848_, v___f_1850_, v_t_1847_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg(lean_object* v_cmp_1852_, lean_object* v_t_u2081_1853_, lean_object* v_t_u2082_1854_){
_start:
{
lean_object* v___f_1855_; lean_object* v___x_1856_; 
v___f_1855_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1855_, 0, v_cmp_1852_);
v___x_1856_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1855_, v_t_u2081_1853_, v_t_u2082_1854_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge(lean_object* v_00_u03b1_1857_, lean_object* v_cmp_1858_, lean_object* v_t_u2081_1859_, lean_object* v_t_u2082_1860_){
_start:
{
lean_object* v___f_1861_; lean_object* v___x_1862_; 
v___f_1861_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1861_, 0, v_cmp_1858_);
v___x_1862_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1861_, v_t_u2081_1859_, v_t_u2082_1860_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg___lam__0(lean_object* v_cmp_1863_, lean_object* v_a_1864_, lean_object* v_____s_1865_){
_start:
{
uint8_t v___x_1866_; 
lean_inc(v_____s_1865_);
lean_inc(v_a_1864_);
lean_inc_ref(v_cmp_1863_);
v___x_1866_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1863_, v_a_1864_, v_____s_1865_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_box(0);
v___x_1868_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1863_, v_a_1864_, v___x_1867_, v_____s_1865_);
v___x_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; 
lean_dec(v_a_1864_);
lean_dec_ref(v_cmp_1863_);
v___x_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1870_, 0, v_____s_1865_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg(lean_object* v_cmp_1871_, lean_object* v_inst_1872_, lean_object* v_t_1873_, lean_object* v_l_1874_){
_start:
{
lean_object* v___f_1875_; lean_object* v___x_1876_; 
v___f_1875_ = lean_alloc_closure((void*)(l_Std_TreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1875_, 0, v_cmp_1871_);
v___x_1876_ = lean_apply_4(v_inst_1872_, lean_box(0), v_l_1874_, v_t_1873_, v___f_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany(lean_object* v_00_u03b1_1877_, lean_object* v_cmp_1878_, lean_object* v_00_u03c1_1879_, lean_object* v_inst_1880_, lean_object* v_t_1881_, lean_object* v_l_1882_){
_start:
{
lean_object* v___f_1883_; lean_object* v___x_1884_; 
v___f_1883_ = lean_alloc_closure((void*)(l_Std_TreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1883_, 0, v_cmp_1878_);
v___x_1884_ = lean_apply_4(v_inst_1880_, lean_box(0), v_l_1882_, v_t_1881_, v___f_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_union___redArg(lean_object* v_cmp_1885_, lean_object* v_t_u2081_1886_, lean_object* v_t_u2082_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1885_, v_t_u2081_1886_, v_t_u2082_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_union(lean_object* v_00_u03b1_1889_, lean_object* v_cmp_1890_, lean_object* v_t_u2081_1891_, lean_object* v_t_u2082_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1890_, v_t_u2081_1891_, v_t_u2082_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion___redArg(lean_object* v_cmp_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_alloc_closure((void*)(l_Std_TreeSet_union), 4, 2);
lean_closure_set(v___x_1895_, 0, lean_box(0));
lean_closure_set(v___x_1895_, 1, v_cmp_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion(lean_object* v_00_u03b1_1896_, lean_object* v_cmp_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_alloc_closure((void*)(l_Std_TreeSet_union), 4, 2);
lean_closure_set(v___x_1898_, 0, lean_box(0));
lean_closure_set(v___x_1898_, 1, v_cmp_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_inter___redArg(lean_object* v_cmp_1899_, lean_object* v_t_u2081_1900_, lean_object* v_t_u2082_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1899_, v_t_u2081_1900_, v_t_u2082_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_inter(lean_object* v_00_u03b1_1903_, lean_object* v_cmp_1904_, lean_object* v_t_u2081_1905_, lean_object* v_t_u2082_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1904_, v_t_u2081_1905_, v_t_u2082_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter___redArg(lean_object* v_cmp_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_alloc_closure((void*)(l_Std_TreeSet_inter), 4, 2);
lean_closure_set(v___x_1909_, 0, lean_box(0));
lean_closure_set(v___x_1909_, 1, v_cmp_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter(lean_object* v_00_u03b1_1910_, lean_object* v_cmp_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_alloc_closure((void*)(l_Std_TreeSet_inter), 4, 2);
lean_closure_set(v___x_1912_, 0, lean_box(0));
lean_closure_set(v___x_1912_, 1, v_cmp_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_cmp_1913_, lean_object* v_t_1914_, lean_object* v_k_1915_){
_start:
{
if (lean_obj_tag(v_t_1914_) == 0)
{
lean_object* v_k_1916_; lean_object* v_v_1917_; lean_object* v_l_1918_; lean_object* v_r_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v_k_1916_ = lean_ctor_get(v_t_1914_, 1);
lean_inc(v_k_1916_);
v_v_1917_ = lean_ctor_get(v_t_1914_, 2);
lean_inc(v_v_1917_);
v_l_1918_ = lean_ctor_get(v_t_1914_, 3);
lean_inc(v_l_1918_);
v_r_1919_ = lean_ctor_get(v_t_1914_, 4);
lean_inc(v_r_1919_);
lean_dec_ref_known(v_t_1914_, 5);
lean_inc_ref(v_cmp_1913_);
lean_inc(v_k_1915_);
v___x_1920_ = lean_apply_2(v_cmp_1913_, v_k_1915_, v_k_1916_);
v___x_1921_ = lean_unbox(v___x_1920_);
switch(v___x_1921_)
{
case 0:
{
lean_dec(v_r_1919_);
lean_dec(v_v_1917_);
v_t_1914_ = v_l_1918_;
goto _start;
}
case 1:
{
lean_object* v___x_1923_; 
lean_dec(v_r_1919_);
lean_dec(v_l_1918_);
lean_dec(v_k_1915_);
lean_dec_ref(v_cmp_1913_);
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_v_1917_);
return v___x_1923_;
}
default: 
{
lean_dec(v_l_1918_);
lean_dec(v_v_1917_);
v_t_1914_ = v_r_1919_;
goto _start;
}
}
}
else
{
lean_object* v___x_1925_; 
lean_dec(v_k_1915_);
lean_dec_ref(v_cmp_1913_);
v___x_1925_ = lean_box(0);
return v___x_1925_;
}
}
}
uint8_t l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1926_, lean_object* v_x_1927_){
_start:
{
if (lean_obj_tag(v_x_1926_) == 0)
{
if (lean_obj_tag(v_x_1927_) == 0)
{
uint8_t v___x_1928_; 
v___x_1928_ = 1;
return v___x_1928_;
}
else
{
uint8_t v___x_1929_; 
v___x_1929_ = 0;
return v___x_1929_;
}
}
else
{
if (lean_obj_tag(v_x_1927_) == 0)
{
uint8_t v___x_1930_; 
v___x_1930_ = 0;
return v___x_1930_;
}
else
{
uint8_t v___x_1931_; 
v___x_1931_ = 1;
return v___x_1931_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1926_ = stack[0].m_obj;
lean_object* v_x_1927_ = stack[1].m_obj;
uint8_t v_res_1932_;
v_res_1932_ = l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v_x_1926_, v_x_1927_);
stack->m_num = v_res_1932_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1933_, lean_object* v_x_1934_){
_start:
{
uint8_t v_res_1935_; lean_object* v_r_1936_; 
v_res_1935_ = l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v_x_1933_, v_x_1934_);
lean_dec(v_x_1934_);
lean_dec(v_x_1933_);
v_r_1936_ = lean_box(v_res_1935_);
return v_r_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v_cmp_1939_, lean_object* v_t_u2082_1940_, lean_object* v_init_1941_, lean_object* v_x_1942_){
_start:
{
lean_object* v___x_1943_; uint8_t v___y_1945_; lean_object* v___x_1950_; uint8_t v___y_1952_; uint8_t v___x_1970_; 
v___x_1943_ = lean_box(0);
v___x_1950_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___x_1970_ = lean_nat_dec_eq(v___y_1937_, v___y_1938_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1971_; 
v___x_1971_ = 1;
v___y_1952_ = v___x_1971_;
goto v___jp_1951_;
}
else
{
uint8_t v___x_1972_; 
v___x_1972_ = 0;
v___y_1952_ = v___x_1972_;
goto v___jp_1951_;
}
v___jp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1946_ = lean_box(v___y_1945_);
v___x_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___x_1943_);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
return v___x_1949_;
}
v___jp_1951_:
{
if (lean_obj_tag(v_x_1942_) == 0)
{
lean_object* v_k_1953_; lean_object* v_v_1954_; lean_object* v_l_1955_; lean_object* v_r_1956_; lean_object* v___x_1957_; 
v_k_1953_ = lean_ctor_get(v_x_1942_, 1);
lean_inc(v_k_1953_);
v_v_1954_ = lean_ctor_get(v_x_1942_, 2);
lean_inc(v_v_1954_);
v_l_1955_ = lean_ctor_get(v_x_1942_, 3);
lean_inc(v_l_1955_);
v_r_1956_ = lean_ctor_get(v_x_1942_, 4);
lean_inc(v_r_1956_);
lean_dec_ref_known(v_x_1942_, 5);
lean_inc(v_t_u2082_1940_);
lean_inc_ref(v_cmp_1939_);
v___x_1957_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1937_, v___y_1938_, v_cmp_1939_, v_t_u2082_1940_, v_init_1941_, v_l_1955_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_dec(v_r_1956_);
lean_dec(v_v_1954_);
lean_dec(v_k_1953_);
lean_dec(v_t_u2082_1940_);
lean_dec_ref(v_cmp_1939_);
return v___x_1957_;
}
else
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1967_; 
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v___x_1957_, 0);
lean_dec(v_unused_1968_);
v___x_1959_ = v___x_1957_;
v_isShared_1960_ = v_isSharedCheck_1967_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v___x_1957_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1967_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
lean_inc(v_t_u2082_1940_);
lean_inc_ref(v_cmp_1939_);
v___x_1961_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1939_, v_t_u2082_1940_, v_k_1953_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v_v_1954_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_v_1954_);
v___x_1963_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
uint8_t v___x_1964_; 
v___x_1964_ = l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v___x_1961_, v___x_1963_);
lean_dec_ref(v___x_1963_);
lean_dec(v___x_1961_);
if (v___x_1964_ == 0)
{
lean_dec(v_r_1956_);
lean_dec(v_t_u2082_1940_);
lean_dec_ref(v_cmp_1939_);
v___y_1945_ = v___y_1952_;
goto v___jp_1944_;
}
else
{
if (v___y_1952_ == 0)
{
v_init_1941_ = v___x_1950_;
v_x_1942_ = v_r_1956_;
goto _start;
}
else
{
lean_dec(v_r_1956_);
lean_dec(v_t_u2082_1940_);
lean_dec_ref(v_cmp_1939_);
v___y_1945_ = v___y_1952_;
goto v___jp_1944_;
}
}
}
}
}
}
else
{
lean_object* v___x_1969_; 
lean_dec(v_t_u2082_1940_);
lean_dec_ref(v_cmp_1939_);
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_init_1941_);
return v___x_1969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v_cmp_1975_, lean_object* v_t_u2082_1976_, lean_object* v_init_1977_, lean_object* v_x_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1973_, v___y_1974_, v_cmp_1975_, v_t_u2082_1976_, v_init_1977_, v_x_1978_);
lean_dec(v___y_1974_);
lean_dec(v___y_1973_);
return v_res_1979_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_1980_, lean_object* v_t_u2081_1981_, lean_object* v_t_u2082_1982_){
_start:
{
lean_object* v___y_1984_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1997_; 
if (lean_obj_tag(v_t_u2081_1981_) == 0)
{
lean_object* v_size_2000_; 
v_size_2000_ = lean_ctor_get(v_t_u2081_1981_, 0);
lean_inc(v_size_2000_);
v___y_1997_ = v_size_2000_;
goto v___jp_1996_;
}
else
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_unsigned_to_nat(0u);
v___y_1997_ = v___x_2001_;
goto v___jp_1996_;
}
v___jp_1983_:
{
lean_object* v_fst_1985_; 
v_fst_1985_ = lean_ctor_get(v___y_1984_, 0);
lean_inc(v_fst_1985_);
lean_dec_ref(v___y_1984_);
if (lean_obj_tag(v_fst_1985_) == 0)
{
uint8_t v___x_1986_; 
v___x_1986_ = 1;
return v___x_1986_;
}
else
{
lean_object* v_val_1987_; uint8_t v___x_1988_; 
v_val_1987_ = lean_ctor_get(v_fst_1985_, 0);
lean_inc(v_val_1987_);
lean_dec_ref_known(v_fst_1985_, 1);
v___x_1988_ = lean_unbox(v_val_1987_);
lean_dec(v_val_1987_);
return v___x_1988_;
}
}
v___jp_1989_:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_nat_dec_eq(v___y_1990_, v___y_1991_);
if (v___x_1992_ == 0)
{
lean_dec(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec(v_t_u2082_1982_);
lean_dec(v_t_u2081_1981_);
lean_dec_ref(v_cmp_1980_);
return v___x_1992_;
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v_a_1995_; 
v___x_1993_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___x_1994_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1990_, v___y_1991_, v_cmp_1980_, v_t_u2082_1982_, v___x_1993_, v_t_u2081_1981_);
lean_dec(v___y_1991_);
lean_dec(v___y_1990_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref(v___x_1994_);
v___y_1984_ = v_a_1995_;
goto v___jp_1983_;
}
}
v___jp_1996_:
{
if (lean_obj_tag(v_t_u2082_1982_) == 0)
{
lean_object* v_size_1998_; 
v_size_1998_ = lean_ctor_get(v_t_u2082_1982_, 0);
lean_inc(v_size_1998_);
v___y_1990_ = v___y_1997_;
v___y_1991_ = v_size_1998_;
goto v___jp_1989_;
}
else
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_unsigned_to_nat(0u);
v___y_1990_ = v___y_1997_;
v___y_1991_ = v___x_1999_;
goto v___jp_1989_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1980_ = stack[0].m_obj;
lean_object* v_t_u2081_1981_ = stack[1].m_obj;
lean_object* v_t_u2082_1982_ = stack[2].m_obj;
uint8_t v_res_2002_;
v_res_2002_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1980_, v_t_u2081_1981_, v_t_u2082_1982_);
stack->m_num = v_res_2002_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_2003_, lean_object* v_t_u2081_2004_, lean_object* v_t_u2082_2005_){
_start:
{
uint8_t v_res_2006_; lean_object* v_r_2007_; 
v_res_2006_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2003_, v_t_u2081_2004_, v_t_u2082_2005_);
v_r_2007_ = lean_box(v_res_2006_);
return v_r_2007_;
}
}
uint8_t l_Std_TreeSet_beq___redArg(lean_object* v_cmp_2008_, lean_object* v_t_u2081_2009_, lean_object* v_t_u2082_2010_){
_start:
{
uint8_t v___x_2011_; 
v___x_2011_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2008_, v_t_u2081_2009_, v_t_u2082_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT void l_Std_TreeSet_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2008_ = stack[0].m_obj;
lean_object* v_t_u2081_2009_ = stack[1].m_obj;
lean_object* v_t_u2082_2010_ = stack[2].m_obj;
uint8_t v_res_2012_;
v_res_2012_ = l_Std_TreeSet_beq___redArg(v_cmp_2008_, v_t_u2081_2009_, v_t_u2082_2010_);
stack->m_num = v_res_2012_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___redArg___boxed(lean_object* v_cmp_2013_, lean_object* v_t_u2081_2014_, lean_object* v_t_u2082_2015_){
_start:
{
uint8_t v_res_2016_; lean_object* v_r_2017_; 
v_res_2016_ = l_Std_TreeSet_beq___redArg(v_cmp_2013_, v_t_u2081_2014_, v_t_u2082_2015_);
v_r_2017_ = lean_box(v_res_2016_);
return v_r_2017_;
}
}
uint8_t l_Std_TreeSet_beq(lean_object* v_00_u03b1_2018_, lean_object* v_cmp_2019_, lean_object* v_t_u2081_2020_, lean_object* v_t_u2082_2021_){
_start:
{
uint8_t v___x_2022_; 
v___x_2022_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2019_, v_t_u2081_2020_, v_t_u2082_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT void l_Std_TreeSet_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2019_ = stack[1].m_obj;
lean_object* v_t_u2081_2020_ = stack[2].m_obj;
lean_object* v_t_u2082_2021_ = stack[3].m_obj;
uint8_t v_res_2023_;
v_res_2023_ = l_Std_TreeSet_beq(lean_box(0), v_cmp_2019_, v_t_u2081_2020_, v_t_u2082_2021_);
stack->m_num = v_res_2023_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___boxed(lean_object* v_00_u03b1_2024_, lean_object* v_cmp_2025_, lean_object* v_t_u2081_2026_, lean_object* v_t_u2082_2027_){
_start:
{
uint8_t v_res_2028_; lean_object* v_r_2029_; 
v_res_2028_ = l_Std_TreeSet_beq(v_00_u03b1_2024_, v_cmp_2025_, v_t_u2081_2026_, v_t_u2082_2027_);
v_r_2029_ = lean_box(v_res_2028_);
return v_r_2029_;
}
}
uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(lean_object* v_cmp_2030_, lean_object* v_t_u2081_2031_, lean_object* v_t_u2082_2032_){
_start:
{
uint8_t v___x_2033_; 
v___x_2033_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2030_, v_t_u2081_2031_, v_t_u2082_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT void l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2030_ = stack[0].m_obj;
lean_object* v_t_u2081_2031_ = stack[1].m_obj;
lean_object* v_t_u2082_2032_ = stack[2].m_obj;
uint8_t v_res_2034_;
v_res_2034_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(v_cmp_2030_, v_t_u2081_2031_, v_t_u2082_2032_);
stack->m_num = v_res_2034_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg___boxed(lean_object* v_cmp_2035_, lean_object* v_t_u2081_2036_, lean_object* v_t_u2082_2037_){
_start:
{
uint8_t v_res_2038_; lean_object* v_r_2039_; 
v_res_2038_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(v_cmp_2035_, v_t_u2081_2036_, v_t_u2082_2037_);
v_r_2039_ = lean_box(v_res_2038_);
return v_r_2039_;
}
}
uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(lean_object* v_00_u03b1_2040_, lean_object* v_cmp_2041_, lean_object* v_t_u2081_2042_, lean_object* v_t_u2082_2043_){
_start:
{
uint8_t v___x_2044_; 
v___x_2044_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2041_, v_t_u2081_2042_, v_t_u2082_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT void l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2041_ = stack[1].m_obj;
lean_object* v_t_u2081_2042_ = stack[2].m_obj;
lean_object* v_t_u2082_2043_ = stack[3].m_obj;
uint8_t v_res_2045_;
v_res_2045_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(lean_box(0), v_cmp_2041_, v_t_u2081_2042_, v_t_u2082_2043_);
stack->m_num = v_res_2045_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___boxed(lean_object* v_00_u03b1_2046_, lean_object* v_cmp_2047_, lean_object* v_t_u2081_2048_, lean_object* v_t_u2082_2049_){
_start:
{
uint8_t v_res_2050_; lean_object* v_r_2051_; 
v_res_2050_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(v_00_u03b1_2046_, v_cmp_2047_, v_t_u2081_2048_, v_t_u2082_2049_);
v_r_2051_ = lean_box(v_res_2050_);
return v_r_2051_;
}
}
uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(lean_object* v_cmp_2052_, lean_object* v_t_u2081_2053_, lean_object* v_t_u2082_2054_){
_start:
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2052_, v_t_u2081_2053_, v_t_u2082_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2052_ = stack[0].m_obj;
lean_object* v_t_u2081_2053_ = stack[1].m_obj;
lean_object* v_t_u2082_2054_ = stack[2].m_obj;
uint8_t v_res_2056_;
v_res_2056_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(v_cmp_2052_, v_t_u2081_2053_, v_t_u2082_2054_);
stack->m_num = v_res_2056_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_2057_, lean_object* v_t_u2081_2058_, lean_object* v_t_u2082_2059_){
_start:
{
uint8_t v_res_2060_; lean_object* v_r_2061_; 
v_res_2060_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(v_cmp_2057_, v_t_u2081_2058_, v_t_u2082_2059_);
v_r_2061_ = lean_box(v_res_2060_);
return v_r_2061_;
}
}
uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(lean_object* v_00_u03b1_2062_, lean_object* v_cmp_2063_, lean_object* v_t_u2081_2064_, lean_object* v_t_u2082_2065_){
_start:
{
uint8_t v___x_2066_; 
v___x_2066_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2063_, v_t_u2081_2064_, v_t_u2082_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2063_ = stack[1].m_obj;
lean_object* v_t_u2081_2064_ = stack[2].m_obj;
lean_object* v_t_u2082_2065_ = stack[3].m_obj;
uint8_t v_res_2067_;
v_res_2067_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(lean_box(0), v_cmp_2063_, v_t_u2081_2064_, v_t_u2082_2065_);
stack->m_num = v_res_2067_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2068_, lean_object* v_cmp_2069_, lean_object* v_t_u2081_2070_, lean_object* v_t_u2082_2071_){
_start:
{
uint8_t v_res_2072_; lean_object* v_r_2073_; 
v_res_2072_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(v_00_u03b1_2068_, v_cmp_2069_, v_t_u2081_2070_, v_t_u2082_2071_);
v_r_2073_ = lean_box(v_res_2072_);
return v_r_2073_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2074_, lean_object* v_cmp_2075_, lean_object* v_t_u2081_2076_, lean_object* v_t_u2082_2077_){
_start:
{
uint8_t v___x_2078_; 
v___x_2078_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2075_, v_t_u2081_2076_, v_t_u2082_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2075_ = stack[1].m_obj;
lean_object* v_t_u2081_2076_ = stack[2].m_obj;
lean_object* v_t_u2082_2077_ = stack[3].m_obj;
uint8_t v_res_2079_;
v_res_2079_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(lean_box(0), v_cmp_2075_, v_t_u2081_2076_, v_t_u2082_2077_);
stack->m_num = v_res_2079_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2080_, lean_object* v_cmp_2081_, lean_object* v_t_u2081_2082_, lean_object* v_t_u2082_2083_){
_start:
{
uint8_t v_res_2084_; lean_object* v_r_2085_; 
v_res_2084_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(v_00_u03b1_2080_, v_cmp_2081_, v_t_u2081_2082_, v_t_u2082_2083_);
v_r_2085_ = lean_box(v_res_2084_);
return v_r_2085_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2086_, lean_object* v_cmp_2087_, lean_object* v_00_u03b4_2088_, lean_object* v_t_2089_, lean_object* v_k_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_2087_, v_t_2089_, v_k_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v_cmp_2095_, lean_object* v_t_u2082_2096_, lean_object* v_init_2097_, lean_object* v_x_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_2093_, v___y_2094_, v_cmp_2095_, v_t_u2082_2096_, v_init_2097_, v_x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v_cmp_2103_, lean_object* v_t_u2082_2104_, lean_object* v_init_2105_, lean_object* v_x_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2100_, v___y_2101_, v___y_2102_, v_cmp_2103_, v_t_u2082_2104_, v_init_2105_, v_x_2106_);
lean_dec(v___y_2102_);
lean_dec(v___y_2101_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq___redArg(lean_object* v_cmp_2108_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_alloc_closure((void*)(l_Std_TreeSet_beq___boxed), 4, 2);
lean_closure_set(v___x_2109_, 0, lean_box(0));
lean_closure_set(v___x_2109_, 1, v_cmp_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq(lean_object* v_00_u03b1_2110_, lean_object* v_cmp_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_alloc_closure((void*)(l_Std_TreeSet_beq___boxed), 4, 2);
lean_closure_set(v___x_2112_, 0, lean_box(0));
lean_closure_set(v___x_2112_, 1, v_cmp_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_diff___redArg(lean_object* v_cmp_2113_, lean_object* v_t_u2081_2114_, lean_object* v_t_u2082_2115_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2113_, v_t_u2081_2114_, v_t_u2082_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_diff(lean_object* v_00_u03b1_2117_, lean_object* v_cmp_2118_, lean_object* v_t_u2081_2119_, lean_object* v_t_u2082_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2118_, v_t_u2081_2119_, v_t_u2082_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff___redArg(lean_object* v_cmp_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_alloc_closure((void*)(l_Std_TreeSet_diff), 4, 2);
lean_closure_set(v___x_2123_, 0, lean_box(0));
lean_closure_set(v___x_2123_, 1, v_cmp_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff(lean_object* v_00_u03b1_2124_, lean_object* v_cmp_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_alloc_closure((void*)(l_Std_TreeSet_diff), 4, 2);
lean_closure_set(v___x_2126_, 0, lean_box(0));
lean_closure_set(v___x_2126_, 1, v_cmp_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg___lam__0(lean_object* v_cmp_2127_, lean_object* v_a_2128_, lean_object* v_____s_2129_){
_start:
{
lean_object* v_r_2130_; lean_object* v___x_2131_; 
v_r_2130_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2127_, v_a_2128_, v_____s_2129_);
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_r_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg(lean_object* v_cmp_2132_, lean_object* v_inst_2133_, lean_object* v_t_2134_, lean_object* v_l_2135_){
_start:
{
lean_object* v___f_2136_; lean_object* v___x_2137_; 
v___f_2136_ = lean_alloc_closure((void*)(l_Std_TreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2136_, 0, v_cmp_2132_);
v___x_2137_ = lean_apply_4(v_inst_2133_, lean_box(0), v_l_2135_, v_t_2134_, v___f_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany(lean_object* v_00_u03b1_2138_, lean_object* v_cmp_2139_, lean_object* v_00_u03c1_2140_, lean_object* v_inst_2141_, lean_object* v_t_2142_, lean_object* v_l_2143_){
_start:
{
lean_object* v___f_2144_; lean_object* v___x_2145_; 
v___f_2144_ = lean_alloc_closure((void*)(l_Std_TreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2144_, 0, v_cmp_2139_);
v___x_2145_ = lean_apply_4(v_inst_2141_, lean_box(0), v_l_2143_, v_t_2142_, v___f_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1(lean_object* v___f_2149_, lean_object* v_inst_2150_, lean_object* v_m_2151_, lean_object* v_prec_2152_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2153_ = ((lean_object*)(l_Std_TreeSet_instRepr___redArg___lam__1___closed__1));
v___x_2154_ = lean_box(0);
v___x_2155_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_2156_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2155_, v___f_2149_, v___x_2154_, v_m_2151_);
v___x_2157_ = l_List_repr___redArg(v_inst_2150_, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2153_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Repr_addAppParen(v___x_2158_, v_prec_2152_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1___boxed(lean_object* v___f_2160_, lean_object* v_inst_2161_, lean_object* v_m_2162_, lean_object* v_prec_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Std_TreeSet_instRepr___redArg___lam__1(v___f_2160_, v_inst_2161_, v_m_2162_, v_prec_2163_);
lean_dec(v_prec_2163_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg(lean_object* v_inst_2165_){
_start:
{
lean_object* v___f_2166_; lean_object* v___f_2167_; 
v___f_2166_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___f_2167_ = lean_alloc_closure((void*)(l_Std_TreeSet_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2167_, 0, v___f_2166_);
lean_closure_set(v___f_2167_, 1, v_inst_2165_);
return v___f_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr(lean_object* v_00_u03b1_2168_, lean_object* v_cmp_2169_, lean_object* v_inst_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Std_TreeSet_instRepr___redArg(v_inst_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___boxed(lean_object* v_00_u03b1_2172_, lean_object* v_cmp_2173_, lean_object* v_inst_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Std_TreeSet_instRepr(v_00_u03b1_2172_, v_cmp_2173_, v_inst_2174_);
lean_dec_ref(v_cmp_2173_);
return v_res_2175_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_TreeSet___auto__1 = _init_l_Std_TreeSet___auto__1();
lean_mark_persistent(l_Std_TreeSet___auto__1);
l_Std_TreeSet_ofList___auto__1 = _init_l_Std_TreeSet_ofList___auto__1();
lean_mark_persistent(l_Std_TreeSet_ofList___auto__1);
l_Std_TreeSet_ofArray___auto__1 = _init_l_Std_TreeSet_ofArray___auto__1();
lean_mark_persistent(l_Std_TreeSet_ofArray___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeSet_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
