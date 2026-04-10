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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__15;
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__16;
static const lean_ctor_object l_Std_TreeSet___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
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
static lean_once_cell_t l_Std_TreeSet___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_TreeSet___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Std_TreeSet___auto__1___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__14));
v___x_34_ = lean_string_utf8_byte_size(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__16(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__15, &l_Std_TreeSet___auto__1___closed__15_once, _init_l_Std_TreeSet___auto__1___closed__15);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__14));
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_box(0);
v___x_42_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__17));
v___x_43_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__16, &l_Std_TreeSet___auto__1___closed__16_once, _init_l_Std_TreeSet___auto__1___closed__16);
v___x_44_ = lean_box(2);
v___x_45_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
lean_ctor_set(v___x_45_, 2, v___x_42_);
lean_ctor_set(v___x_45_, 3, v___x_41_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__18, &l_Std_TreeSet___auto__1___closed__18_once, _init_l_Std_TreeSet___auto__1___closed__18);
v___x_47_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__13, &l_Std_TreeSet___auto__1___closed__13_once, _init_l_Std_TreeSet___auto__1___closed__13);
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__19, &l_Std_TreeSet___auto__1___closed__19_once, _init_l_Std_TreeSet___auto__1___closed__19);
v___x_50_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__11));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__21(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__20, &l_Std_TreeSet___auto__1___closed__20_once, _init_l_Std_TreeSet___auto__1___closed__20);
v___x_54_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__5));
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__22(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__21, &l_Std_TreeSet___auto__1___closed__21_once, _init_l_Std_TreeSet___auto__1___closed__21);
v___x_57_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__9));
v___x_58_ = lean_box(2);
v___x_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__23(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__22, &l_Std_TreeSet___auto__1___closed__22_once, _init_l_Std_TreeSet___auto__1___closed__22);
v___x_61_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__24(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__23, &l_Std_TreeSet___auto__1___closed__23_once, _init_l_Std_TreeSet___auto__1___closed__23);
v___x_64_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__7));
v___x_65_ = lean_box(2);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__25(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__24, &l_Std_TreeSet___auto__1___closed__24_once, _init_l_Std_TreeSet___auto__1___closed__24);
v___x_68_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__5));
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1___closed__26(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__25, &l_Std_TreeSet___auto__1___closed__25_once, _init_l_Std_TreeSet___auto__1___closed__25);
v___x_71_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__4));
v___x_72_ = lean_box(2);
v___x_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_TreeSet___auto__1(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__26, &l_Std_TreeSet___auto__1___closed__26_once, _init_l_Std_TreeSet___auto__1___closed__26);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_empty(lean_object* v_00_u03b1_75_, lean_object* v_cmp_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(1);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___boxed(lean_object* v_00_u03b1_78_, lean_object* v_cmp_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_TreeSet_empty(v_00_u03b1_78_, v_cmp_79_);
lean_dec_ref(v_cmp_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection(lean_object* v_00_u03b1_81_, lean_object* v_cmp_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_box(1);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_84_, lean_object* v_cmp_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_TreeSet_instEmptyCollection(v_00_u03b1_84_, v_cmp_85_);
lean_dec_ref(v_cmp_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited(lean_object* v_00_u03b1_87_, lean_object* v_cmp_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(1);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___boxed(lean_object* v_00_u03b1_90_, lean_object* v_cmp_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_TreeSet_instInhabited(v_00_u03b1_90_, v_cmp_91_);
lean_dec_ref(v_cmp_91_);
return v_res_92_;
}
}
static lean_object* _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3));
v___x_131_ = l_String_toRawSubstring_x27(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(lean_object* v_x_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__3));
lean_inc(v_x_149_);
v___x_153_ = l_Lean_Syntax_isOfKind(v_x_149_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v_x_149_);
v___x_154_ = lean_box(1);
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_a_151_);
return v___x_155_;
}
else
{
lean_object* v_quotContext_156_; lean_object* v_currMacroScope_157_; lean_object* v_ref_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_quotContext_156_ = lean_ctor_get(v_a_150_, 1);
v_currMacroScope_157_ = lean_ctor_get(v_a_150_, 2);
v_ref_158_ = lean_ctor_get(v_a_150_, 5);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = l_Lean_Syntax_getArg(v_x_149_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(2u);
v___x_162_ = l_Lean_Syntax_getArg(v_x_149_, v___x_161_);
lean_dec(v_x_149_);
v___x_163_ = 0;
v___x_164_ = l_Lean_SourceInfo_fromRef(v_ref_158_, v___x_163_);
v___x_165_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2));
v___x_166_ = lean_obj_once(&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4, &l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4_once, _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4);
v___x_167_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_157_);
lean_inc(v_quotContext_156_);
v___x_168_ = l_Lean_addMacroScope(v_quotContext_156_, v___x_167_, v_currMacroScope_157_);
v___x_169_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10));
lean_inc_n(v___x_164_, 2);
v___x_170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_170_, 0, v___x_164_);
lean_ctor_set(v___x_170_, 1, v___x_166_);
lean_ctor_set(v___x_170_, 2, v___x_168_);
lean_ctor_set(v___x_170_, 3, v___x_169_);
v___x_171_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__9));
v___x_172_ = l_Lean_Syntax_node2(v___x_164_, v___x_171_, v___x_160_, v___x_162_);
v___x_173_ = l_Lean_Syntax_node2(v___x_164_, v___x_165_, v___x_170_, v___x_172_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_a_151_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___boxed(lean_object* v_x_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(v_x_175_, v_a_176_, v_a_177_);
lean_dec_ref(v_a_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(lean_object* v_x_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2));
lean_inc(v_x_182_);
v___x_186_ = l_Lean_Syntax_isOfKind(v_x_182_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_x_182_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v_a_184_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = l_Lean_Syntax_getArg(v_x_182_, v___x_189_);
v___x_191_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1));
lean_inc(v___x_190_);
v___x_192_ = l_Lean_Syntax_isOfKind(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v___x_190_);
lean_dec(v_x_182_);
v___x_193_ = lean_box(0);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v_a_184_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = l_Lean_Syntax_getArg(v_x_182_, v___x_195_);
lean_dec(v_x_182_);
v___x_197_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_196_);
v___x_198_ = l_Lean_Syntax_matchesNull(v___x_196_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v___x_196_);
lean_dec(v___x_190_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v_a_184_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_ref_203_; uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_201_ = l_Lean_Syntax_getArg(v___x_196_, v___x_189_);
v___x_202_ = l_Lean_Syntax_getArg(v___x_196_, v___x_195_);
lean_dec(v___x_196_);
v_ref_203_ = l_Lean_replaceRef(v___x_190_, v_a_183_);
lean_dec(v___x_190_);
v___x_204_ = 0;
v___x_205_ = l_Lean_SourceInfo_fromRef(v_ref_203_, v___x_204_);
lean_dec(v_ref_203_);
v___x_206_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__3));
v___x_207_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__6));
lean_inc(v___x_205_);
v___x_208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_205_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = l_Lean_Syntax_node3(v___x_205_, v___x_206_, v___x_201_, v___x_208_, v___x_202_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v_a_184_);
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___boxed(lean_object* v_x_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(v_x_211_, v_a_212_, v_a_213_);
lean_dec(v_a_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insert___redArg(lean_object* v_cmp_215_, lean_object* v_l_216_, lean_object* v_a_217_){
_start:
{
uint8_t v___x_218_; 
lean_inc(v_l_216_);
lean_inc(v_a_217_);
lean_inc_ref(v_cmp_215_);
v___x_218_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_215_, v_a_217_, v_l_216_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_box(0);
v___x_220_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_215_, v_a_217_, v___x_219_, v_l_216_);
return v___x_220_;
}
else
{
lean_dec(v_a_217_);
lean_dec_ref(v_cmp_215_);
return v_l_216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insert(lean_object* v_00_u03b1_221_, lean_object* v_cmp_222_, lean_object* v_l_223_, lean_object* v_a_224_){
_start:
{
uint8_t v___x_225_; 
lean_inc(v_l_223_);
lean_inc(v_a_224_);
lean_inc_ref(v_cmp_222_);
v___x_225_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_222_, v_a_224_, v_l_223_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_box(0);
v___x_227_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_222_, v_a_224_, v___x_226_, v_l_223_);
return v___x_227_;
}
else
{
lean_dec(v_a_224_);
lean_dec_ref(v_cmp_222_);
return v_l_223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg___lam__0(lean_object* v_cmp_228_, lean_object* v_e_229_){
_start:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_box(1);
lean_inc(v_e_229_);
lean_inc_ref(v_cmp_228_);
v___x_231_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_228_, v_e_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_box(0);
v___x_233_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_228_, v_e_229_, v___x_232_, v___x_230_);
return v___x_233_;
}
else
{
lean_dec(v_e_229_);
lean_dec_ref(v_cmp_228_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg(lean_object* v_cmp_234_){
_start:
{
lean_object* v___f_235_; 
v___f_235_ = lean_alloc_closure((void*)(l_Std_TreeSet_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_235_, 0, v_cmp_234_);
return v___f_235_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton(lean_object* v_00_u03b1_236_, lean_object* v_cmp_237_){
_start:
{
lean_object* v___f_238_; 
v___f_238_ = lean_alloc_closure((void*)(l_Std_TreeSet_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_238_, 0, v_cmp_237_);
return v___f_238_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg___lam__0(lean_object* v_cmp_239_, lean_object* v_e_240_, lean_object* v_s_241_){
_start:
{
uint8_t v___x_242_; 
lean_inc(v_s_241_);
lean_inc(v_e_240_);
lean_inc_ref(v_cmp_239_);
v___x_242_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_239_, v_e_240_, v_s_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_box(0);
v___x_244_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_239_, v_e_240_, v___x_243_, v_s_241_);
return v___x_244_;
}
else
{
lean_dec(v_e_240_);
lean_dec_ref(v_cmp_239_);
return v_s_241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg(lean_object* v_cmp_245_){
_start:
{
lean_object* v___f_246_; 
v___f_246_ = lean_alloc_closure((void*)(l_Std_TreeSet_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_246_, 0, v_cmp_245_);
return v___f_246_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert(lean_object* v_00_u03b1_247_, lean_object* v_cmp_248_){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = lean_alloc_closure((void*)(l_Std_TreeSet_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_249_, 0, v_cmp_248_);
return v___f_249_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert___redArg(lean_object* v_cmp_250_, lean_object* v_t_251_, lean_object* v_a_252_){
_start:
{
uint8_t v___x_253_; 
lean_inc(v_t_251_);
lean_inc(v_a_252_);
lean_inc_ref(v_cmp_250_);
v___x_253_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_250_, v_a_252_, v_t_251_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = lean_box(0);
v___x_255_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_250_, v_a_252_, v___x_254_, v_t_251_);
v___x_256_ = lean_box(v___x_253_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v_a_252_);
lean_dec_ref(v_cmp_250_);
v___x_258_ = lean_box(v___x_253_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_t_251_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert(lean_object* v_00_u03b1_260_, lean_object* v_cmp_261_, lean_object* v_t_262_, lean_object* v_a_263_){
_start:
{
uint8_t v___x_264_; 
lean_inc(v_t_262_);
lean_inc(v_a_263_);
lean_inc_ref(v_cmp_261_);
v___x_264_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_261_, v_a_263_, v_t_262_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = lean_box(0);
v___x_266_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_261_, v_a_263_, v___x_265_, v_t_262_);
v___x_267_ = lean_box(v___x_264_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v_a_263_);
lean_dec_ref(v_cmp_261_);
v___x_269_ = lean_box(v___x_264_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_t_262_);
return v___x_270_;
}
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_contains___redArg(lean_object* v_cmp_271_, lean_object* v_l_272_, lean_object* v_a_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_271_, v_a_273_, v_l_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___redArg___boxed(lean_object* v_cmp_275_, lean_object* v_l_276_, lean_object* v_a_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Std_TreeSet_contains___redArg(v_cmp_275_, v_l_276_, v_a_277_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_contains(lean_object* v_00_u03b1_280_, lean_object* v_cmp_281_, lean_object* v_l_282_, lean_object* v_a_283_){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_281_, v_a_283_, v_l_282_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___boxed(lean_object* v_00_u03b1_285_, lean_object* v_cmp_286_, lean_object* v_l_287_, lean_object* v_a_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Std_TreeSet_contains(v_00_u03b1_285_, v_cmp_286_, v_l_287_, v_a_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership(lean_object* v_00_u03b1_291_, lean_object* v_cmp_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_box(0);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___boxed(lean_object* v_00_u03b1_294_, lean_object* v_cmp_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_TreeSet_instMembership(v_00_u03b1_294_, v_cmp_295_);
lean_dec_ref(v_cmp_295_);
return v_res_296_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableMem___redArg(lean_object* v_cmp_297_, lean_object* v_m_298_, lean_object* v_a_299_){
_start:
{
uint8_t v___x_300_; 
v___x_300_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_297_, v_a_299_, v_m_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___redArg___boxed(lean_object* v_cmp_301_, lean_object* v_m_302_, lean_object* v_a_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Std_TreeSet_instDecidableMem___redArg(v_cmp_301_, v_m_302_, v_a_303_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableMem(lean_object* v_00_u03b1_306_, lean_object* v_cmp_307_, lean_object* v_m_308_, lean_object* v_a_309_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_307_, v_a_309_, v_m_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___boxed(lean_object* v_00_u03b1_311_, lean_object* v_cmp_312_, lean_object* v_m_313_, lean_object* v_a_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Std_TreeSet_instDecidableMem(v_00_u03b1_311_, v_cmp_312_, v_m_313_, v_a_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg(lean_object* v_t_317_){
_start:
{
if (lean_obj_tag(v_t_317_) == 0)
{
lean_object* v_size_318_; 
v_size_318_ = lean_ctor_get(v_t_317_, 0);
lean_inc(v_size_318_);
return v_size_318_;
}
else
{
lean_object* v___x_319_; 
v___x_319_ = lean_unsigned_to_nat(0u);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg___boxed(lean_object* v_t_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Std_TreeSet_size___redArg(v_t_320_);
lean_dec(v_t_320_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size(lean_object* v_00_u03b1_322_, lean_object* v_cmp_323_, lean_object* v_t_324_){
_start:
{
if (lean_obj_tag(v_t_324_) == 0)
{
lean_object* v_size_325_; 
v_size_325_ = lean_ctor_get(v_t_324_, 0);
lean_inc(v_size_325_);
return v_size_325_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_unsigned_to_nat(0u);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___boxed(lean_object* v_00_u03b1_327_, lean_object* v_cmp_328_, lean_object* v_t_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_TreeSet_size(v_00_u03b1_327_, v_cmp_328_, v_t_329_);
lean_dec(v_t_329_);
lean_dec_ref(v_cmp_328_);
return v_res_330_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_isEmpty___redArg(lean_object* v_t_331_){
_start:
{
if (lean_obj_tag(v_t_331_) == 0)
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
else
{
uint8_t v___x_333_; 
v___x_333_ = 1;
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___redArg___boxed(lean_object* v_t_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Std_TreeSet_isEmpty___redArg(v_t_334_);
lean_dec(v_t_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_isEmpty(lean_object* v_00_u03b1_337_, lean_object* v_cmp_338_, lean_object* v_t_339_){
_start:
{
if (lean_obj_tag(v_t_339_) == 0)
{
uint8_t v___x_340_; 
v___x_340_ = 0;
return v___x_340_;
}
else
{
uint8_t v___x_341_; 
v___x_341_ = 1;
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___boxed(lean_object* v_00_u03b1_342_, lean_object* v_cmp_343_, lean_object* v_t_344_){
_start:
{
uint8_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = l_Std_TreeSet_isEmpty(v_00_u03b1_342_, v_cmp_343_, v_t_344_);
lean_dec(v_t_344_);
lean_dec_ref(v_cmp_343_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_erase___redArg(lean_object* v_cmp_347_, lean_object* v_t_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_347_, v_a_349_, v_t_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_erase(lean_object* v_00_u03b1_351_, lean_object* v_cmp_352_, lean_object* v_t_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_352_, v_a_354_, v_t_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f___redArg(lean_object* v_cmp_356_, lean_object* v_t_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_356_, v_t_357_, v_a_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f(lean_object* v_00_u03b1_360_, lean_object* v_cmp_361_, lean_object* v_t_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_361_, v_t_362_, v_a_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get___redArg(lean_object* v_cmp_365_, lean_object* v_t_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_365_, v_t_366_, v_a_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get(lean_object* v_00_u03b1_369_, lean_object* v_cmp_370_, lean_object* v_t_371_, lean_object* v_a_372_, lean_object* v_h_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_370_, v_t_371_, v_a_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___redArg(lean_object* v_cmp_375_, lean_object* v_inst_376_, lean_object* v_t_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_375_, v_t_377_, v_a_378_, v_inst_376_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___redArg___boxed(lean_object* v_cmp_380_, lean_object* v_inst_381_, lean_object* v_t_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_TreeSet_get_x21___redArg(v_cmp_380_, v_inst_381_, v_t_382_, v_a_383_);
lean_dec(v_inst_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21(lean_object* v_00_u03b1_385_, lean_object* v_cmp_386_, lean_object* v_inst_387_, lean_object* v_t_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_386_, v_t_388_, v_a_389_, v_inst_387_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___boxed(lean_object* v_00_u03b1_391_, lean_object* v_cmp_392_, lean_object* v_inst_393_, lean_object* v_t_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_TreeSet_get_x21(v_00_u03b1_391_, v_cmp_392_, v_inst_393_, v_t_394_, v_a_395_);
lean_dec(v_inst_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg(lean_object* v_cmp_397_, lean_object* v_t_398_, lean_object* v_a_399_, lean_object* v_fallback_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_397_, v_t_398_, v_a_399_, v_fallback_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg___boxed(lean_object* v_cmp_402_, lean_object* v_t_403_, lean_object* v_a_404_, lean_object* v_fallback_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_TreeSet_getD___redArg(v_cmp_402_, v_t_403_, v_a_404_, v_fallback_405_);
lean_dec(v_fallback_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD(lean_object* v_00_u03b1_407_, lean_object* v_cmp_408_, lean_object* v_t_409_, lean_object* v_a_410_, lean_object* v_fallback_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_408_, v_t_409_, v_a_410_, v_fallback_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___boxed(lean_object* v_00_u03b1_413_, lean_object* v_cmp_414_, lean_object* v_t_415_, lean_object* v_a_416_, lean_object* v_fallback_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_TreeSet_getD(v_00_u03b1_413_, v_cmp_414_, v_t_415_, v_a_416_, v_fallback_417_);
lean_dec(v_fallback_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg(lean_object* v_t_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg___boxed(lean_object* v_t_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Std_TreeSet_min_x3f___redArg(v_t_421_);
lean_dec(v_t_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f(lean_object* v_00_u03b1_423_, lean_object* v_cmp_424_, lean_object* v_t_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___boxed(lean_object* v_00_u03b1_427_, lean_object* v_cmp_428_, lean_object* v_t_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_TreeSet_min_x3f(v_00_u03b1_427_, v_cmp_428_, v_t_429_);
lean_dec(v_t_429_);
lean_dec_ref(v_cmp_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg(lean_object* v_t_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg___boxed(lean_object* v_t_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_TreeSet_min___redArg(v_t_433_);
lean_dec(v_t_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min(lean_object* v_00_u03b1_435_, lean_object* v_cmp_436_, lean_object* v_t_437_, lean_object* v_h_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_437_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___boxed(lean_object* v_00_u03b1_440_, lean_object* v_cmp_441_, lean_object* v_t_442_, lean_object* v_h_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_TreeSet_min(v_00_u03b1_440_, v_cmp_441_, v_t_442_, v_h_443_);
lean_dec(v_t_442_);
lean_dec_ref(v_cmp_441_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg(lean_object* v_inst_445_, lean_object* v_t_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_445_, v_t_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg___boxed(lean_object* v_inst_448_, lean_object* v_t_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_TreeSet_min_x21___redArg(v_inst_448_, v_t_449_);
lean_dec(v_t_449_);
lean_dec(v_inst_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21(lean_object* v_00_u03b1_451_, lean_object* v_cmp_452_, lean_object* v_inst_453_, lean_object* v_t_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_453_, v_t_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___boxed(lean_object* v_00_u03b1_456_, lean_object* v_cmp_457_, lean_object* v_inst_458_, lean_object* v_t_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_TreeSet_min_x21(v_00_u03b1_456_, v_cmp_457_, v_inst_458_, v_t_459_);
lean_dec(v_t_459_);
lean_dec(v_inst_458_);
lean_dec_ref(v_cmp_457_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg(lean_object* v_t_461_, lean_object* v_fallback_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_461_, v_fallback_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg___boxed(lean_object* v_t_464_, lean_object* v_fallback_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_TreeSet_minD___redArg(v_t_464_, v_fallback_465_);
lean_dec(v_fallback_465_);
lean_dec(v_t_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD(lean_object* v_00_u03b1_467_, lean_object* v_cmp_468_, lean_object* v_t_469_, lean_object* v_fallback_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_469_, v_fallback_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___boxed(lean_object* v_00_u03b1_472_, lean_object* v_cmp_473_, lean_object* v_t_474_, lean_object* v_fallback_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_TreeSet_minD(v_00_u03b1_472_, v_cmp_473_, v_t_474_, v_fallback_475_);
lean_dec(v_fallback_475_);
lean_dec(v_t_474_);
lean_dec_ref(v_cmp_473_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg(lean_object* v_t_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg___boxed(lean_object* v_t_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_TreeSet_max_x3f___redArg(v_t_479_);
lean_dec(v_t_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f(lean_object* v_00_u03b1_481_, lean_object* v_cmp_482_, lean_object* v_t_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___boxed(lean_object* v_00_u03b1_485_, lean_object* v_cmp_486_, lean_object* v_t_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_TreeSet_max_x3f(v_00_u03b1_485_, v_cmp_486_, v_t_487_);
lean_dec(v_t_487_);
lean_dec_ref(v_cmp_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg(lean_object* v_t_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg___boxed(lean_object* v_t_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_TreeSet_max___redArg(v_t_491_);
lean_dec(v_t_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max(lean_object* v_00_u03b1_493_, lean_object* v_cmp_494_, lean_object* v_t_495_, lean_object* v_h_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___boxed(lean_object* v_00_u03b1_498_, lean_object* v_cmp_499_, lean_object* v_t_500_, lean_object* v_h_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_TreeSet_max(v_00_u03b1_498_, v_cmp_499_, v_t_500_, v_h_501_);
lean_dec(v_t_500_);
lean_dec_ref(v_cmp_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg(lean_object* v_inst_503_, lean_object* v_t_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_503_, v_t_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg___boxed(lean_object* v_inst_506_, lean_object* v_t_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_TreeSet_max_x21___redArg(v_inst_506_, v_t_507_);
lean_dec(v_t_507_);
lean_dec(v_inst_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21(lean_object* v_00_u03b1_509_, lean_object* v_cmp_510_, lean_object* v_inst_511_, lean_object* v_t_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_511_, v_t_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___boxed(lean_object* v_00_u03b1_514_, lean_object* v_cmp_515_, lean_object* v_inst_516_, lean_object* v_t_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_TreeSet_max_x21(v_00_u03b1_514_, v_cmp_515_, v_inst_516_, v_t_517_);
lean_dec(v_t_517_);
lean_dec(v_inst_516_);
lean_dec_ref(v_cmp_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg(lean_object* v_t_519_, lean_object* v_fallback_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_519_, v_fallback_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg___boxed(lean_object* v_t_522_, lean_object* v_fallback_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_TreeSet_maxD___redArg(v_t_522_, v_fallback_523_);
lean_dec(v_fallback_523_);
lean_dec(v_t_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD(lean_object* v_00_u03b1_525_, lean_object* v_cmp_526_, lean_object* v_t_527_, lean_object* v_fallback_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_527_, v_fallback_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___boxed(lean_object* v_00_u03b1_530_, lean_object* v_cmp_531_, lean_object* v_t_532_, lean_object* v_fallback_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_TreeSet_maxD(v_00_u03b1_530_, v_cmp_531_, v_t_532_, v_fallback_533_);
lean_dec(v_fallback_533_);
lean_dec(v_t_532_);
lean_dec_ref(v_cmp_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg(lean_object* v_t_535_, lean_object* v_n_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_535_, v_n_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg___boxed(lean_object* v_t_538_, lean_object* v_n_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_TreeSet_atIdx_x3f___redArg(v_t_538_, v_n_539_);
lean_dec(v_t_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f(lean_object* v_00_u03b1_541_, lean_object* v_cmp_542_, lean_object* v_t_543_, lean_object* v_n_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_543_, v_n_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___boxed(lean_object* v_00_u03b1_546_, lean_object* v_cmp_547_, lean_object* v_t_548_, lean_object* v_n_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_TreeSet_atIdx_x3f(v_00_u03b1_546_, v_cmp_547_, v_t_548_, v_n_549_);
lean_dec(v_t_548_);
lean_dec_ref(v_cmp_547_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg(lean_object* v_t_551_, lean_object* v_n_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_551_, v_n_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg___boxed(lean_object* v_t_554_, lean_object* v_n_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_TreeSet_atIdx___redArg(v_t_554_, v_n_555_);
lean_dec(v_t_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx(lean_object* v_00_u03b1_557_, lean_object* v_cmp_558_, lean_object* v_t_559_, lean_object* v_n_560_, lean_object* v_h_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_559_, v_n_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___boxed(lean_object* v_00_u03b1_563_, lean_object* v_cmp_564_, lean_object* v_t_565_, lean_object* v_n_566_, lean_object* v_h_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_TreeSet_atIdx(v_00_u03b1_563_, v_cmp_564_, v_t_565_, v_n_566_, v_h_567_);
lean_dec(v_t_565_);
lean_dec_ref(v_cmp_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg(lean_object* v_inst_569_, lean_object* v_t_570_, lean_object* v_n_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_569_, v_t_570_, v_n_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg___boxed(lean_object* v_inst_573_, lean_object* v_t_574_, lean_object* v_n_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_TreeSet_atIdx_x21___redArg(v_inst_573_, v_t_574_, v_n_575_);
lean_dec(v_t_574_);
lean_dec(v_inst_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21(lean_object* v_00_u03b1_577_, lean_object* v_cmp_578_, lean_object* v_inst_579_, lean_object* v_t_580_, lean_object* v_n_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_579_, v_t_580_, v_n_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___boxed(lean_object* v_00_u03b1_583_, lean_object* v_cmp_584_, lean_object* v_inst_585_, lean_object* v_t_586_, lean_object* v_n_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_TreeSet_atIdx_x21(v_00_u03b1_583_, v_cmp_584_, v_inst_585_, v_t_586_, v_n_587_);
lean_dec(v_t_586_);
lean_dec(v_inst_585_);
lean_dec_ref(v_cmp_584_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg(lean_object* v_t_589_, lean_object* v_n_590_, lean_object* v_fallback_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_589_, v_n_590_, v_fallback_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg___boxed(lean_object* v_t_593_, lean_object* v_n_594_, lean_object* v_fallback_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_TreeSet_atIdxD___redArg(v_t_593_, v_n_594_, v_fallback_595_);
lean_dec(v_fallback_595_);
lean_dec(v_t_593_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD(lean_object* v_00_u03b1_597_, lean_object* v_cmp_598_, lean_object* v_t_599_, lean_object* v_n_600_, lean_object* v_fallback_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_599_, v_n_600_, v_fallback_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___boxed(lean_object* v_00_u03b1_603_, lean_object* v_cmp_604_, lean_object* v_t_605_, lean_object* v_n_606_, lean_object* v_fallback_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_TreeSet_atIdxD(v_00_u03b1_603_, v_cmp_604_, v_t_605_, v_n_606_, v_fallback_607_);
lean_dec(v_fallback_607_);
lean_dec(v_t_605_);
lean_dec_ref(v_cmp_604_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f___redArg(lean_object* v_cmp_609_, lean_object* v_t_610_, lean_object* v_k_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_box(0);
v___x_613_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_609_, v_k_611_, v___x_612_, v_t_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f(lean_object* v_00_u03b1_614_, lean_object* v_cmp_615_, lean_object* v_t_616_, lean_object* v_k_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_box(0);
v___x_619_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_615_, v_k_617_, v___x_618_, v_t_616_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f___redArg(lean_object* v_cmp_620_, lean_object* v_t_621_, lean_object* v_k_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_box(0);
v___x_624_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_620_, v_k_622_, v___x_623_, v_t_621_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f(lean_object* v_00_u03b1_625_, lean_object* v_cmp_626_, lean_object* v_t_627_, lean_object* v_k_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_box(0);
v___x_630_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_626_, v_k_628_, v___x_629_, v_t_627_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f___redArg(lean_object* v_cmp_631_, lean_object* v_t_632_, lean_object* v_k_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_box(0);
v___x_635_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_631_, v_k_633_, v___x_634_, v_t_632_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f(lean_object* v_00_u03b1_636_, lean_object* v_cmp_637_, lean_object* v_t_638_, lean_object* v_k_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_box(0);
v___x_641_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_637_, v_k_639_, v___x_640_, v_t_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f___redArg(lean_object* v_cmp_642_, lean_object* v_t_643_, lean_object* v_k_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box(0);
v___x_646_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_642_, v_k_644_, v___x_645_, v_t_643_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f(lean_object* v_00_u03b1_647_, lean_object* v_cmp_648_, lean_object* v_t_649_, lean_object* v_k_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_box(0);
v___x_652_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_648_, v_k_650_, v___x_651_, v_t_649_);
return v___x_652_;
}
}
static lean_object* _init_l_Std_TreeSet_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__2));
v___x_657_ = lean_unsigned_to_nat(14u);
v___x_658_ = lean_unsigned_to_nat(22u);
v___x_659_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__1));
v___x_660_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__0));
v___x_661_ = l_mkPanicMessageWithDecl(v___x_660_, v___x_659_, v___x_658_, v___x_657_, v___x_656_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___redArg(lean_object* v_cmp_662_, lean_object* v_inst_663_, lean_object* v_t_664_, lean_object* v_k_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_box(0);
v___x_667_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_662_, v_k_665_, v___x_666_, v_t_664_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_669_ = l_panic___redArg(v_inst_663_, v___x_668_);
return v___x_669_;
}
else
{
lean_object* v_val_670_; 
v_val_670_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_670_);
lean_dec_ref(v___x_667_);
return v_val_670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___redArg___boxed(lean_object* v_cmp_671_, lean_object* v_inst_672_, lean_object* v_t_673_, lean_object* v_k_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_TreeSet_getGE_x21___redArg(v_cmp_671_, v_inst_672_, v_t_673_, v_k_674_);
lean_dec(v_inst_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21(lean_object* v_00_u03b1_676_, lean_object* v_cmp_677_, lean_object* v_inst_678_, lean_object* v_t_679_, lean_object* v_k_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_box(0);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_677_, v_k_680_, v___x_681_, v_t_679_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___boxed(lean_object* v_00_u03b1_686_, lean_object* v_cmp_687_, lean_object* v_inst_688_, lean_object* v_t_689_, lean_object* v_k_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_TreeSet_getGE_x21(v_00_u03b1_686_, v_cmp_687_, v_inst_688_, v_t_689_, v_k_690_);
lean_dec(v_inst_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg(lean_object* v_cmp_692_, lean_object* v_inst_693_, lean_object* v_t_694_, lean_object* v_k_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_box(0);
v___x_697_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_692_, v_k_695_, v___x_696_, v_t_694_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_699_ = l_panic___redArg(v_inst_693_, v___x_698_);
return v___x_699_;
}
else
{
lean_object* v_val_700_; 
v_val_700_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_val_700_);
lean_dec_ref(v___x_697_);
return v_val_700_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg___boxed(lean_object* v_cmp_701_, lean_object* v_inst_702_, lean_object* v_t_703_, lean_object* v_k_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Std_TreeSet_getGT_x21___redArg(v_cmp_701_, v_inst_702_, v_t_703_, v_k_704_);
lean_dec(v_inst_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21(lean_object* v_00_u03b1_706_, lean_object* v_cmp_707_, lean_object* v_inst_708_, lean_object* v_t_709_, lean_object* v_k_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_box(0);
v___x_712_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_707_, v_k_710_, v___x_711_, v_t_709_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_714_ = l_panic___redArg(v_inst_708_, v___x_713_);
return v___x_714_;
}
else
{
lean_object* v_val_715_; 
v_val_715_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_val_715_);
lean_dec_ref(v___x_712_);
return v_val_715_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___boxed(lean_object* v_00_u03b1_716_, lean_object* v_cmp_717_, lean_object* v_inst_718_, lean_object* v_t_719_, lean_object* v_k_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_TreeSet_getGT_x21(v_00_u03b1_716_, v_cmp_717_, v_inst_718_, v_t_719_, v_k_720_);
lean_dec(v_inst_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg(lean_object* v_cmp_722_, lean_object* v_inst_723_, lean_object* v_t_724_, lean_object* v_k_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_box(0);
v___x_727_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_722_, v_k_725_, v___x_726_, v_t_724_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_729_ = l_panic___redArg(v_inst_723_, v___x_728_);
return v___x_729_;
}
else
{
lean_object* v_val_730_; 
v_val_730_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_val_730_);
lean_dec_ref(v___x_727_);
return v_val_730_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg___boxed(lean_object* v_cmp_731_, lean_object* v_inst_732_, lean_object* v_t_733_, lean_object* v_k_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_TreeSet_getLE_x21___redArg(v_cmp_731_, v_inst_732_, v_t_733_, v_k_734_);
lean_dec(v_inst_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21(lean_object* v_00_u03b1_736_, lean_object* v_cmp_737_, lean_object* v_inst_738_, lean_object* v_t_739_, lean_object* v_k_740_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_box(0);
v___x_742_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_737_, v_k_740_, v___x_741_, v_t_739_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_744_ = l_panic___redArg(v_inst_738_, v___x_743_);
return v___x_744_;
}
else
{
lean_object* v_val_745_; 
v_val_745_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_val_745_);
lean_dec_ref(v___x_742_);
return v_val_745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___boxed(lean_object* v_00_u03b1_746_, lean_object* v_cmp_747_, lean_object* v_inst_748_, lean_object* v_t_749_, lean_object* v_k_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_TreeSet_getLE_x21(v_00_u03b1_746_, v_cmp_747_, v_inst_748_, v_t_749_, v_k_750_);
lean_dec(v_inst_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg(lean_object* v_cmp_752_, lean_object* v_inst_753_, lean_object* v_t_754_, lean_object* v_k_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_box(0);
v___x_757_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_752_, v_k_755_, v___x_756_, v_t_754_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_759_ = l_panic___redArg(v_inst_753_, v___x_758_);
return v___x_759_;
}
else
{
lean_object* v_val_760_; 
v_val_760_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_val_760_);
lean_dec_ref(v___x_757_);
return v_val_760_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg___boxed(lean_object* v_cmp_761_, lean_object* v_inst_762_, lean_object* v_t_763_, lean_object* v_k_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_TreeSet_getLT_x21___redArg(v_cmp_761_, v_inst_762_, v_t_763_, v_k_764_);
lean_dec(v_inst_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21(lean_object* v_00_u03b1_766_, lean_object* v_cmp_767_, lean_object* v_inst_768_, lean_object* v_t_769_, lean_object* v_k_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_box(0);
v___x_772_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_767_, v_k_770_, v___x_771_, v_t_769_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_774_ = l_panic___redArg(v_inst_768_, v___x_773_);
return v___x_774_;
}
else
{
lean_object* v_val_775_; 
v_val_775_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_val_775_);
lean_dec_ref(v___x_772_);
return v_val_775_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___boxed(lean_object* v_00_u03b1_776_, lean_object* v_cmp_777_, lean_object* v_inst_778_, lean_object* v_t_779_, lean_object* v_k_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_TreeSet_getLT_x21(v_00_u03b1_776_, v_cmp_777_, v_inst_778_, v_t_779_, v_k_780_);
lean_dec(v_inst_778_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg(lean_object* v_cmp_782_, lean_object* v_t_783_, lean_object* v_k_784_, lean_object* v_fallback_785_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_box(0);
v___x_787_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_782_, v_k_784_, v___x_786_, v_t_783_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_inc(v_fallback_785_);
return v_fallback_785_;
}
else
{
lean_object* v_val_788_; 
v_val_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_val_788_);
lean_dec_ref(v___x_787_);
return v_val_788_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg___boxed(lean_object* v_cmp_789_, lean_object* v_t_790_, lean_object* v_k_791_, lean_object* v_fallback_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_TreeSet_getGED___redArg(v_cmp_789_, v_t_790_, v_k_791_, v_fallback_792_);
lean_dec(v_fallback_792_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED(lean_object* v_00_u03b1_794_, lean_object* v_cmp_795_, lean_object* v_t_796_, lean_object* v_k_797_, lean_object* v_fallback_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_box(0);
v___x_800_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_795_, v_k_797_, v___x_799_, v_t_796_);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___boxed(lean_object* v_00_u03b1_802_, lean_object* v_cmp_803_, lean_object* v_t_804_, lean_object* v_k_805_, lean_object* v_fallback_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_TreeSet_getGED(v_00_u03b1_802_, v_cmp_803_, v_t_804_, v_k_805_, v_fallback_806_);
lean_dec(v_fallback_806_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg(lean_object* v_cmp_808_, lean_object* v_t_809_, lean_object* v_k_810_, lean_object* v_fallback_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_box(0);
v___x_813_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_808_, v_k_810_, v___x_812_, v_t_809_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_inc(v_fallback_811_);
return v_fallback_811_;
}
else
{
lean_object* v_val_814_; 
v_val_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_val_814_);
lean_dec_ref(v___x_813_);
return v_val_814_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg___boxed(lean_object* v_cmp_815_, lean_object* v_t_816_, lean_object* v_k_817_, lean_object* v_fallback_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_TreeSet_getGTD___redArg(v_cmp_815_, v_t_816_, v_k_817_, v_fallback_818_);
lean_dec(v_fallback_818_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD(lean_object* v_00_u03b1_820_, lean_object* v_cmp_821_, lean_object* v_t_822_, lean_object* v_k_823_, lean_object* v_fallback_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_box(0);
v___x_826_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_821_, v_k_823_, v___x_825_, v_t_822_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_inc(v_fallback_824_);
return v_fallback_824_;
}
else
{
lean_object* v_val_827_; 
v_val_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_val_827_);
lean_dec_ref(v___x_826_);
return v_val_827_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___boxed(lean_object* v_00_u03b1_828_, lean_object* v_cmp_829_, lean_object* v_t_830_, lean_object* v_k_831_, lean_object* v_fallback_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_TreeSet_getGTD(v_00_u03b1_828_, v_cmp_829_, v_t_830_, v_k_831_, v_fallback_832_);
lean_dec(v_fallback_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg(lean_object* v_cmp_834_, lean_object* v_t_835_, lean_object* v_k_836_, lean_object* v_fallback_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_box(0);
v___x_839_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_834_, v_k_836_, v___x_838_, v_t_835_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_inc(v_fallback_837_);
return v_fallback_837_;
}
else
{
lean_object* v_val_840_; 
v_val_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_val_840_);
lean_dec_ref(v___x_839_);
return v_val_840_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg___boxed(lean_object* v_cmp_841_, lean_object* v_t_842_, lean_object* v_k_843_, lean_object* v_fallback_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_TreeSet_getLED___redArg(v_cmp_841_, v_t_842_, v_k_843_, v_fallback_844_);
lean_dec(v_fallback_844_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED(lean_object* v_00_u03b1_846_, lean_object* v_cmp_847_, lean_object* v_t_848_, lean_object* v_k_849_, lean_object* v_fallback_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_box(0);
v___x_852_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_847_, v_k_849_, v___x_851_, v_t_848_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_inc(v_fallback_850_);
return v_fallback_850_;
}
else
{
lean_object* v_val_853_; 
v_val_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_val_853_);
lean_dec_ref(v___x_852_);
return v_val_853_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___boxed(lean_object* v_00_u03b1_854_, lean_object* v_cmp_855_, lean_object* v_t_856_, lean_object* v_k_857_, lean_object* v_fallback_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_TreeSet_getLED(v_00_u03b1_854_, v_cmp_855_, v_t_856_, v_k_857_, v_fallback_858_);
lean_dec(v_fallback_858_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg(lean_object* v_cmp_860_, lean_object* v_t_861_, lean_object* v_k_862_, lean_object* v_fallback_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_box(0);
v___x_865_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_860_, v_k_862_, v___x_864_, v_t_861_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_inc(v_fallback_863_);
return v_fallback_863_;
}
else
{
lean_object* v_val_866_; 
v_val_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_val_866_);
lean_dec_ref(v___x_865_);
return v_val_866_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg___boxed(lean_object* v_cmp_867_, lean_object* v_t_868_, lean_object* v_k_869_, lean_object* v_fallback_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_TreeSet_getLTD___redArg(v_cmp_867_, v_t_868_, v_k_869_, v_fallback_870_);
lean_dec(v_fallback_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD(lean_object* v_00_u03b1_872_, lean_object* v_cmp_873_, lean_object* v_t_874_, lean_object* v_k_875_, lean_object* v_fallback_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_box(0);
v___x_878_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_873_, v_k_875_, v___x_877_, v_t_874_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_inc(v_fallback_876_);
return v_fallback_876_;
}
else
{
lean_object* v_val_879_; 
v_val_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_val_879_);
lean_dec_ref(v___x_878_);
return v_val_879_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___boxed(lean_object* v_00_u03b1_880_, lean_object* v_cmp_881_, lean_object* v_t_882_, lean_object* v_k_883_, lean_object* v_fallback_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_TreeSet_getLTD(v_00_u03b1_880_, v_cmp_881_, v_t_882_, v_k_883_, v_fallback_884_);
lean_dec(v_fallback_884_);
return v_res_885_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_filter___redArg___lam__0(lean_object* v_f_886_, lean_object* v_a_887_, lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = lean_apply_1(v_f_886_, v_a_887_);
v___x_890_ = lean_unbox(v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg___lam__0___boxed(lean_object* v_f_891_, lean_object* v_a_892_, lean_object* v_x_893_){
_start:
{
uint8_t v_res_894_; lean_object* v_r_895_; 
v_res_894_ = l_Std_TreeSet_filter___redArg___lam__0(v_f_891_, v_a_892_, v_x_893_);
v_r_895_ = lean_box(v_res_894_);
return v_r_895_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg(lean_object* v_f_896_, lean_object* v_m_897_){
_start:
{
lean_object* v___f_898_; lean_object* v___x_899_; 
v___f_898_ = lean_alloc_closure((void*)(l_Std_TreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_898_, 0, v_f_896_);
v___x_899_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_898_, v_m_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter(lean_object* v_00_u03b1_900_, lean_object* v_cmp_901_, lean_object* v_f_902_, lean_object* v_m_903_){
_start:
{
lean_object* v___f_904_; lean_object* v___x_905_; 
v___f_904_ = lean_alloc_closure((void*)(l_Std_TreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_904_, 0, v_f_902_);
v___x_905_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_904_, v_m_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___boxed(lean_object* v_00_u03b1_906_, lean_object* v_cmp_907_, lean_object* v_f_908_, lean_object* v_m_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Std_TreeSet_filter(v_00_u03b1_906_, v_cmp_907_, v_f_908_, v_m_909_);
lean_dec_ref(v_cmp_907_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg___lam__0(lean_object* v_f_911_, lean_object* v_c_912_, lean_object* v_a_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_apply_2(v_f_911_, v_c_912_, v_a_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg(lean_object* v_inst_916_, lean_object* v_f_917_, lean_object* v_init_918_, lean_object* v_t_919_){
_start:
{
lean_object* v___f_920_; lean_object* v___x_921_; 
v___f_920_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_920_, 0, v_f_917_);
v___x_921_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_916_, v___f_920_, v_init_918_, v_t_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM(lean_object* v_00_u03b1_922_, lean_object* v_cmp_923_, lean_object* v_m_924_, lean_object* v_00_u03b4_925_, lean_object* v_inst_926_, lean_object* v_f_927_, lean_object* v_init_928_, lean_object* v_t_929_){
_start:
{
lean_object* v___f_930_; lean_object* v___x_931_; 
v___f_930_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_930_, 0, v_f_927_);
v___x_931_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_926_, v___f_930_, v_init_928_, v_t_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___boxed(lean_object* v_00_u03b1_932_, lean_object* v_cmp_933_, lean_object* v_m_934_, lean_object* v_00_u03b4_935_, lean_object* v_inst_936_, lean_object* v_f_937_, lean_object* v_init_938_, lean_object* v_t_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Std_TreeSet_foldlM(v_00_u03b1_932_, v_cmp_933_, v_m_934_, v_00_u03b4_935_, v_inst_936_, v_f_937_, v_init_938_, v_t_939_);
lean_dec_ref(v_cmp_933_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___redArg(lean_object* v_f_941_, lean_object* v_init_942_, lean_object* v_t_943_){
_start:
{
lean_object* v___f_944_; lean_object* v___x_945_; 
v___f_944_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_944_, 0, v_f_941_);
v___x_945_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_944_, v_init_942_, v_t_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl(lean_object* v_00_u03b1_946_, lean_object* v_cmp_947_, lean_object* v_00_u03b4_948_, lean_object* v_f_949_, lean_object* v_init_950_, lean_object* v_t_951_){
_start:
{
lean_object* v___f_952_; lean_object* v___x_953_; 
v___f_952_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_952_, 0, v_f_949_);
v___x_953_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_952_, v_init_950_, v_t_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___boxed(lean_object* v_00_u03b1_954_, lean_object* v_cmp_955_, lean_object* v_00_u03b4_956_, lean_object* v_f_957_, lean_object* v_init_958_, lean_object* v_t_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Std_TreeSet_foldl(v_00_u03b1_954_, v_cmp_955_, v_00_u03b4_956_, v_f_957_, v_init_958_, v_t_959_);
lean_dec_ref(v_cmp_955_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg___lam__0(lean_object* v_f_961_, lean_object* v_a_962_, lean_object* v_x_963_, lean_object* v_acc_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = lean_apply_2(v_f_961_, v_a_962_, v_acc_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg(lean_object* v_inst_966_, lean_object* v_f_967_, lean_object* v_init_968_, lean_object* v_t_969_){
_start:
{
lean_object* v___f_970_; lean_object* v___x_971_; 
v___f_970_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_970_, 0, v_f_967_);
v___x_971_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_966_, v___f_970_, v_init_968_, v_t_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM(lean_object* v_00_u03b1_972_, lean_object* v_cmp_973_, lean_object* v_m_974_, lean_object* v_00_u03b4_975_, lean_object* v_inst_976_, lean_object* v_f_977_, lean_object* v_init_978_, lean_object* v_t_979_){
_start:
{
lean_object* v___f_980_; lean_object* v___x_981_; 
v___f_980_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_980_, 0, v_f_977_);
v___x_981_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_976_, v___f_980_, v_init_978_, v_t_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___boxed(lean_object* v_00_u03b1_982_, lean_object* v_cmp_983_, lean_object* v_m_984_, lean_object* v_00_u03b4_985_, lean_object* v_inst_986_, lean_object* v_f_987_, lean_object* v_init_988_, lean_object* v_t_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Std_TreeSet_foldrM(v_00_u03b1_982_, v_cmp_983_, v_m_984_, v_00_u03b4_985_, v_inst_986_, v_f_987_, v_init_988_, v_t_989_);
lean_dec_ref(v_cmp_983_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg___lam__0(lean_object* v_f_991_, lean_object* v_x1_992_, lean_object* v_x2_993_, lean_object* v_x3_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = lean_apply_2(v_f_991_, v_x1_992_, v_x3_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg(lean_object* v_f_1015_, lean_object* v_init_1016_, lean_object* v_t_1017_){
_start:
{
lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___f_1018_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1018_, 0, v_f_1015_);
v___x_1019_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1020_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1019_, v___f_1018_, v_init_1016_, v_t_1017_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr(lean_object* v_00_u03b1_1021_, lean_object* v_cmp_1022_, lean_object* v_00_u03b4_1023_, lean_object* v_f_1024_, lean_object* v_init_1025_, lean_object* v_t_1026_){
_start:
{
lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___f_1027_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1027_, 0, v_f_1024_);
v___x_1028_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1029_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1028_, v___f_1027_, v_init_1025_, v_t_1026_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___boxed(lean_object* v_00_u03b1_1030_, lean_object* v_cmp_1031_, lean_object* v_00_u03b4_1032_, lean_object* v_f_1033_, lean_object* v_init_1034_, lean_object* v_t_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Std_TreeSet_foldr(v_00_u03b1_1030_, v_cmp_1031_, v_00_u03b4_1032_, v_f_1033_, v_init_1034_, v_t_1035_);
lean_dec_ref(v_cmp_1031_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg___lam__0(lean_object* v_f_1037_, lean_object* v_cmp_1038_, lean_object* v_x_1039_, lean_object* v_a_1040_, lean_object* v_b_1041_){
_start:
{
lean_object* v_fst_1042_; lean_object* v_snd_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1057_; 
v_fst_1042_ = lean_ctor_get(v_x_1039_, 0);
v_snd_1043_ = lean_ctor_get(v_x_1039_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_x_1039_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1045_ = v_x_1039_;
v_isShared_1046_ = v_isSharedCheck_1057_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_snd_1043_);
lean_inc(v_fst_1042_);
lean_dec(v_x_1039_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1057_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; uint8_t v___x_1048_; 
lean_inc(v_a_1040_);
v___x_1047_ = lean_apply_1(v_f_1037_, v_a_1040_);
v___x_1048_ = lean_unbox(v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1038_, v_a_1040_, v_b_1041_, v_snd_1043_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 1, v___x_1049_);
v___x_1051_ = v___x_1045_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_fst_1042_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1038_, v_a_1040_, v_b_1041_, v_fst_1042_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1053_);
v___x_1055_ = v___x_1045_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_snd_1043_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg(lean_object* v_cmp_1060_, lean_object* v_f_1061_, lean_object* v_t_1062_){
_start:
{
lean_object* v___f_1063_; lean_object* v___x_1064_; lean_object* v_p_1065_; lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v___f_1063_ = lean_alloc_closure((void*)(l_Std_TreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1063_, 0, v_f_1061_);
lean_closure_set(v___f_1063_, 1, v_cmp_1060_);
v___x_1064_ = ((lean_object*)(l_Std_TreeSet_partition___redArg___closed__0));
v_p_1065_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1063_, v___x_1064_, v_t_1062_);
v_fst_1066_ = lean_ctor_get(v_p_1065_, 0);
v_snd_1067_ = lean_ctor_get(v_p_1065_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_p_1065_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v_p_1065_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_snd_1067_);
lean_inc(v_fst_1066_);
lean_dec(v_p_1065_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_fst_1066_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_snd_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition(lean_object* v_00_u03b1_1075_, lean_object* v_cmp_1076_, lean_object* v_f_1077_, lean_object* v_t_1078_){
_start:
{
lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v_p_1081_; lean_object* v_fst_1082_; lean_object* v_snd_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v___f_1079_ = lean_alloc_closure((void*)(l_Std_TreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1079_, 0, v_f_1077_);
lean_closure_set(v___f_1079_, 1, v_cmp_1076_);
v___x_1080_ = ((lean_object*)(l_Std_TreeSet_partition___redArg___closed__0));
v_p_1081_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1079_, v___x_1080_, v_t_1078_);
v_fst_1082_ = lean_ctor_get(v_p_1081_, 0);
v_snd_1083_ = lean_ctor_get(v_p_1081_, 1);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_p_1081_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v_p_1081_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_snd_1083_);
lean_inc(v_fst_1082_);
lean_dec(v_p_1081_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_fst_1082_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_snd_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg___lam__0(lean_object* v_f_1091_, lean_object* v_x_1092_, lean_object* v_k_1093_, lean_object* v_v_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_apply_1(v_f_1091_, v_k_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg(lean_object* v_inst_1096_, lean_object* v_f_1097_, lean_object* v_t_1098_){
_start:
{
lean_object* v___f_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___f_1099_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1099_, 0, v_f_1097_);
v___x_1100_ = lean_box(0);
v___x_1101_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1096_, v___f_1099_, v___x_1100_, v_t_1098_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM(lean_object* v_00_u03b1_1102_, lean_object* v_cmp_1103_, lean_object* v_m_1104_, lean_object* v_inst_1105_, lean_object* v_f_1106_, lean_object* v_t_1107_){
_start:
{
lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___f_1108_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1108_, 0, v_f_1106_);
v___x_1109_ = lean_box(0);
v___x_1110_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1105_, v___f_1108_, v___x_1109_, v_t_1107_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___boxed(lean_object* v_00_u03b1_1111_, lean_object* v_cmp_1112_, lean_object* v_m_1113_, lean_object* v_inst_1114_, lean_object* v_f_1115_, lean_object* v_t_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_TreeSet_forM(v_00_u03b1_1111_, v_cmp_1112_, v_m_1113_, v_inst_1114_, v_f_1115_, v_t_1116_);
lean_dec_ref(v_cmp_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__0(lean_object* v_f_1118_, lean_object* v_a_1119_, lean_object* v_b_1120_, lean_object* v_c_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_apply_2(v_f_1118_, v_a_1119_, v_c_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__1(lean_object* v_toPure_1123_, lean_object* v_____do__lift_1124_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg(lean_object* v_inst_1127_, lean_object* v_f_1128_, lean_object* v_init_1129_, lean_object* v_t_1130_){
_start:
{
lean_object* v_toApplicative_1131_; lean_object* v_toBind_1132_; lean_object* v_toPure_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; 
v_toApplicative_1131_ = lean_ctor_get(v_inst_1127_, 0);
v_toBind_1132_ = lean_ctor_get(v_inst_1127_, 1);
lean_inc(v_toBind_1132_);
v_toPure_1133_ = lean_ctor_get(v_toApplicative_1131_, 1);
lean_inc(v_toPure_1133_);
v___f_1134_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1134_, 0, v_f_1128_);
v___x_1135_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1127_, v___f_1134_, v_init_1129_, v_t_1130_);
v___f_1136_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1136_, 0, v_toPure_1133_);
v___x_1137_ = lean_apply_4(v_toBind_1132_, lean_box(0), lean_box(0), v___x_1135_, v___f_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn(lean_object* v_00_u03b1_1138_, lean_object* v_cmp_1139_, lean_object* v_00_u03b4_1140_, lean_object* v_m_1141_, lean_object* v_inst_1142_, lean_object* v_f_1143_, lean_object* v_init_1144_, lean_object* v_t_1145_){
_start:
{
lean_object* v_toApplicative_1146_; lean_object* v_toBind_1147_; lean_object* v_toPure_1148_; lean_object* v___f_1149_; lean_object* v___x_1150_; lean_object* v___f_1151_; lean_object* v___x_1152_; 
v_toApplicative_1146_ = lean_ctor_get(v_inst_1142_, 0);
v_toBind_1147_ = lean_ctor_get(v_inst_1142_, 1);
lean_inc(v_toBind_1147_);
v_toPure_1148_ = lean_ctor_get(v_toApplicative_1146_, 1);
lean_inc(v_toPure_1148_);
v___f_1149_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1149_, 0, v_f_1143_);
v___x_1150_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1142_, v___f_1149_, v_init_1144_, v_t_1145_);
v___f_1151_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1151_, 0, v_toPure_1148_);
v___x_1152_ = lean_apply_4(v_toBind_1147_, lean_box(0), lean_box(0), v___x_1150_, v___f_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_cmp_1154_, lean_object* v_00_u03b4_1155_, lean_object* v_m_1156_, lean_object* v_inst_1157_, lean_object* v_f_1158_, lean_object* v_init_1159_, lean_object* v_t_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_TreeSet_forIn(v_00_u03b1_1153_, v_cmp_1154_, v_00_u03b4_1155_, v_m_1156_, v_inst_1157_, v_f_1158_, v_init_1159_, v_t_1160_);
lean_dec_ref(v_cmp_1154_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg___lam__1(lean_object* v_inst_1162_, lean_object* v_t_1163_, lean_object* v_f_1164_){
_start:
{
lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___f_1165_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1165_, 0, v_f_1164_);
v___x_1166_ = lean_box(0);
v___x_1167_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1162_, v___f_1165_, v___x_1166_, v_t_1163_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg(lean_object* v_inst_1168_){
_start:
{
lean_object* v___f_1169_; 
v___f_1169_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1169_, 0, v_inst_1168_);
return v___f_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad(lean_object* v_00_u03b1_1170_, lean_object* v_cmp_1171_, lean_object* v_m_1172_, lean_object* v_inst_1173_){
_start:
{
lean_object* v___f_1174_; 
v___f_1174_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1174_, 0, v_inst_1173_);
return v___f_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___boxed(lean_object* v_00_u03b1_1175_, lean_object* v_cmp_1176_, lean_object* v_m_1177_, lean_object* v_inst_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Std_TreeSet_instForMOfMonad(v_00_u03b1_1175_, v_cmp_1176_, v_m_1177_, v_inst_1178_);
lean_dec_ref(v_cmp_1176_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg___lam__2(lean_object* v_inst_1180_, lean_object* v_00_u03b2_1181_, lean_object* v_m_1182_, lean_object* v_init_1183_, lean_object* v_f_1184_){
_start:
{
lean_object* v_toApplicative_1185_; lean_object* v_toBind_1186_; lean_object* v_toPure_1187_; lean_object* v___f_1188_; lean_object* v___x_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; 
v_toApplicative_1185_ = lean_ctor_get(v_inst_1180_, 0);
v_toBind_1186_ = lean_ctor_get(v_inst_1180_, 1);
lean_inc(v_toBind_1186_);
v_toPure_1187_ = lean_ctor_get(v_toApplicative_1185_, 1);
lean_inc(v_toPure_1187_);
v___f_1188_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1188_, 0, v_f_1184_);
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1180_, v___f_1188_, v_init_1183_, v_m_1182_);
v___f_1190_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1190_, 0, v_toPure_1187_);
v___x_1191_ = lean_apply_4(v_toBind_1186_, lean_box(0), lean_box(0), v___x_1189_, v___f_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg(lean_object* v_inst_1192_){
_start:
{
lean_object* v___f_1193_; 
v___f_1193_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1193_, 0, v_inst_1192_);
return v___f_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad(lean_object* v_00_u03b1_1194_, lean_object* v_cmp_1195_, lean_object* v_m_1196_, lean_object* v_inst_1197_){
_start:
{
lean_object* v___f_1198_; 
v___f_1198_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1198_, 0, v_inst_1197_);
return v___f_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_1199_, lean_object* v_cmp_1200_, lean_object* v_m_1201_, lean_object* v_inst_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Std_TreeSet_instForInOfMonad(v_00_u03b1_1199_, v_cmp_1200_, v_m_1201_, v_inst_1202_);
lean_dec_ref(v_cmp_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0(lean_object* v_p_1204_, lean_object* v___x_1205_, lean_object* v___x_1206_, lean_object* v_a_1207_, lean_object* v_b_1208_, lean_object* v_acc_1209_){
_start:
{
lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = lean_apply_1(v_p_1204_, v_a_1207_);
v___x_1211_ = lean_unbox(v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1205_);
return v___x_1212_;
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec_ref(v___x_1205_);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1210_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v___x_1206_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0___boxed(lean_object* v_p_1216_, lean_object* v___x_1217_, lean_object* v___x_1218_, lean_object* v_a_1219_, lean_object* v_b_1220_, lean_object* v_acc_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_TreeSet_any___redArg___lam__0(v_p_1216_, v___x_1217_, v___x_1218_, v_a_1219_, v_b_1220_, v_acc_1221_);
lean_dec_ref(v_acc_1221_);
return v_res_1222_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_any___redArg(lean_object* v_t_1226_, lean_object* v_p_1227_){
_start:
{
lean_object* v___y_1229_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; lean_object* v_a_1239_; 
v___x_1234_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1235_ = lean_box(0);
v___x_1236_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1237_ = lean_alloc_closure((void*)(l_Std_TreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1237_, 0, v_p_1227_);
lean_closure_set(v___f_1237_, 1, v___x_1236_);
lean_closure_set(v___f_1237_, 2, v___x_1235_);
v___x_1238_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1234_, v___f_1237_, v___x_1236_, v_t_1226_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___y_1229_ = v_a_1239_;
goto v___jp_1228_;
v___jp_1228_:
{
lean_object* v_fst_1230_; 
v_fst_1230_ = lean_ctor_get(v___y_1229_, 0);
lean_inc(v_fst_1230_);
lean_dec_ref(v___y_1229_);
if (lean_obj_tag(v_fst_1230_) == 0)
{
uint8_t v___x_1231_; 
v___x_1231_ = 0;
return v___x_1231_;
}
else
{
lean_object* v_val_1232_; uint8_t v___x_1233_; 
v_val_1232_ = lean_ctor_get(v_fst_1230_, 0);
lean_inc(v_val_1232_);
lean_dec_ref(v_fst_1230_);
v___x_1233_ = lean_unbox(v_val_1232_);
lean_dec(v_val_1232_);
return v___x_1233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___boxed(lean_object* v_t_1240_, lean_object* v_p_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Std_TreeSet_any___redArg(v_t_1240_, v_p_1241_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_any(lean_object* v_00_u03b1_1244_, lean_object* v_cmp_1245_, lean_object* v_t_1246_, lean_object* v_p_1247_){
_start:
{
lean_object* v___y_1249_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___f_1257_; lean_object* v___x_1258_; lean_object* v_a_1259_; 
v___x_1254_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1255_ = lean_box(0);
v___x_1256_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1257_ = lean_alloc_closure((void*)(l_Std_TreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1257_, 0, v_p_1247_);
lean_closure_set(v___f_1257_, 1, v___x_1256_);
lean_closure_set(v___f_1257_, 2, v___x_1255_);
v___x_1258_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1254_, v___f_1257_, v___x_1256_, v_t_1246_);
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec(v___x_1258_);
v___y_1249_ = v_a_1259_;
goto v___jp_1248_;
v___jp_1248_:
{
lean_object* v_fst_1250_; 
v_fst_1250_ = lean_ctor_get(v___y_1249_, 0);
lean_inc(v_fst_1250_);
lean_dec_ref(v___y_1249_);
if (lean_obj_tag(v_fst_1250_) == 0)
{
uint8_t v___x_1251_; 
v___x_1251_ = 0;
return v___x_1251_;
}
else
{
lean_object* v_val_1252_; uint8_t v___x_1253_; 
v_val_1252_ = lean_ctor_get(v_fst_1250_, 0);
lean_inc(v_val_1252_);
lean_dec_ref(v_fst_1250_);
v___x_1253_ = lean_unbox(v_val_1252_);
lean_dec(v_val_1252_);
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_cmp_1261_, lean_object* v_t_1262_, lean_object* v_p_1263_){
_start:
{
uint8_t v_res_1264_; lean_object* v_r_1265_; 
v_res_1264_ = l_Std_TreeSet_any(v_00_u03b1_1260_, v_cmp_1261_, v_t_1262_, v_p_1263_);
lean_dec_ref(v_cmp_1261_);
v_r_1265_ = lean_box(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0(lean_object* v_p_1266_, lean_object* v___x_1267_, lean_object* v___x_1268_, lean_object* v_a_1269_, lean_object* v_b_1270_, lean_object* v_acc_1271_){
_start:
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = lean_apply_1(v_p_1266_, v_a_1269_);
v___x_1273_ = lean_unbox(v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec_ref(v___x_1268_);
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v___x_1267_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1268_);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0___boxed(lean_object* v_p_1278_, lean_object* v___x_1279_, lean_object* v___x_1280_, lean_object* v_a_1281_, lean_object* v_b_1282_, lean_object* v_acc_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Std_TreeSet_all___redArg___lam__0(v_p_1278_, v___x_1279_, v___x_1280_, v_a_1281_, v_b_1282_, v_acc_1283_);
lean_dec_ref(v_acc_1283_);
return v_res_1284_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_all___redArg(lean_object* v_t_1285_, lean_object* v_p_1286_){
_start:
{
lean_object* v___y_1288_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v_a_1298_; 
v___x_1293_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1294_ = lean_box(0);
v___x_1295_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1296_ = lean_alloc_closure((void*)(l_Std_TreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1296_, 0, v_p_1286_);
lean_closure_set(v___f_1296_, 1, v___x_1294_);
lean_closure_set(v___f_1296_, 2, v___x_1295_);
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
v___x_1290_ = 1;
return v___x_1290_;
}
else
{
lean_object* v_val_1291_; uint8_t v___x_1292_; 
v_val_1291_ = lean_ctor_get(v_fst_1289_, 0);
lean_inc(v_val_1291_);
lean_dec_ref(v_fst_1289_);
v___x_1292_ = lean_unbox(v_val_1291_);
lean_dec(v_val_1291_);
return v___x_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___boxed(lean_object* v_t_1299_, lean_object* v_p_1300_){
_start:
{
uint8_t v_res_1301_; lean_object* v_r_1302_; 
v_res_1301_ = l_Std_TreeSet_all___redArg(v_t_1299_, v_p_1300_);
v_r_1302_ = lean_box(v_res_1301_);
return v_r_1302_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_all(lean_object* v_00_u03b1_1303_, lean_object* v_cmp_1304_, lean_object* v_t_1305_, lean_object* v_p_1306_){
_start:
{
lean_object* v___y_1308_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___f_1316_; lean_object* v___x_1317_; lean_object* v_a_1318_; 
v___x_1313_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1314_ = lean_box(0);
v___x_1315_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1316_ = lean_alloc_closure((void*)(l_Std_TreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1316_, 0, v_p_1306_);
lean_closure_set(v___f_1316_, 1, v___x_1314_);
lean_closure_set(v___f_1316_, 2, v___x_1315_);
v___x_1317_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1313_, v___f_1316_, v___x_1315_, v_t_1305_);
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___y_1308_ = v_a_1318_;
goto v___jp_1307_;
v___jp_1307_:
{
lean_object* v_fst_1309_; 
v_fst_1309_ = lean_ctor_get(v___y_1308_, 0);
lean_inc(v_fst_1309_);
lean_dec_ref(v___y_1308_);
if (lean_obj_tag(v_fst_1309_) == 0)
{
uint8_t v___x_1310_; 
v___x_1310_ = 1;
return v___x_1310_;
}
else
{
lean_object* v_val_1311_; uint8_t v___x_1312_; 
v_val_1311_ = lean_ctor_get(v_fst_1309_, 0);
lean_inc(v_val_1311_);
lean_dec_ref(v_fst_1309_);
v___x_1312_ = lean_unbox(v_val_1311_);
lean_dec(v_val_1311_);
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___boxed(lean_object* v_00_u03b1_1319_, lean_object* v_cmp_1320_, lean_object* v_t_1321_, lean_object* v_p_1322_){
_start:
{
uint8_t v_res_1323_; lean_object* v_r_1324_; 
v_res_1323_ = l_Std_TreeSet_all(v_00_u03b1_1319_, v_cmp_1320_, v_t_1321_, v_p_1322_);
lean_dec_ref(v_cmp_1320_);
v_r_1324_ = lean_box(v_res_1323_);
return v_r_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg___lam__0(lean_object* v_x1_1325_, lean_object* v_x2_1326_, lean_object* v_x3_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_x1_1325_);
lean_ctor_set(v___x_1328_, 1, v_x3_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg(lean_object* v_t_1330_){
_start:
{
lean_object* v___f_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___f_1331_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___x_1332_ = lean_box(0);
v___x_1333_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1334_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1333_, v___f_1331_, v___x_1332_, v_t_1330_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList(lean_object* v_00_u03b1_1335_, lean_object* v_cmp_1336_, lean_object* v_t_1337_){
_start:
{
lean_object* v___f_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___f_1338_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___x_1339_ = lean_box(0);
v___x_1340_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1341_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1340_, v___f_1338_, v___x_1339_, v_t_1337_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_cmp_1343_, lean_object* v_t_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Std_TreeSet_toList(v_00_u03b1_1342_, v_cmp_1343_, v_t_1344_);
lean_dec_ref(v_cmp_1343_);
return v_res_1345_;
}
}
static lean_object* _init_l_Std_TreeSet_ofList___auto__1(void){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__26, &l_Std_TreeSet___auto__1___closed__26_once, _init_l_Std_TreeSet___auto__1___closed__26);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(lean_object* v_cmp_1347_, lean_object* v_k_1348_, lean_object* v_v_1349_, lean_object* v_t_1350_){
_start:
{
if (lean_obj_tag(v_t_1350_) == 0)
{
lean_object* v_size_1351_; lean_object* v_k_1352_; lean_object* v_v_1353_; lean_object* v_l_1354_; lean_object* v_r_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1636_; 
v_size_1351_ = lean_ctor_get(v_t_1350_, 0);
v_k_1352_ = lean_ctor_get(v_t_1350_, 1);
v_v_1353_ = lean_ctor_get(v_t_1350_, 2);
v_l_1354_ = lean_ctor_get(v_t_1350_, 3);
v_r_1355_ = lean_ctor_get(v_t_1350_, 4);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_t_1350_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1357_ = v_t_1350_;
v_isShared_1358_ = v_isSharedCheck_1636_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_r_1355_);
lean_inc(v_l_1354_);
lean_inc(v_v_1353_);
lean_inc(v_k_1352_);
lean_inc(v_size_1351_);
lean_dec(v_t_1350_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1636_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; uint8_t v___x_1360_; 
lean_inc_ref(v_cmp_1347_);
lean_inc(v_k_1352_);
lean_inc(v_k_1348_);
v___x_1359_ = lean_apply_2(v_cmp_1347_, v_k_1348_, v_k_1352_);
v___x_1360_ = lean_unbox(v___x_1359_);
switch(v___x_1360_)
{
case 0:
{
lean_object* v_impl_1361_; lean_object* v___x_1362_; 
lean_dec(v_size_1351_);
v_impl_1361_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1347_, v_k_1348_, v_v_1349_, v_l_1354_);
v___x_1362_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1355_) == 0)
{
lean_object* v_size_1363_; lean_object* v_size_1364_; lean_object* v_k_1365_; lean_object* v_v_1366_; lean_object* v_l_1367_; lean_object* v_r_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_size_1363_ = lean_ctor_get(v_r_1355_, 0);
v_size_1364_ = lean_ctor_get(v_impl_1361_, 0);
lean_inc(v_size_1364_);
v_k_1365_ = lean_ctor_get(v_impl_1361_, 1);
lean_inc(v_k_1365_);
v_v_1366_ = lean_ctor_get(v_impl_1361_, 2);
lean_inc(v_v_1366_);
v_l_1367_ = lean_ctor_get(v_impl_1361_, 3);
lean_inc(v_l_1367_);
v_r_1368_ = lean_ctor_get(v_impl_1361_, 4);
lean_inc(v_r_1368_);
v___x_1369_ = lean_unsigned_to_nat(3u);
v___x_1370_ = lean_nat_mul(v___x_1369_, v_size_1363_);
v___x_1371_ = lean_nat_dec_lt(v___x_1370_, v_size_1364_);
lean_dec(v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_dec(v_r_1368_);
lean_dec(v_l_1367_);
lean_dec(v_v_1366_);
lean_dec(v_k_1365_);
v___x_1372_ = lean_nat_add(v___x_1362_, v_size_1364_);
lean_dec(v_size_1364_);
v___x_1373_ = lean_nat_add(v___x_1372_, v_size_1363_);
lean_dec(v___x_1372_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 3, v_impl_1361_);
lean_ctor_set(v___x_1357_, 0, v___x_1373_);
v___x_1375_ = v___x_1357_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1376_, 3, v_impl_1361_);
lean_ctor_set(v_reuseFailAlloc_1376_, 4, v_r_1355_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
else
{
lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1442_; 
v_isSharedCheck_1442_ = !lean_is_exclusive(v_impl_1361_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; lean_object* v_unused_1444_; lean_object* v_unused_1445_; lean_object* v_unused_1446_; lean_object* v_unused_1447_; 
v_unused_1443_ = lean_ctor_get(v_impl_1361_, 4);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_impl_1361_, 3);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v_impl_1361_, 2);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_impl_1361_, 1);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_impl_1361_, 0);
lean_dec(v_unused_1447_);
v___x_1378_ = v_impl_1361_;
v_isShared_1379_ = v_isSharedCheck_1442_;
goto v_resetjp_1377_;
}
else
{
lean_dec(v_impl_1361_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1442_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v_size_1380_; lean_object* v_size_1381_; lean_object* v_k_1382_; lean_object* v_v_1383_; lean_object* v_l_1384_; lean_object* v_r_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_size_1380_ = lean_ctor_get(v_l_1367_, 0);
v_size_1381_ = lean_ctor_get(v_r_1368_, 0);
v_k_1382_ = lean_ctor_get(v_r_1368_, 1);
v_v_1383_ = lean_ctor_get(v_r_1368_, 2);
v_l_1384_ = lean_ctor_get(v_r_1368_, 3);
v_r_1385_ = lean_ctor_get(v_r_1368_, 4);
v___x_1386_ = lean_unsigned_to_nat(2u);
v___x_1387_ = lean_nat_mul(v___x_1386_, v_size_1380_);
v___x_1388_ = lean_nat_dec_lt(v_size_1381_, v___x_1387_);
lean_dec(v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1417_; 
lean_inc(v_r_1385_);
lean_inc(v_l_1384_);
lean_inc(v_v_1383_);
lean_inc(v_k_1382_);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_r_1368_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; lean_object* v_unused_1419_; lean_object* v_unused_1420_; lean_object* v_unused_1421_; lean_object* v_unused_1422_; 
v_unused_1418_ = lean_ctor_get(v_r_1368_, 4);
lean_dec(v_unused_1418_);
v_unused_1419_ = lean_ctor_get(v_r_1368_, 3);
lean_dec(v_unused_1419_);
v_unused_1420_ = lean_ctor_get(v_r_1368_, 2);
lean_dec(v_unused_1420_);
v_unused_1421_ = lean_ctor_get(v_r_1368_, 1);
lean_dec(v_unused_1421_);
v_unused_1422_ = lean_ctor_get(v_r_1368_, 0);
lean_dec(v_unused_1422_);
v___x_1390_ = v_r_1368_;
v_isShared_1391_ = v_isSharedCheck_1417_;
goto v_resetjp_1389_;
}
else
{
lean_dec(v_r_1368_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1417_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___x_1405_; lean_object* v___y_1407_; 
v___x_1392_ = lean_nat_add(v___x_1362_, v_size_1364_);
lean_dec(v_size_1364_);
v___x_1393_ = lean_nat_add(v___x_1392_, v_size_1363_);
lean_dec(v___x_1392_);
v___x_1405_ = lean_nat_add(v___x_1362_, v_size_1380_);
if (lean_obj_tag(v_l_1384_) == 0)
{
lean_object* v_size_1415_; 
v_size_1415_ = lean_ctor_get(v_l_1384_, 0);
lean_inc(v_size_1415_);
v___y_1407_ = v_size_1415_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_unsigned_to_nat(0u);
v___y_1407_ = v___x_1416_;
goto v___jp_1406_;
}
v___jp_1394_:
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1398_ = lean_nat_add(v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec(v___y_1396_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 4, v_r_1355_);
lean_ctor_set(v___x_1390_, 3, v_r_1385_);
lean_ctor_set(v___x_1390_, 2, v_v_1353_);
lean_ctor_set(v___x_1390_, 1, v_k_1352_);
lean_ctor_set(v___x_1390_, 0, v___x_1398_);
v___x_1400_ = v___x_1390_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_r_1385_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_r_1355_);
v___x_1400_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1402_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 4, v___x_1400_);
lean_ctor_set(v___x_1378_, 3, v___y_1395_);
lean_ctor_set(v___x_1378_, 2, v_v_1383_);
lean_ctor_set(v___x_1378_, 1, v_k_1382_);
lean_ctor_set(v___x_1378_, 0, v___x_1393_);
v___x_1402_ = v___x_1378_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_k_1382_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_v_1383_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v___y_1395_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
v___jp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = lean_nat_add(v___x_1405_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec(v___x_1405_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_l_1384_);
lean_ctor_set(v___x_1357_, 3, v_l_1367_);
lean_ctor_set(v___x_1357_, 2, v_v_1366_);
lean_ctor_set(v___x_1357_, 1, v_k_1365_);
lean_ctor_set(v___x_1357_, 0, v___x_1408_);
v___x_1410_ = v___x_1357_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v_l_1367_);
lean_ctor_set(v_reuseFailAlloc_1414_, 4, v_l_1384_);
v___x_1410_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_nat_add(v___x_1362_, v_size_1363_);
if (lean_obj_tag(v_r_1385_) == 0)
{
lean_object* v_size_1412_; 
v_size_1412_ = lean_ctor_get(v_r_1385_, 0);
lean_inc(v_size_1412_);
v___y_1395_ = v___x_1410_;
v___y_1396_ = v___x_1411_;
v___y_1397_ = v_size_1412_;
goto v___jp_1394_;
}
else
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_unsigned_to_nat(0u);
v___y_1395_ = v___x_1410_;
v___y_1396_ = v___x_1411_;
v___y_1397_ = v___x_1413_;
goto v___jp_1394_;
}
}
}
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
lean_del_object(v___x_1357_);
v___x_1423_ = lean_nat_add(v___x_1362_, v_size_1364_);
lean_dec(v_size_1364_);
v___x_1424_ = lean_nat_add(v___x_1423_, v_size_1363_);
lean_dec(v___x_1423_);
v___x_1425_ = lean_nat_add(v___x_1362_, v_size_1363_);
v___x_1426_ = lean_nat_add(v___x_1425_, v_size_1381_);
lean_dec(v___x_1425_);
lean_inc_ref(v_r_1355_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 4, v_r_1355_);
lean_ctor_set(v___x_1378_, 3, v_r_1368_);
lean_ctor_set(v___x_1378_, 2, v_v_1353_);
lean_ctor_set(v___x_1378_, 1, v_k_1352_);
lean_ctor_set(v___x_1378_, 0, v___x_1426_);
v___x_1428_ = v___x_1378_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_r_1368_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_r_1355_);
v___x_1428_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
v_isSharedCheck_1435_ = !lean_is_exclusive(v_r_1355_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; lean_object* v_unused_1439_; lean_object* v_unused_1440_; 
v_unused_1436_ = lean_ctor_get(v_r_1355_, 4);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_r_1355_, 3);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_r_1355_, 2);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_r_1355_, 1);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_r_1355_, 0);
lean_dec(v_unused_1440_);
v___x_1430_ = v_r_1355_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_dec(v_r_1355_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1428_);
lean_ctor_set(v___x_1430_, 3, v_l_1367_);
lean_ctor_set(v___x_1430_, 2, v_v_1366_);
lean_ctor_set(v___x_1430_, 1, v_k_1365_);
lean_ctor_set(v___x_1430_, 0, v___x_1424_);
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_l_1367_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v___x_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1448_; 
v_l_1448_ = lean_ctor_get(v_impl_1361_, 3);
lean_inc(v_l_1448_);
if (lean_obj_tag(v_l_1448_) == 0)
{
lean_object* v_r_1449_; lean_object* v_k_1450_; lean_object* v_v_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1462_; 
v_r_1449_ = lean_ctor_get(v_impl_1361_, 4);
v_k_1450_ = lean_ctor_get(v_impl_1361_, 1);
v_v_1451_ = lean_ctor_get(v_impl_1361_, 2);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_impl_1361_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; lean_object* v_unused_1464_; 
v_unused_1463_ = lean_ctor_get(v_impl_1361_, 3);
lean_dec(v_unused_1463_);
v_unused_1464_ = lean_ctor_get(v_impl_1361_, 0);
lean_dec(v_unused_1464_);
v___x_1453_ = v_impl_1361_;
v_isShared_1454_ = v_isSharedCheck_1462_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_r_1449_);
lean_inc(v_v_1451_);
lean_inc(v_k_1450_);
lean_dec(v_impl_1361_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1462_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1449_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 3, v_r_1449_);
lean_ctor_set(v___x_1453_, 2, v_v_1353_);
lean_ctor_set(v___x_1453_, 1, v_k_1352_);
lean_ctor_set(v___x_1453_, 0, v___x_1362_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_r_1449_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_r_1449_);
v___x_1457_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1459_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v___x_1457_);
lean_ctor_set(v___x_1357_, 3, v_l_1448_);
lean_ctor_set(v___x_1357_, 2, v_v_1451_);
lean_ctor_set(v___x_1357_, 1, v_k_1450_);
lean_ctor_set(v___x_1357_, 0, v___x_1455_);
v___x_1459_ = v___x_1357_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_k_1450_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_v_1451_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_l_1448_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_object* v_r_1465_; 
v_r_1465_ = lean_ctor_get(v_impl_1361_, 4);
lean_inc(v_r_1465_);
if (lean_obj_tag(v_r_1465_) == 0)
{
lean_object* v_k_1466_; lean_object* v_v_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1490_; 
v_k_1466_ = lean_ctor_get(v_impl_1361_, 1);
v_v_1467_ = lean_ctor_get(v_impl_1361_, 2);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_impl_1361_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; 
v_unused_1491_ = lean_ctor_get(v_impl_1361_, 4);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_impl_1361_, 3);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_impl_1361_, 0);
lean_dec(v_unused_1493_);
v___x_1469_ = v_impl_1361_;
v_isShared_1470_ = v_isSharedCheck_1490_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_v_1467_);
lean_inc(v_k_1466_);
lean_dec(v_impl_1361_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1490_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_k_1471_; lean_object* v_v_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1486_; 
v_k_1471_ = lean_ctor_get(v_r_1465_, 1);
v_v_1472_ = lean_ctor_get(v_r_1465_, 2);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_r_1465_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; lean_object* v_unused_1488_; lean_object* v_unused_1489_; 
v_unused_1487_ = lean_ctor_get(v_r_1465_, 4);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_r_1465_, 3);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_r_1465_, 0);
lean_dec(v_unused_1489_);
v___x_1474_ = v_r_1465_;
v_isShared_1475_ = v_isSharedCheck_1486_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
lean_dec(v_r_1465_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1486_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = lean_unsigned_to_nat(3u);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 4, v_l_1448_);
lean_ctor_set(v___x_1474_, 3, v_l_1448_);
lean_ctor_set(v___x_1474_, 2, v_v_1467_);
lean_ctor_set(v___x_1474_, 1, v_k_1466_);
lean_ctor_set(v___x_1474_, 0, v___x_1362_);
v___x_1478_ = v___x_1474_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1466_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1467_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_l_1448_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_l_1448_);
v___x_1478_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 4, v_l_1448_);
lean_ctor_set(v___x_1469_, 2, v_v_1353_);
lean_ctor_set(v___x_1469_, 1, v_k_1352_);
lean_ctor_set(v___x_1469_, 0, v___x_1362_);
v___x_1480_ = v___x_1469_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_l_1448_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_l_1448_);
v___x_1480_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v___x_1480_);
lean_ctor_set(v___x_1357_, 3, v___x_1478_);
lean_ctor_set(v___x_1357_, 2, v_v_1472_);
lean_ctor_set(v___x_1357_, 1, v_k_1471_);
lean_ctor_set(v___x_1357_, 0, v___x_1476_);
v___x_1482_ = v___x_1357_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_k_1471_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_v_1472_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_unsigned_to_nat(2u);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_r_1465_);
lean_ctor_set(v___x_1357_, 3, v_impl_1361_);
lean_ctor_set(v___x_1357_, 0, v___x_1494_);
v___x_1496_ = v___x_1357_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v_impl_1361_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v_r_1465_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1499_; 
lean_dec(v_v_1353_);
lean_dec(v_k_1352_);
lean_dec_ref(v_cmp_1347_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 2, v_v_1349_);
lean_ctor_set(v___x_1357_, 1, v_k_1348_);
v___x_1499_ = v___x_1357_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_size_1351_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1354_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_r_1355_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
default: 
{
lean_object* v_impl_1501_; lean_object* v___x_1502_; 
lean_dec(v_size_1351_);
v_impl_1501_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1347_, v_k_1348_, v_v_1349_, v_r_1355_);
v___x_1502_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1354_) == 0)
{
lean_object* v_size_1503_; lean_object* v_size_1504_; lean_object* v_k_1505_; lean_object* v_v_1506_; lean_object* v_l_1507_; lean_object* v_r_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v_size_1503_ = lean_ctor_get(v_l_1354_, 0);
v_size_1504_ = lean_ctor_get(v_impl_1501_, 0);
lean_inc(v_size_1504_);
v_k_1505_ = lean_ctor_get(v_impl_1501_, 1);
lean_inc(v_k_1505_);
v_v_1506_ = lean_ctor_get(v_impl_1501_, 2);
lean_inc(v_v_1506_);
v_l_1507_ = lean_ctor_get(v_impl_1501_, 3);
lean_inc(v_l_1507_);
v_r_1508_ = lean_ctor_get(v_impl_1501_, 4);
lean_inc(v_r_1508_);
v___x_1509_ = lean_unsigned_to_nat(3u);
v___x_1510_ = lean_nat_mul(v___x_1509_, v_size_1503_);
v___x_1511_ = lean_nat_dec_lt(v___x_1510_, v_size_1504_);
lean_dec(v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_dec(v_r_1508_);
lean_dec(v_l_1507_);
lean_dec(v_v_1506_);
lean_dec(v_k_1505_);
v___x_1512_ = lean_nat_add(v___x_1502_, v_size_1503_);
v___x_1513_ = lean_nat_add(v___x_1512_, v_size_1504_);
lean_dec(v_size_1504_);
lean_dec(v___x_1512_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_impl_1501_);
lean_ctor_set(v___x_1357_, 0, v___x_1513_);
v___x_1515_ = v___x_1357_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_l_1354_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v_impl_1501_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
else
{
lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1580_; 
v_isSharedCheck_1580_ = !lean_is_exclusive(v_impl_1501_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; lean_object* v_unused_1582_; lean_object* v_unused_1583_; lean_object* v_unused_1584_; lean_object* v_unused_1585_; 
v_unused_1581_ = lean_ctor_get(v_impl_1501_, 4);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_impl_1501_, 3);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_impl_1501_, 2);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_impl_1501_, 1);
lean_dec(v_unused_1584_);
v_unused_1585_ = lean_ctor_get(v_impl_1501_, 0);
lean_dec(v_unused_1585_);
v___x_1518_ = v_impl_1501_;
v_isShared_1519_ = v_isSharedCheck_1580_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v_impl_1501_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1580_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_size_1520_; lean_object* v_k_1521_; lean_object* v_v_1522_; lean_object* v_l_1523_; lean_object* v_r_1524_; lean_object* v_size_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v_size_1520_ = lean_ctor_get(v_l_1507_, 0);
v_k_1521_ = lean_ctor_get(v_l_1507_, 1);
v_v_1522_ = lean_ctor_get(v_l_1507_, 2);
v_l_1523_ = lean_ctor_get(v_l_1507_, 3);
v_r_1524_ = lean_ctor_get(v_l_1507_, 4);
v_size_1525_ = lean_ctor_get(v_r_1508_, 0);
v___x_1526_ = lean_unsigned_to_nat(2u);
v___x_1527_ = lean_nat_mul(v___x_1526_, v_size_1525_);
v___x_1528_ = lean_nat_dec_lt(v_size_1520_, v___x_1527_);
lean_dec(v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1556_; 
lean_inc(v_r_1524_);
lean_inc(v_l_1523_);
lean_inc(v_v_1522_);
lean_inc(v_k_1521_);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_l_1507_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; lean_object* v_unused_1558_; lean_object* v_unused_1559_; lean_object* v_unused_1560_; lean_object* v_unused_1561_; 
v_unused_1557_ = lean_ctor_get(v_l_1507_, 4);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v_l_1507_, 3);
lean_dec(v_unused_1558_);
v_unused_1559_ = lean_ctor_get(v_l_1507_, 2);
lean_dec(v_unused_1559_);
v_unused_1560_ = lean_ctor_get(v_l_1507_, 1);
lean_dec(v_unused_1560_);
v_unused_1561_ = lean_ctor_get(v_l_1507_, 0);
lean_dec(v_unused_1561_);
v___x_1530_ = v_l_1507_;
v_isShared_1531_ = v_isSharedCheck_1556_;
goto v_resetjp_1529_;
}
else
{
lean_dec(v_l_1507_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1556_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1546_; 
v___x_1532_ = lean_nat_add(v___x_1502_, v_size_1503_);
v___x_1533_ = lean_nat_add(v___x_1532_, v_size_1504_);
lean_dec(v_size_1504_);
if (lean_obj_tag(v_l_1523_) == 0)
{
lean_object* v_size_1554_; 
v_size_1554_ = lean_ctor_get(v_l_1523_, 0);
lean_inc(v_size_1554_);
v___y_1546_ = v_size_1554_;
goto v___jp_1545_;
}
else
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_unsigned_to_nat(0u);
v___y_1546_ = v___x_1555_;
goto v___jp_1545_;
}
v___jp_1534_:
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1538_ = lean_nat_add(v___y_1535_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec(v___y_1535_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 4, v_r_1508_);
lean_ctor_set(v___x_1530_, 3, v_r_1524_);
lean_ctor_set(v___x_1530_, 2, v_v_1506_);
lean_ctor_set(v___x_1530_, 1, v_k_1505_);
lean_ctor_set(v___x_1530_, 0, v___x_1538_);
v___x_1540_ = v___x_1530_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_k_1505_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_v_1506_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_r_1524_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_r_1508_);
v___x_1540_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1542_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 4, v___x_1540_);
lean_ctor_set(v___x_1518_, 3, v___y_1536_);
lean_ctor_set(v___x_1518_, 2, v_v_1522_);
lean_ctor_set(v___x_1518_, 1, v_k_1521_);
lean_ctor_set(v___x_1518_, 0, v___x_1533_);
v___x_1542_ = v___x_1518_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_k_1521_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_v_1522_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v___y_1536_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
v___jp_1545_:
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = lean_nat_add(v___x_1532_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec(v___x_1532_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_l_1523_);
lean_ctor_set(v___x_1357_, 0, v___x_1547_);
v___x_1549_ = v___x_1357_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_l_1354_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_l_1523_);
v___x_1549_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_nat_add(v___x_1502_, v_size_1525_);
if (lean_obj_tag(v_r_1524_) == 0)
{
lean_object* v_size_1551_; 
v_size_1551_ = lean_ctor_get(v_r_1524_, 0);
lean_inc(v_size_1551_);
v___y_1535_ = v___x_1550_;
v___y_1536_ = v___x_1549_;
v___y_1537_ = v_size_1551_;
goto v___jp_1534_;
}
else
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_unsigned_to_nat(0u);
v___y_1535_ = v___x_1550_;
v___y_1536_ = v___x_1549_;
v___y_1537_ = v___x_1552_;
goto v___jp_1534_;
}
}
}
}
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
lean_del_object(v___x_1357_);
v___x_1562_ = lean_nat_add(v___x_1502_, v_size_1503_);
v___x_1563_ = lean_nat_add(v___x_1562_, v_size_1504_);
lean_dec(v_size_1504_);
v___x_1564_ = lean_nat_add(v___x_1562_, v_size_1520_);
lean_dec(v___x_1562_);
lean_inc_ref(v_l_1354_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 4, v_l_1507_);
lean_ctor_set(v___x_1518_, 3, v_l_1354_);
lean_ctor_set(v___x_1518_, 2, v_v_1353_);
lean_ctor_set(v___x_1518_, 1, v_k_1352_);
lean_ctor_set(v___x_1518_, 0, v___x_1564_);
v___x_1566_ = v___x_1518_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v_l_1354_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v_l_1507_);
v___x_1566_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
v_isSharedCheck_1573_ = !lean_is_exclusive(v_l_1354_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; lean_object* v_unused_1578_; 
v_unused_1574_ = lean_ctor_get(v_l_1354_, 4);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_l_1354_, 3);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_l_1354_, 2);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_l_1354_, 1);
lean_dec(v_unused_1577_);
v_unused_1578_ = lean_ctor_get(v_l_1354_, 0);
lean_dec(v_unused_1578_);
v___x_1568_ = v_l_1354_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_dec(v_l_1354_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 4, v_r_1508_);
lean_ctor_set(v___x_1568_, 3, v___x_1566_);
lean_ctor_set(v___x_1568_, 2, v_v_1506_);
lean_ctor_set(v___x_1568_, 1, v_k_1505_);
lean_ctor_set(v___x_1568_, 0, v___x_1563_);
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_k_1505_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_v_1506_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_r_1508_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1586_; 
v_l_1586_ = lean_ctor_get(v_impl_1501_, 3);
lean_inc(v_l_1586_);
if (lean_obj_tag(v_l_1586_) == 0)
{
lean_object* v_r_1587_; lean_object* v_k_1588_; lean_object* v_v_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1612_; 
v_r_1587_ = lean_ctor_get(v_impl_1501_, 4);
v_k_1588_ = lean_ctor_get(v_impl_1501_, 1);
v_v_1589_ = lean_ctor_get(v_impl_1501_, 2);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_impl_1501_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; 
v_unused_1613_ = lean_ctor_get(v_impl_1501_, 3);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_impl_1501_, 0);
lean_dec(v_unused_1614_);
v___x_1591_ = v_impl_1501_;
v_isShared_1592_ = v_isSharedCheck_1612_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_r_1587_);
lean_inc(v_v_1589_);
lean_inc(v_k_1588_);
lean_dec(v_impl_1501_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1612_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v_k_1593_; lean_object* v_v_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1608_; 
v_k_1593_ = lean_ctor_get(v_l_1586_, 1);
v_v_1594_ = lean_ctor_get(v_l_1586_, 2);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_l_1586_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; lean_object* v_unused_1610_; lean_object* v_unused_1611_; 
v_unused_1609_ = lean_ctor_get(v_l_1586_, 4);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_l_1586_, 3);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_l_1586_, 0);
lean_dec(v_unused_1611_);
v___x_1596_ = v_l_1586_;
v_isShared_1597_ = v_isSharedCheck_1608_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_v_1594_);
lean_inc(v_k_1593_);
lean_dec(v_l_1586_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1608_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1598_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1587_, 2);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 4, v_r_1587_);
lean_ctor_set(v___x_1596_, 3, v_r_1587_);
lean_ctor_set(v___x_1596_, 2, v_v_1353_);
lean_ctor_set(v___x_1596_, 1, v_k_1352_);
lean_ctor_set(v___x_1596_, 0, v___x_1502_);
v___x_1600_ = v___x_1596_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_r_1587_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_r_1587_);
v___x_1600_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1602_; 
lean_inc(v_r_1587_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 3, v_r_1587_);
lean_ctor_set(v___x_1591_, 0, v___x_1502_);
v___x_1602_ = v___x_1591_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_k_1588_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_v_1589_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_r_1587_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_r_1587_);
v___x_1602_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1604_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v___x_1602_);
lean_ctor_set(v___x_1357_, 3, v___x_1600_);
lean_ctor_set(v___x_1357_, 2, v_v_1594_);
lean_ctor_set(v___x_1357_, 1, v_k_1593_);
lean_ctor_set(v___x_1357_, 0, v___x_1598_);
v___x_1604_ = v___x_1357_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_k_1593_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_v_1594_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1605_, 4, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
}
else
{
lean_object* v_r_1615_; 
v_r_1615_ = lean_ctor_get(v_impl_1501_, 4);
lean_inc(v_r_1615_);
if (lean_obj_tag(v_r_1615_) == 0)
{
lean_object* v_k_1616_; lean_object* v_v_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1628_; 
v_k_1616_ = lean_ctor_get(v_impl_1501_, 1);
v_v_1617_ = lean_ctor_get(v_impl_1501_, 2);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_impl_1501_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; lean_object* v_unused_1630_; lean_object* v_unused_1631_; 
v_unused_1629_ = lean_ctor_get(v_impl_1501_, 4);
lean_dec(v_unused_1629_);
v_unused_1630_ = lean_ctor_get(v_impl_1501_, 3);
lean_dec(v_unused_1630_);
v_unused_1631_ = lean_ctor_get(v_impl_1501_, 0);
lean_dec(v_unused_1631_);
v___x_1619_ = v_impl_1501_;
v_isShared_1620_ = v_isSharedCheck_1628_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_v_1617_);
lean_inc(v_k_1616_);
lean_dec(v_impl_1501_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1628_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = lean_unsigned_to_nat(3u);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v_l_1586_);
lean_ctor_set(v___x_1619_, 2, v_v_1353_);
lean_ctor_set(v___x_1619_, 1, v_k_1352_);
lean_ctor_set(v___x_1619_, 0, v___x_1502_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v_l_1586_);
lean_ctor_set(v_reuseFailAlloc_1627_, 4, v_l_1586_);
v___x_1623_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_r_1615_);
lean_ctor_set(v___x_1357_, 3, v___x_1623_);
lean_ctor_set(v___x_1357_, 2, v_v_1617_);
lean_ctor_set(v___x_1357_, 1, v_k_1616_);
lean_ctor_set(v___x_1357_, 0, v___x_1621_);
v___x_1625_ = v___x_1357_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_k_1616_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_v_1617_);
lean_ctor_set(v_reuseFailAlloc_1626_, 3, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1626_, 4, v_r_1615_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1632_ = lean_unsigned_to_nat(2u);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_impl_1501_);
lean_ctor_set(v___x_1357_, 3, v_r_1615_);
lean_ctor_set(v___x_1357_, 0, v___x_1632_);
v___x_1634_ = v___x_1357_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v_r_1615_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v_impl_1501_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
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
lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_dec_ref(v_cmp_1347_);
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v_k_1348_);
lean_ctor_set(v___x_1638_, 2, v_v_1349_);
lean_ctor_set(v___x_1638_, 3, v_t_1350_);
lean_ctor_set(v___x_1638_, 4, v_t_1350_);
return v___x_1638_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(lean_object* v_cmp_1639_, lean_object* v_k_1640_, lean_object* v_t_1641_){
_start:
{
if (lean_obj_tag(v_t_1641_) == 0)
{
lean_object* v_k_1642_; lean_object* v_l_1643_; lean_object* v_r_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v_k_1642_ = lean_ctor_get(v_t_1641_, 1);
lean_inc(v_k_1642_);
v_l_1643_ = lean_ctor_get(v_t_1641_, 3);
lean_inc(v_l_1643_);
v_r_1644_ = lean_ctor_get(v_t_1641_, 4);
lean_inc(v_r_1644_);
lean_dec_ref(v_t_1641_);
lean_inc_ref(v_cmp_1639_);
lean_inc(v_k_1640_);
v___x_1645_ = lean_apply_2(v_cmp_1639_, v_k_1640_, v_k_1642_);
v___x_1646_ = lean_unbox(v___x_1645_);
switch(v___x_1646_)
{
case 0:
{
lean_dec(v_r_1644_);
v_t_1641_ = v_l_1643_;
goto _start;
}
case 1:
{
uint8_t v___x_1648_; 
lean_dec(v_r_1644_);
lean_dec(v_l_1643_);
lean_dec(v_k_1640_);
lean_dec_ref(v_cmp_1639_);
v___x_1648_ = 1;
return v___x_1648_;
}
default: 
{
lean_dec(v_l_1643_);
v_t_1641_ = v_r_1644_;
goto _start;
}
}
}
else
{
uint8_t v___x_1650_; 
lean_dec(v_k_1640_);
lean_dec_ref(v_cmp_1639_);
v___x_1650_ = 0;
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg___boxed(lean_object* v_cmp_1651_, lean_object* v_k_1652_, lean_object* v_t_1653_){
_start:
{
uint8_t v_res_1654_; lean_object* v_r_1655_; 
v_res_1654_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1651_, v_k_1652_, v_t_1653_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(lean_object* v_cmp_1656_, lean_object* v_as_x27_1657_, lean_object* v_b_1658_){
_start:
{
if (lean_obj_tag(v_as_x27_1657_) == 0)
{
lean_dec_ref(v_cmp_1656_);
return v_b_1658_;
}
else
{
lean_object* v_head_1659_; lean_object* v_tail_1660_; uint8_t v___x_1661_; 
v_head_1659_ = lean_ctor_get(v_as_x27_1657_, 0);
lean_inc_n(v_head_1659_, 2);
v_tail_1660_ = lean_ctor_get(v_as_x27_1657_, 1);
lean_inc(v_tail_1660_);
lean_dec_ref(v_as_x27_1657_);
lean_inc(v_b_1658_);
lean_inc_ref(v_cmp_1656_);
v___x_1661_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1656_, v_head_1659_, v_b_1658_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_box(0);
lean_inc_ref(v_cmp_1656_);
v___x_1663_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1656_, v_head_1659_, v___x_1662_, v_b_1658_);
v_as_x27_1657_ = v_tail_1660_;
v_b_1658_ = v___x_1663_;
goto _start;
}
else
{
lean_dec(v_head_1659_);
v_as_x27_1657_ = v_tail_1660_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___redArg(lean_object* v_l_1666_, lean_object* v_cmp_1667_){
_start:
{
lean_object* v_r_1668_; lean_object* v___x_1669_; 
v_r_1668_ = lean_box(1);
v___x_1669_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1667_, v_l_1666_, v_r_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList(lean_object* v_00_u03b1_1670_, lean_object* v_l_1671_, lean_object* v_cmp_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Std_TreeSet_ofList___redArg(v_l_1671_, v_cmp_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(lean_object* v_00_u03b1_1674_, lean_object* v_cmp_1675_, lean_object* v_00_u03b2_1676_, lean_object* v_k_1677_, lean_object* v_t_1678_){
_start:
{
uint8_t v___x_1679_; 
v___x_1679_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1675_, v_k_1677_, v_t_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___boxed(lean_object* v_00_u03b1_1680_, lean_object* v_cmp_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_k_1683_, lean_object* v_t_1684_){
_start:
{
uint8_t v_res_1685_; lean_object* v_r_1686_; 
v_res_1685_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(v_00_u03b1_1680_, v_cmp_1681_, v_00_u03b2_1682_, v_k_1683_, v_t_1684_);
v_r_1686_ = lean_box(v_res_1685_);
return v_r_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1(lean_object* v_00_u03b1_1687_, lean_object* v_cmp_1688_, lean_object* v_00_u03b2_1689_, lean_object* v_k_1690_, lean_object* v_v_1691_, lean_object* v_t_1692_, lean_object* v_hl_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1688_, v_k_1690_, v_v_1691_, v_t_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(lean_object* v_00_u03b1_1695_, lean_object* v_cmp_1696_, lean_object* v_as_1697_, lean_object* v_as_x27_1698_, lean_object* v_b_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1696_, v_as_x27_1698_, v_b_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___boxed(lean_object* v_00_u03b1_1702_, lean_object* v_cmp_1703_, lean_object* v_as_1704_, lean_object* v_as_x27_1705_, lean_object* v_b_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(v_00_u03b1_1702_, v_cmp_1703_, v_as_1704_, v_as_x27_1705_, v_b_1706_, v_a_1707_);
lean_dec(v_as_1704_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg___lam__0(lean_object* v_l_1709_, lean_object* v_k_1710_, lean_object* v_x_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_array_push(v_l_1709_, v_k_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg(lean_object* v_t_1714_){
_start:
{
lean_object* v___f_1715_; lean_object* v___y_1717_; 
v___f_1715_ = ((lean_object*)(l_Std_TreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1714_) == 0)
{
lean_object* v_size_1720_; 
v_size_1720_ = lean_ctor_get(v_t_1714_, 0);
lean_inc(v_size_1720_);
v___y_1717_ = v_size_1720_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_unsigned_to_nat(0u);
v___y_1717_ = v___x_1721_;
goto v___jp_1716_;
}
v___jp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_mk_empty_array_with_capacity(v___y_1717_);
lean_dec(v___y_1717_);
v___x_1719_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1715_, v___x_1718_, v_t_1714_);
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray(lean_object* v_00_u03b1_1722_, lean_object* v_cmp_1723_, lean_object* v_t_1724_){
_start:
{
lean_object* v___f_1725_; lean_object* v___y_1727_; 
v___f_1725_ = ((lean_object*)(l_Std_TreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1724_) == 0)
{
lean_object* v_size_1730_; 
v_size_1730_ = lean_ctor_get(v_t_1724_, 0);
lean_inc(v_size_1730_);
v___y_1727_ = v_size_1730_;
goto v___jp_1726_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_unsigned_to_nat(0u);
v___y_1727_ = v___x_1731_;
goto v___jp_1726_;
}
v___jp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_mk_empty_array_with_capacity(v___y_1727_);
lean_dec(v___y_1727_);
v___x_1729_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1725_, v___x_1728_, v_t_1724_);
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___boxed(lean_object* v_00_u03b1_1732_, lean_object* v_cmp_1733_, lean_object* v_t_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Std_TreeSet_toArray(v_00_u03b1_1732_, v_cmp_1733_, v_t_1734_);
lean_dec_ref(v_cmp_1733_);
return v_res_1735_;
}
}
static lean_object* _init_l_Std_TreeSet_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__26, &l_Std_TreeSet___auto__1___closed__26_once, _init_l_Std_TreeSet___auto__1___closed__26);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(lean_object* v_cmp_1737_, lean_object* v_as_1738_, size_t v_sz_1739_, size_t v_i_1740_, lean_object* v_b_1741_){
_start:
{
lean_object* v___y_1743_; uint8_t v___x_1747_; 
v___x_1747_ = lean_usize_dec_lt(v_i_1740_, v_sz_1739_);
if (v___x_1747_ == 0)
{
lean_dec_ref(v_cmp_1737_);
return v_b_1741_;
}
else
{
lean_object* v_a_1748_; uint8_t v___x_1749_; 
v_a_1748_ = lean_array_uget_borrowed(v_as_1738_, v_i_1740_);
lean_inc(v_b_1741_);
lean_inc(v_a_1748_);
lean_inc_ref(v_cmp_1737_);
v___x_1749_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1737_, v_a_1748_, v_b_1741_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_box(0);
lean_inc(v_a_1748_);
lean_inc_ref(v_cmp_1737_);
v___x_1751_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1737_, v_a_1748_, v___x_1750_, v_b_1741_);
v___y_1743_ = v___x_1751_;
goto v___jp_1742_;
}
else
{
v___y_1743_ = v_b_1741_;
goto v___jp_1742_;
}
}
v___jp_1742_:
{
size_t v___x_1744_; size_t v___x_1745_; 
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_add(v_i_1740_, v___x_1744_);
v_i_1740_ = v___x_1745_;
v_b_1741_ = v___y_1743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg___boxed(lean_object* v_cmp_1752_, lean_object* v_as_1753_, lean_object* v_sz_1754_, lean_object* v_i_1755_, lean_object* v_b_1756_){
_start:
{
size_t v_sz_boxed_1757_; size_t v_i_boxed_1758_; lean_object* v_res_1759_; 
v_sz_boxed_1757_ = lean_unbox_usize(v_sz_1754_);
lean_dec(v_sz_1754_);
v_i_boxed_1758_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_res_1759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1752_, v_as_1753_, v_sz_boxed_1757_, v_i_boxed_1758_, v_b_1756_);
lean_dec_ref(v_as_1753_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg(lean_object* v_a_1760_, lean_object* v_cmp_1761_){
_start:
{
lean_object* v_r_1762_; size_t v_sz_1763_; size_t v___x_1764_; lean_object* v___x_1765_; 
v_r_1762_ = lean_box(1);
v_sz_1763_ = lean_array_size(v_a_1760_);
v___x_1764_ = ((size_t)0ULL);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1761_, v_a_1760_, v_sz_1763_, v___x_1764_, v_r_1762_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg___boxed(lean_object* v_a_1766_, lean_object* v_cmp_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Std_TreeSet_ofArray___redArg(v_a_1766_, v_cmp_1767_);
lean_dec_ref(v_a_1766_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray(lean_object* v_00_u03b1_1769_, lean_object* v_a_1770_, lean_object* v_cmp_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Std_TreeSet_ofArray___redArg(v_a_1770_, v_cmp_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___boxed(lean_object* v_00_u03b1_1773_, lean_object* v_a_1774_, lean_object* v_cmp_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_TreeSet_ofArray(v_00_u03b1_1773_, v_a_1774_, v_cmp_1775_);
lean_dec_ref(v_a_1774_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(lean_object* v_00_u03b1_1777_, lean_object* v_cmp_1778_, lean_object* v_as_1779_, size_t v_sz_1780_, size_t v_i_1781_, lean_object* v_b_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1778_, v_as_1779_, v_sz_1780_, v_i_1781_, v_b_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___boxed(lean_object* v_00_u03b1_1784_, lean_object* v_cmp_1785_, lean_object* v_as_1786_, lean_object* v_sz_1787_, lean_object* v_i_1788_, lean_object* v_b_1789_){
_start:
{
size_t v_sz_boxed_1790_; size_t v_i_boxed_1791_; lean_object* v_res_1792_; 
v_sz_boxed_1790_ = lean_unbox_usize(v_sz_1787_);
lean_dec(v_sz_1787_);
v_i_boxed_1791_ = lean_unbox_usize(v_i_1788_);
lean_dec(v_i_1788_);
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(v_00_u03b1_1784_, v_cmp_1785_, v_as_1786_, v_sz_boxed_1790_, v_i_boxed_1791_, v_b_1789_);
lean_dec_ref(v_as_1786_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0(lean_object* v_b_u2082_1795_, lean_object* v_x_1796_){
_start:
{
if (lean_obj_tag(v_x_1796_) == 0)
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1797_, 0, v_b_u2082_1795_);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = ((lean_object*)(l_Std_TreeSet_merge___redArg___lam__0___closed__0));
return v___x_1798_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1799_, lean_object* v_x_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Std_TreeSet_merge___redArg___lam__0(v_b_u2082_1799_, v_x_1800_);
lean_dec(v_x_1800_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__1(lean_object* v_cmp_1802_, lean_object* v_t_1803_, lean_object* v_a_1804_, lean_object* v_b_u2082_1805_){
_start:
{
lean_object* v___f_1806_; lean_object* v___x_1807_; 
v___f_1806_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1806_, 0, v_b_u2082_1805_);
v___x_1807_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_1802_, v_a_1804_, v___f_1806_, v_t_1803_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg(lean_object* v_cmp_1808_, lean_object* v_t_u2081_1809_, lean_object* v_t_u2082_1810_){
_start:
{
lean_object* v___f_1811_; lean_object* v___x_1812_; 
v___f_1811_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1811_, 0, v_cmp_1808_);
v___x_1812_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1811_, v_t_u2081_1809_, v_t_u2082_1810_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge(lean_object* v_00_u03b1_1813_, lean_object* v_cmp_1814_, lean_object* v_t_u2081_1815_, lean_object* v_t_u2082_1816_){
_start:
{
lean_object* v___f_1817_; lean_object* v___x_1818_; 
v___f_1817_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1817_, 0, v_cmp_1814_);
v___x_1818_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1817_, v_t_u2081_1815_, v_t_u2082_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg___lam__0(lean_object* v_cmp_1819_, lean_object* v_a_1820_, lean_object* v_____s_1821_){
_start:
{
uint8_t v___x_1822_; 
lean_inc(v_____s_1821_);
lean_inc(v_a_1820_);
lean_inc_ref(v_cmp_1819_);
v___x_1822_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1819_, v_a_1820_, v_____s_1821_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_box(0);
v___x_1824_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1819_, v_a_1820_, v___x_1823_, v_____s_1821_);
v___x_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; 
lean_dec(v_a_1820_);
lean_dec_ref(v_cmp_1819_);
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_____s_1821_);
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg(lean_object* v_cmp_1827_, lean_object* v_inst_1828_, lean_object* v_t_1829_, lean_object* v_l_1830_){
_start:
{
lean_object* v___f_1831_; lean_object* v___x_1832_; 
v___f_1831_ = lean_alloc_closure((void*)(l_Std_TreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1831_, 0, v_cmp_1827_);
v___x_1832_ = lean_apply_4(v_inst_1828_, lean_box(0), v_l_1830_, v_t_1829_, v___f_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany(lean_object* v_00_u03b1_1833_, lean_object* v_cmp_1834_, lean_object* v_00_u03c1_1835_, lean_object* v_inst_1836_, lean_object* v_t_1837_, lean_object* v_l_1838_){
_start:
{
lean_object* v___f_1839_; lean_object* v___x_1840_; 
v___f_1839_ = lean_alloc_closure((void*)(l_Std_TreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1839_, 0, v_cmp_1834_);
v___x_1840_ = lean_apply_4(v_inst_1836_, lean_box(0), v_l_1838_, v_t_1837_, v___f_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_union___redArg(lean_object* v_cmp_1841_, lean_object* v_t_u2081_1842_, lean_object* v_t_u2082_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1841_, v_t_u2081_1842_, v_t_u2082_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_union(lean_object* v_00_u03b1_1845_, lean_object* v_cmp_1846_, lean_object* v_t_u2081_1847_, lean_object* v_t_u2082_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1846_, v_t_u2081_1847_, v_t_u2082_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion___redArg(lean_object* v_cmp_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_alloc_closure((void*)(l_Std_TreeSet_union), 4, 2);
lean_closure_set(v___x_1851_, 0, lean_box(0));
lean_closure_set(v___x_1851_, 1, v_cmp_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion(lean_object* v_00_u03b1_1852_, lean_object* v_cmp_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_alloc_closure((void*)(l_Std_TreeSet_union), 4, 2);
lean_closure_set(v___x_1854_, 0, lean_box(0));
lean_closure_set(v___x_1854_, 1, v_cmp_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_inter___redArg(lean_object* v_cmp_1855_, lean_object* v_t_u2081_1856_, lean_object* v_t_u2082_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1855_, v_t_u2081_1856_, v_t_u2082_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_inter(lean_object* v_00_u03b1_1859_, lean_object* v_cmp_1860_, lean_object* v_t_u2081_1861_, lean_object* v_t_u2082_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1860_, v_t_u2081_1861_, v_t_u2082_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter___redArg(lean_object* v_cmp_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_alloc_closure((void*)(l_Std_TreeSet_inter), 4, 2);
lean_closure_set(v___x_1865_, 0, lean_box(0));
lean_closure_set(v___x_1865_, 1, v_cmp_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter(lean_object* v_00_u03b1_1866_, lean_object* v_cmp_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_alloc_closure((void*)(l_Std_TreeSet_inter), 4, 2);
lean_closure_set(v___x_1868_, 0, lean_box(0));
lean_closure_set(v___x_1868_, 1, v_cmp_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_cmp_1869_, lean_object* v_t_1870_, lean_object* v_k_1871_){
_start:
{
if (lean_obj_tag(v_t_1870_) == 0)
{
lean_object* v_k_1872_; lean_object* v_v_1873_; lean_object* v_l_1874_; lean_object* v_r_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v_k_1872_ = lean_ctor_get(v_t_1870_, 1);
lean_inc(v_k_1872_);
v_v_1873_ = lean_ctor_get(v_t_1870_, 2);
lean_inc(v_v_1873_);
v_l_1874_ = lean_ctor_get(v_t_1870_, 3);
lean_inc(v_l_1874_);
v_r_1875_ = lean_ctor_get(v_t_1870_, 4);
lean_inc(v_r_1875_);
lean_dec_ref(v_t_1870_);
lean_inc_ref(v_cmp_1869_);
lean_inc(v_k_1871_);
v___x_1876_ = lean_apply_2(v_cmp_1869_, v_k_1871_, v_k_1872_);
v___x_1877_ = lean_unbox(v___x_1876_);
switch(v___x_1877_)
{
case 0:
{
lean_dec(v_r_1875_);
lean_dec(v_v_1873_);
v_t_1870_ = v_l_1874_;
goto _start;
}
case 1:
{
lean_object* v___x_1879_; 
lean_dec(v_r_1875_);
lean_dec(v_l_1874_);
lean_dec(v_k_1871_);
lean_dec_ref(v_cmp_1869_);
v___x_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_v_1873_);
return v___x_1879_;
}
default: 
{
lean_dec(v_l_1874_);
lean_dec(v_v_1873_);
v_t_1870_ = v_r_1875_;
goto _start;
}
}
}
else
{
lean_object* v___x_1881_; 
lean_dec(v_k_1871_);
lean_dec_ref(v_cmp_1869_);
v___x_1881_ = lean_box(0);
return v___x_1881_;
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1882_, lean_object* v_x_1883_){
_start:
{
if (lean_obj_tag(v_x_1882_) == 0)
{
if (lean_obj_tag(v_x_1883_) == 0)
{
uint8_t v___x_1884_; 
v___x_1884_ = 1;
return v___x_1884_;
}
else
{
uint8_t v___x_1885_; 
v___x_1885_ = 0;
return v___x_1885_;
}
}
else
{
if (lean_obj_tag(v_x_1883_) == 0)
{
uint8_t v___x_1886_; 
v___x_1886_ = 0;
return v___x_1886_;
}
else
{
uint8_t v___x_1887_; 
v___x_1887_ = 1;
return v___x_1887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
uint8_t v_res_1890_; lean_object* v_r_1891_; 
v_res_1890_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v_x_1888_, v_x_1889_);
lean_dec(v_x_1889_);
lean_dec(v_x_1888_);
v_r_1891_ = lean_box(v_res_1890_);
return v_r_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_cmp_1892_, lean_object* v_t_u2082_1893_, lean_object* v_init_1894_, lean_object* v_x_1895_){
_start:
{
if (lean_obj_tag(v_x_1895_) == 0)
{
lean_object* v_k_1896_; lean_object* v_v_1897_; lean_object* v_l_1898_; lean_object* v_r_1899_; lean_object* v___x_1900_; 
v_k_1896_ = lean_ctor_get(v_x_1895_, 1);
lean_inc(v_k_1896_);
v_v_1897_ = lean_ctor_get(v_x_1895_, 2);
lean_inc(v_v_1897_);
v_l_1898_ = lean_ctor_get(v_x_1895_, 3);
lean_inc(v_l_1898_);
v_r_1899_ = lean_ctor_get(v_x_1895_, 4);
lean_inc(v_r_1899_);
lean_dec_ref(v_x_1895_);
lean_inc(v_t_u2082_1893_);
lean_inc_ref(v_cmp_1892_);
v___x_1900_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_1892_, v_t_u2082_1893_, v_init_1894_, v_l_1898_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_dec(v_r_1899_);
lean_dec(v_v_1897_);
lean_dec(v_k_1896_);
lean_dec(v_t_u2082_1893_);
lean_dec_ref(v_cmp_1892_);
return v___x_1900_;
}
else
{
lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1916_; 
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v___x_1900_, 0);
lean_dec(v_unused_1917_);
v___x_1902_ = v___x_1900_;
v_isShared_1903_ = v_isSharedCheck_1916_;
goto v_resetjp_1901_;
}
else
{
lean_dec(v___x_1900_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1916_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1904_ = lean_box(0);
lean_inc(v_t_u2082_1893_);
lean_inc_ref(v_cmp_1892_);
v___x_1905_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1892_, v_t_u2082_1893_, v_k_1896_);
v___x_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_v_1897_);
v___x_1907_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v___x_1905_, v___x_1906_);
lean_dec_ref(v___x_1906_);
lean_dec(v___x_1905_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_dec(v_r_1899_);
lean_dec(v_t_u2082_1893_);
lean_dec_ref(v_cmp_1892_);
v___x_1908_ = lean_box(v___x_1907_);
v___x_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v___x_1904_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set_tag(v___x_1902_, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1910_);
v___x_1912_ = v___x_1902_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
else
{
lean_object* v___x_1914_; 
lean_del_object(v___x_1902_);
v___x_1914_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v_init_1894_ = v___x_1914_;
v_x_1895_ = v_r_1899_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1918_; 
lean_dec(v_t_u2082_1893_);
lean_dec_ref(v_cmp_1892_);
v___x_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_init_1894_);
return v___x_1918_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_1919_, lean_object* v_t_u2081_1920_, lean_object* v_t_u2082_1921_){
_start:
{
lean_object* v___y_1923_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1936_; 
if (lean_obj_tag(v_t_u2081_1920_) == 0)
{
lean_object* v_size_1939_; 
v_size_1939_ = lean_ctor_get(v_t_u2081_1920_, 0);
lean_inc(v_size_1939_);
v___y_1936_ = v_size_1939_;
goto v___jp_1935_;
}
else
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_unsigned_to_nat(0u);
v___y_1936_ = v___x_1940_;
goto v___jp_1935_;
}
v___jp_1922_:
{
lean_object* v_fst_1924_; 
v_fst_1924_ = lean_ctor_get(v___y_1923_, 0);
lean_inc(v_fst_1924_);
lean_dec_ref(v___y_1923_);
if (lean_obj_tag(v_fst_1924_) == 0)
{
uint8_t v___x_1925_; 
v___x_1925_ = 1;
return v___x_1925_;
}
else
{
lean_object* v_val_1926_; uint8_t v___x_1927_; 
v_val_1926_ = lean_ctor_get(v_fst_1924_, 0);
lean_inc(v_val_1926_);
lean_dec_ref(v_fst_1924_);
v___x_1927_ = lean_unbox(v_val_1926_);
lean_dec(v_val_1926_);
return v___x_1927_;
}
}
v___jp_1928_:
{
uint8_t v___x_1931_; 
v___x_1931_ = lean_nat_dec_eq(v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
if (v___x_1931_ == 0)
{
lean_dec(v_t_u2082_1921_);
lean_dec(v_t_u2081_1920_);
lean_dec_ref(v_cmp_1919_);
return v___x_1931_;
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v_a_1934_; 
v___x_1932_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___x_1933_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_1919_, v_t_u2082_1921_, v___x_1932_, v_t_u2081_1920_);
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref(v___x_1933_);
v___y_1923_ = v_a_1934_;
goto v___jp_1922_;
}
}
v___jp_1935_:
{
if (lean_obj_tag(v_t_u2082_1921_) == 0)
{
lean_object* v_size_1937_; 
v_size_1937_ = lean_ctor_get(v_t_u2082_1921_, 0);
lean_inc(v_size_1937_);
v___y_1929_ = v___y_1936_;
v___y_1930_ = v_size_1937_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_unsigned_to_nat(0u);
v___y_1929_ = v___y_1936_;
v___y_1930_ = v___x_1938_;
goto v___jp_1928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_1941_, lean_object* v_t_u2081_1942_, lean_object* v_t_u2082_1943_){
_start:
{
uint8_t v_res_1944_; lean_object* v_r_1945_; 
v_res_1944_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1941_, v_t_u2081_1942_, v_t_u2082_1943_);
v_r_1945_ = lean_box(v_res_1944_);
return v_r_1945_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_beq___redArg(lean_object* v_cmp_1946_, lean_object* v_t_u2081_1947_, lean_object* v_t_u2082_1948_){
_start:
{
uint8_t v___x_1949_; 
v___x_1949_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1946_, v_t_u2081_1947_, v_t_u2082_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___redArg___boxed(lean_object* v_cmp_1950_, lean_object* v_t_u2081_1951_, lean_object* v_t_u2082_1952_){
_start:
{
uint8_t v_res_1953_; lean_object* v_r_1954_; 
v_res_1953_ = l_Std_TreeSet_beq___redArg(v_cmp_1950_, v_t_u2081_1951_, v_t_u2082_1952_);
v_r_1954_ = lean_box(v_res_1953_);
return v_r_1954_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_beq(lean_object* v_00_u03b1_1955_, lean_object* v_cmp_1956_, lean_object* v_t_u2081_1957_, lean_object* v_t_u2082_1958_){
_start:
{
uint8_t v___x_1959_; 
v___x_1959_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1956_, v_t_u2081_1957_, v_t_u2082_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___boxed(lean_object* v_00_u03b1_1960_, lean_object* v_cmp_1961_, lean_object* v_t_u2081_1962_, lean_object* v_t_u2082_1963_){
_start:
{
uint8_t v_res_1964_; lean_object* v_r_1965_; 
v_res_1964_ = l_Std_TreeSet_beq(v_00_u03b1_1960_, v_cmp_1961_, v_t_u2081_1962_, v_t_u2082_1963_);
v_r_1965_ = lean_box(v_res_1964_);
return v_r_1965_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(lean_object* v_cmp_1966_, lean_object* v_t_u2081_1967_, lean_object* v_t_u2082_1968_){
_start:
{
uint8_t v___x_1969_; 
v___x_1969_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1966_, v_t_u2081_1967_, v_t_u2082_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg___boxed(lean_object* v_cmp_1970_, lean_object* v_t_u2081_1971_, lean_object* v_t_u2082_1972_){
_start:
{
uint8_t v_res_1973_; lean_object* v_r_1974_; 
v_res_1973_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(v_cmp_1970_, v_t_u2081_1971_, v_t_u2082_1972_);
v_r_1974_ = lean_box(v_res_1973_);
return v_r_1974_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(lean_object* v_00_u03b1_1975_, lean_object* v_cmp_1976_, lean_object* v_t_u2081_1977_, lean_object* v_t_u2082_1978_){
_start:
{
uint8_t v___x_1979_; 
v___x_1979_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1976_, v_t_u2081_1977_, v_t_u2082_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___boxed(lean_object* v_00_u03b1_1980_, lean_object* v_cmp_1981_, lean_object* v_t_u2081_1982_, lean_object* v_t_u2082_1983_){
_start:
{
uint8_t v_res_1984_; lean_object* v_r_1985_; 
v_res_1984_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(v_00_u03b1_1980_, v_cmp_1981_, v_t_u2081_1982_, v_t_u2082_1983_);
v_r_1985_ = lean_box(v_res_1984_);
return v_r_1985_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(lean_object* v_cmp_1986_, lean_object* v_t_u2081_1987_, lean_object* v_t_u2082_1988_){
_start:
{
uint8_t v___x_1989_; 
v___x_1989_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1986_, v_t_u2081_1987_, v_t_u2082_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_1990_, lean_object* v_t_u2081_1991_, lean_object* v_t_u2082_1992_){
_start:
{
uint8_t v_res_1993_; lean_object* v_r_1994_; 
v_res_1993_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(v_cmp_1990_, v_t_u2081_1991_, v_t_u2082_1992_);
v_r_1994_ = lean_box(v_res_1993_);
return v_r_1994_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(lean_object* v_00_u03b1_1995_, lean_object* v_cmp_1996_, lean_object* v_t_u2081_1997_, lean_object* v_t_u2082_1998_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1996_, v_t_u2081_1997_, v_t_u2082_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2000_, lean_object* v_cmp_2001_, lean_object* v_t_u2081_2002_, lean_object* v_t_u2082_2003_){
_start:
{
uint8_t v_res_2004_; lean_object* v_r_2005_; 
v_res_2004_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(v_00_u03b1_2000_, v_cmp_2001_, v_t_u2081_2002_, v_t_u2082_2003_);
v_r_2005_ = lean_box(v_res_2004_);
return v_r_2005_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2006_, lean_object* v_cmp_2007_, lean_object* v_t_u2081_2008_, lean_object* v_t_u2082_2009_){
_start:
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2007_, v_t_u2081_2008_, v_t_u2082_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2011_, lean_object* v_cmp_2012_, lean_object* v_t_u2081_2013_, lean_object* v_t_u2082_2014_){
_start:
{
uint8_t v_res_2015_; lean_object* v_r_2016_; 
v_res_2015_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(v_00_u03b1_2011_, v_cmp_2012_, v_t_u2081_2013_, v_t_u2082_2014_);
v_r_2016_ = lean_box(v_res_2015_);
return v_r_2016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2017_, lean_object* v_cmp_2018_, lean_object* v_00_u03b4_2019_, lean_object* v_t_2020_, lean_object* v_k_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_2018_, v_t_2020_, v_k_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2023_, lean_object* v_cmp_2024_, lean_object* v_t_u2082_2025_, lean_object* v_init_2026_, lean_object* v_x_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_2024_, v_t_u2082_2025_, v_init_2026_, v_x_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq___redArg(lean_object* v_cmp_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_alloc_closure((void*)(l_Std_TreeSet_beq___boxed), 4, 2);
lean_closure_set(v___x_2030_, 0, lean_box(0));
lean_closure_set(v___x_2030_, 1, v_cmp_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq(lean_object* v_00_u03b1_2031_, lean_object* v_cmp_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_alloc_closure((void*)(l_Std_TreeSet_beq___boxed), 4, 2);
lean_closure_set(v___x_2033_, 0, lean_box(0));
lean_closure_set(v___x_2033_, 1, v_cmp_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_diff___redArg(lean_object* v_cmp_2034_, lean_object* v_t_u2081_2035_, lean_object* v_t_u2082_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2034_, v_t_u2081_2035_, v_t_u2082_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_diff(lean_object* v_00_u03b1_2038_, lean_object* v_cmp_2039_, lean_object* v_t_u2081_2040_, lean_object* v_t_u2082_2041_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2039_, v_t_u2081_2040_, v_t_u2082_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff___redArg(lean_object* v_cmp_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = lean_alloc_closure((void*)(l_Std_TreeSet_diff), 4, 2);
lean_closure_set(v___x_2044_, 0, lean_box(0));
lean_closure_set(v___x_2044_, 1, v_cmp_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff(lean_object* v_00_u03b1_2045_, lean_object* v_cmp_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_alloc_closure((void*)(l_Std_TreeSet_diff), 4, 2);
lean_closure_set(v___x_2047_, 0, lean_box(0));
lean_closure_set(v___x_2047_, 1, v_cmp_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg___lam__0(lean_object* v_cmp_2048_, lean_object* v_a_2049_, lean_object* v_____s_2050_){
_start:
{
lean_object* v_r_2051_; lean_object* v___x_2052_; 
v_r_2051_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2048_, v_a_2049_, v_____s_2050_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_r_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg(lean_object* v_cmp_2053_, lean_object* v_inst_2054_, lean_object* v_t_2055_, lean_object* v_l_2056_){
_start:
{
lean_object* v___f_2057_; lean_object* v___x_2058_; 
v___f_2057_ = lean_alloc_closure((void*)(l_Std_TreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2057_, 0, v_cmp_2053_);
v___x_2058_ = lean_apply_4(v_inst_2054_, lean_box(0), v_l_2056_, v_t_2055_, v___f_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany(lean_object* v_00_u03b1_2059_, lean_object* v_cmp_2060_, lean_object* v_00_u03c1_2061_, lean_object* v_inst_2062_, lean_object* v_t_2063_, lean_object* v_l_2064_){
_start:
{
lean_object* v___f_2065_; lean_object* v___x_2066_; 
v___f_2065_ = lean_alloc_closure((void*)(l_Std_TreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2065_, 0, v_cmp_2060_);
v___x_2066_ = lean_apply_4(v_inst_2062_, lean_box(0), v_l_2064_, v_t_2063_, v___f_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1(lean_object* v___f_2070_, lean_object* v_inst_2071_, lean_object* v_m_2072_, lean_object* v_prec_2073_){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2074_ = ((lean_object*)(l_Std_TreeSet_instRepr___redArg___lam__1___closed__1));
v___x_2075_ = lean_box(0);
v___x_2076_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_2077_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2076_, v___f_2070_, v___x_2075_, v_m_2072_);
v___x_2078_ = l_List_repr___redArg(v_inst_2071_, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2074_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = l_Repr_addAppParen(v___x_2079_, v_prec_2073_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1___boxed(lean_object* v___f_2081_, lean_object* v_inst_2082_, lean_object* v_m_2083_, lean_object* v_prec_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Std_TreeSet_instRepr___redArg___lam__1(v___f_2081_, v_inst_2082_, v_m_2083_, v_prec_2084_);
lean_dec(v_prec_2084_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg(lean_object* v_inst_2086_){
_start:
{
lean_object* v___f_2087_; lean_object* v___f_2088_; 
v___f_2087_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___f_2088_ = lean_alloc_closure((void*)(l_Std_TreeSet_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2088_, 0, v___f_2087_);
lean_closure_set(v___f_2088_, 1, v_inst_2086_);
return v___f_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr(lean_object* v_00_u03b1_2089_, lean_object* v_cmp_2090_, lean_object* v_inst_2091_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Std_TreeSet_instRepr___redArg(v_inst_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___boxed(lean_object* v_00_u03b1_2093_, lean_object* v_cmp_2094_, lean_object* v_inst_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Std_TreeSet_instRepr(v_00_u03b1_2093_, v_cmp_2094_, v_inst_2095_);
lean_dec_ref(v_cmp_2094_);
return v_res_2096_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
