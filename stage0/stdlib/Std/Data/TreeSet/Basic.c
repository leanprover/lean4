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
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_150_);
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
lean_inc(v_quotContext_156_);
v_currMacroScope_157_ = lean_ctor_get(v_a_150_, 2);
lean_inc(v_currMacroScope_157_);
v_ref_158_ = lean_ctor_get(v_a_150_, 5);
lean_inc(v_ref_158_);
lean_dec_ref(v_a_150_);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = l_Lean_Syntax_getArg(v_x_149_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(2u);
v___x_162_ = l_Lean_Syntax_getArg(v_x_149_, v___x_161_);
lean_dec(v_x_149_);
v___x_163_ = 0;
v___x_164_ = l_Lean_SourceInfo_fromRef(v_ref_158_, v___x_163_);
lean_dec(v_ref_158_);
v___x_165_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2));
v___x_166_ = lean_obj_once(&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4, &l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4_once, _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4);
v___x_167_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5));
v___x_168_ = l_Lean_addMacroScope(v_quotContext_156_, v___x_167_, v_currMacroScope_157_);
v___x_169_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10));
lean_inc(v___x_164_);
v___x_170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_170_, 0, v___x_164_);
lean_ctor_set(v___x_170_, 1, v___x_166_);
lean_ctor_set(v___x_170_, 2, v___x_168_);
lean_ctor_set(v___x_170_, 3, v___x_169_);
v___x_171_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__9));
lean_inc(v___x_164_);
v___x_172_ = l_Lean_Syntax_node2(v___x_164_, v___x_171_, v___x_160_, v___x_162_);
v___x_173_ = l_Lean_Syntax_node2(v___x_164_, v___x_165_, v___x_170_, v___x_172_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_a_151_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(lean_object* v_x_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2));
lean_inc(v_x_178_);
v___x_182_ = l_Lean_Syntax_isOfKind(v_x_178_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_x_178_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_a_180_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = l_Lean_Syntax_getArg(v_x_178_, v___x_185_);
v___x_187_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1));
lean_inc(v___x_186_);
v___x_188_ = l_Lean_Syntax_isOfKind(v___x_186_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v___x_186_);
lean_dec(v_x_178_);
v___x_189_ = lean_box(0);
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_180_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = l_Lean_Syntax_getArg(v_x_178_, v___x_191_);
lean_dec(v_x_178_);
v___x_193_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_192_);
v___x_194_ = l_Lean_Syntax_matchesNull(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v___x_192_);
lean_dec(v___x_186_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_180_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_ref_199_; uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_197_ = l_Lean_Syntax_getArg(v___x_192_, v___x_185_);
v___x_198_ = l_Lean_Syntax_getArg(v___x_192_, v___x_191_);
lean_dec(v___x_192_);
v_ref_199_ = l_Lean_replaceRef(v___x_186_, v_a_179_);
lean_dec(v___x_186_);
v___x_200_ = 0;
v___x_201_ = l_Lean_SourceInfo_fromRef(v_ref_199_, v___x_200_);
lean_dec(v_ref_199_);
v___x_202_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__3));
v___x_203_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__6));
lean_inc(v___x_201_);
v___x_204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_201_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = l_Lean_Syntax_node3(v___x_201_, v___x_202_, v___x_197_, v___x_204_, v___x_198_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v_a_180_);
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___boxed(lean_object* v_x_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(v_x_207_, v_a_208_, v_a_209_);
lean_dec(v_a_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insert___redArg(lean_object* v_cmp_211_, lean_object* v_l_212_, lean_object* v_a_213_){
_start:
{
uint8_t v___x_214_; 
lean_inc(v_l_212_);
lean_inc(v_a_213_);
lean_inc_ref(v_cmp_211_);
v___x_214_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_211_, v_a_213_, v_l_212_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_box(0);
v___x_216_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_211_, v_a_213_, v___x_215_, v_l_212_);
return v___x_216_;
}
else
{
lean_dec(v_a_213_);
lean_dec_ref(v_cmp_211_);
return v_l_212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insert(lean_object* v_00_u03b1_217_, lean_object* v_cmp_218_, lean_object* v_l_219_, lean_object* v_a_220_){
_start:
{
uint8_t v___x_221_; 
lean_inc(v_l_219_);
lean_inc(v_a_220_);
lean_inc_ref(v_cmp_218_);
v___x_221_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_218_, v_a_220_, v_l_219_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_box(0);
v___x_223_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_218_, v_a_220_, v___x_222_, v_l_219_);
return v___x_223_;
}
else
{
lean_dec(v_a_220_);
lean_dec_ref(v_cmp_218_);
return v_l_219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg___lam__0(lean_object* v_cmp_224_, lean_object* v_e_225_){
_start:
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = lean_box(1);
lean_inc(v_e_225_);
lean_inc_ref(v_cmp_224_);
v___x_227_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_224_, v_e_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_box(0);
v___x_229_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_224_, v_e_225_, v___x_228_, v___x_226_);
return v___x_229_;
}
else
{
lean_dec(v_e_225_);
lean_dec_ref(v_cmp_224_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg(lean_object* v_cmp_230_){
_start:
{
lean_object* v___f_231_; 
v___f_231_ = lean_alloc_closure((void*)(l_Std_TreeSet_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_231_, 0, v_cmp_230_);
return v___f_231_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton(lean_object* v_00_u03b1_232_, lean_object* v_cmp_233_){
_start:
{
lean_object* v___f_234_; 
v___f_234_ = lean_alloc_closure((void*)(l_Std_TreeSet_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_234_, 0, v_cmp_233_);
return v___f_234_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg___lam__0(lean_object* v_cmp_235_, lean_object* v_e_236_, lean_object* v_s_237_){
_start:
{
uint8_t v___x_238_; 
lean_inc(v_s_237_);
lean_inc(v_e_236_);
lean_inc_ref(v_cmp_235_);
v___x_238_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_235_, v_e_236_, v_s_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_box(0);
v___x_240_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_235_, v_e_236_, v___x_239_, v_s_237_);
return v___x_240_;
}
else
{
lean_dec(v_e_236_);
lean_dec_ref(v_cmp_235_);
return v_s_237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg(lean_object* v_cmp_241_){
_start:
{
lean_object* v___f_242_; 
v___f_242_ = lean_alloc_closure((void*)(l_Std_TreeSet_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_242_, 0, v_cmp_241_);
return v___f_242_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert(lean_object* v_00_u03b1_243_, lean_object* v_cmp_244_){
_start:
{
lean_object* v___f_245_; 
v___f_245_ = lean_alloc_closure((void*)(l_Std_TreeSet_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_245_, 0, v_cmp_244_);
return v___f_245_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert___redArg(lean_object* v_cmp_246_, lean_object* v_t_247_, lean_object* v_a_248_){
_start:
{
uint8_t v___x_249_; 
lean_inc(v_t_247_);
lean_inc(v_a_248_);
lean_inc_ref(v_cmp_246_);
v___x_249_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_246_, v_a_248_, v_t_247_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_250_ = lean_box(0);
v___x_251_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_246_, v_a_248_, v___x_250_, v_t_247_);
v___x_252_ = lean_box(v___x_249_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_a_248_);
lean_dec_ref(v_cmp_246_);
v___x_254_ = lean_box(v___x_249_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_t_247_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert(lean_object* v_00_u03b1_256_, lean_object* v_cmp_257_, lean_object* v_t_258_, lean_object* v_a_259_){
_start:
{
uint8_t v___x_260_; 
lean_inc(v_t_258_);
lean_inc(v_a_259_);
lean_inc_ref(v_cmp_257_);
v___x_260_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_257_, v_a_259_, v_t_258_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_box(0);
v___x_262_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_257_, v_a_259_, v___x_261_, v_t_258_);
v___x_263_ = lean_box(v___x_260_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_a_259_);
lean_dec_ref(v_cmp_257_);
v___x_265_ = lean_box(v___x_260_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_t_258_);
return v___x_266_;
}
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_contains___redArg(lean_object* v_cmp_267_, lean_object* v_l_268_, lean_object* v_a_269_){
_start:
{
uint8_t v___x_270_; 
v___x_270_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_267_, v_a_269_, v_l_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___redArg___boxed(lean_object* v_cmp_271_, lean_object* v_l_272_, lean_object* v_a_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Std_TreeSet_contains___redArg(v_cmp_271_, v_l_272_, v_a_273_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_contains(lean_object* v_00_u03b1_276_, lean_object* v_cmp_277_, lean_object* v_l_278_, lean_object* v_a_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_277_, v_a_279_, v_l_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___boxed(lean_object* v_00_u03b1_281_, lean_object* v_cmp_282_, lean_object* v_l_283_, lean_object* v_a_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Std_TreeSet_contains(v_00_u03b1_281_, v_cmp_282_, v_l_283_, v_a_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership(lean_object* v_00_u03b1_287_, lean_object* v_cmp_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_box(0);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___boxed(lean_object* v_00_u03b1_290_, lean_object* v_cmp_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_TreeSet_instMembership(v_00_u03b1_290_, v_cmp_291_);
lean_dec_ref(v_cmp_291_);
return v_res_292_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableMem___redArg(lean_object* v_cmp_293_, lean_object* v_m_294_, lean_object* v_a_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_293_, v_a_295_, v_m_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___redArg___boxed(lean_object* v_cmp_297_, lean_object* v_m_298_, lean_object* v_a_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_TreeSet_instDecidableMem___redArg(v_cmp_297_, v_m_298_, v_a_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableMem(lean_object* v_00_u03b1_302_, lean_object* v_cmp_303_, lean_object* v_m_304_, lean_object* v_a_305_){
_start:
{
uint8_t v___x_306_; 
v___x_306_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_303_, v_a_305_, v_m_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___boxed(lean_object* v_00_u03b1_307_, lean_object* v_cmp_308_, lean_object* v_m_309_, lean_object* v_a_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_Std_TreeSet_instDecidableMem(v_00_u03b1_307_, v_cmp_308_, v_m_309_, v_a_310_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg(lean_object* v_t_313_){
_start:
{
if (lean_obj_tag(v_t_313_) == 0)
{
lean_object* v_size_314_; 
v_size_314_ = lean_ctor_get(v_t_313_, 0);
lean_inc(v_size_314_);
return v_size_314_;
}
else
{
lean_object* v___x_315_; 
v___x_315_ = lean_unsigned_to_nat(0u);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg___boxed(lean_object* v_t_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_TreeSet_size___redArg(v_t_316_);
lean_dec(v_t_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size(lean_object* v_00_u03b1_318_, lean_object* v_cmp_319_, lean_object* v_t_320_){
_start:
{
if (lean_obj_tag(v_t_320_) == 0)
{
lean_object* v_size_321_; 
v_size_321_ = lean_ctor_get(v_t_320_, 0);
lean_inc(v_size_321_);
return v_size_321_;
}
else
{
lean_object* v___x_322_; 
v___x_322_ = lean_unsigned_to_nat(0u);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___boxed(lean_object* v_00_u03b1_323_, lean_object* v_cmp_324_, lean_object* v_t_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_TreeSet_size(v_00_u03b1_323_, v_cmp_324_, v_t_325_);
lean_dec(v_t_325_);
lean_dec_ref(v_cmp_324_);
return v_res_326_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_isEmpty___redArg(lean_object* v_t_327_){
_start:
{
if (lean_obj_tag(v_t_327_) == 0)
{
uint8_t v___x_328_; 
v___x_328_ = 0;
return v___x_328_;
}
else
{
uint8_t v___x_329_; 
v___x_329_ = 1;
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___redArg___boxed(lean_object* v_t_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Std_TreeSet_isEmpty___redArg(v_t_330_);
lean_dec(v_t_330_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_isEmpty(lean_object* v_00_u03b1_333_, lean_object* v_cmp_334_, lean_object* v_t_335_){
_start:
{
if (lean_obj_tag(v_t_335_) == 0)
{
uint8_t v___x_336_; 
v___x_336_ = 0;
return v___x_336_;
}
else
{
uint8_t v___x_337_; 
v___x_337_ = 1;
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___boxed(lean_object* v_00_u03b1_338_, lean_object* v_cmp_339_, lean_object* v_t_340_){
_start:
{
uint8_t v_res_341_; lean_object* v_r_342_; 
v_res_341_ = l_Std_TreeSet_isEmpty(v_00_u03b1_338_, v_cmp_339_, v_t_340_);
lean_dec(v_t_340_);
lean_dec_ref(v_cmp_339_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_erase___redArg(lean_object* v_cmp_343_, lean_object* v_t_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_343_, v_a_345_, v_t_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_erase(lean_object* v_00_u03b1_347_, lean_object* v_cmp_348_, lean_object* v_t_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_348_, v_a_350_, v_t_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f___redArg(lean_object* v_cmp_352_, lean_object* v_t_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_352_, v_t_353_, v_a_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f(lean_object* v_00_u03b1_356_, lean_object* v_cmp_357_, lean_object* v_t_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_357_, v_t_358_, v_a_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get___redArg(lean_object* v_cmp_361_, lean_object* v_t_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_361_, v_t_362_, v_a_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get(lean_object* v_00_u03b1_365_, lean_object* v_cmp_366_, lean_object* v_t_367_, lean_object* v_a_368_, lean_object* v_h_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_366_, v_t_367_, v_a_368_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___redArg(lean_object* v_cmp_371_, lean_object* v_inst_372_, lean_object* v_t_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_371_, v_t_373_, v_a_374_, v_inst_372_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21(lean_object* v_00_u03b1_376_, lean_object* v_cmp_377_, lean_object* v_inst_378_, lean_object* v_t_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_377_, v_t_379_, v_a_380_, v_inst_378_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg(lean_object* v_cmp_382_, lean_object* v_t_383_, lean_object* v_a_384_, lean_object* v_fallback_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_382_, v_t_383_, v_a_384_, v_fallback_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg___boxed(lean_object* v_cmp_387_, lean_object* v_t_388_, lean_object* v_a_389_, lean_object* v_fallback_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_TreeSet_getD___redArg(v_cmp_387_, v_t_388_, v_a_389_, v_fallback_390_);
lean_dec(v_fallback_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD(lean_object* v_00_u03b1_392_, lean_object* v_cmp_393_, lean_object* v_t_394_, lean_object* v_a_395_, lean_object* v_fallback_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_393_, v_t_394_, v_a_395_, v_fallback_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___boxed(lean_object* v_00_u03b1_398_, lean_object* v_cmp_399_, lean_object* v_t_400_, lean_object* v_a_401_, lean_object* v_fallback_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_TreeSet_getD(v_00_u03b1_398_, v_cmp_399_, v_t_400_, v_a_401_, v_fallback_402_);
lean_dec(v_fallback_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg(lean_object* v_t_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg___boxed(lean_object* v_t_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_TreeSet_min_x3f___redArg(v_t_406_);
lean_dec(v_t_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f(lean_object* v_00_u03b1_408_, lean_object* v_cmp_409_, lean_object* v_t_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___boxed(lean_object* v_00_u03b1_412_, lean_object* v_cmp_413_, lean_object* v_t_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_TreeSet_min_x3f(v_00_u03b1_412_, v_cmp_413_, v_t_414_);
lean_dec(v_t_414_);
lean_dec_ref(v_cmp_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg(lean_object* v_t_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg___boxed(lean_object* v_t_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_TreeSet_min___redArg(v_t_418_);
lean_dec(v_t_418_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min(lean_object* v_00_u03b1_420_, lean_object* v_cmp_421_, lean_object* v_t_422_, lean_object* v_h_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___boxed(lean_object* v_00_u03b1_425_, lean_object* v_cmp_426_, lean_object* v_t_427_, lean_object* v_h_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_TreeSet_min(v_00_u03b1_425_, v_cmp_426_, v_t_427_, v_h_428_);
lean_dec(v_t_427_);
lean_dec_ref(v_cmp_426_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg(lean_object* v_inst_430_, lean_object* v_t_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_430_, v_t_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg___boxed(lean_object* v_inst_433_, lean_object* v_t_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_TreeSet_min_x21___redArg(v_inst_433_, v_t_434_);
lean_dec(v_t_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21(lean_object* v_00_u03b1_436_, lean_object* v_cmp_437_, lean_object* v_inst_438_, lean_object* v_t_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_438_, v_t_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___boxed(lean_object* v_00_u03b1_441_, lean_object* v_cmp_442_, lean_object* v_inst_443_, lean_object* v_t_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_TreeSet_min_x21(v_00_u03b1_441_, v_cmp_442_, v_inst_443_, v_t_444_);
lean_dec(v_t_444_);
lean_dec_ref(v_cmp_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg(lean_object* v_t_446_, lean_object* v_fallback_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_446_, v_fallback_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg___boxed(lean_object* v_t_449_, lean_object* v_fallback_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_TreeSet_minD___redArg(v_t_449_, v_fallback_450_);
lean_dec(v_fallback_450_);
lean_dec(v_t_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD(lean_object* v_00_u03b1_452_, lean_object* v_cmp_453_, lean_object* v_t_454_, lean_object* v_fallback_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_454_, v_fallback_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___boxed(lean_object* v_00_u03b1_457_, lean_object* v_cmp_458_, lean_object* v_t_459_, lean_object* v_fallback_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_TreeSet_minD(v_00_u03b1_457_, v_cmp_458_, v_t_459_, v_fallback_460_);
lean_dec(v_fallback_460_);
lean_dec(v_t_459_);
lean_dec_ref(v_cmp_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg(lean_object* v_t_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg___boxed(lean_object* v_t_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_TreeSet_max_x3f___redArg(v_t_464_);
lean_dec(v_t_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f(lean_object* v_00_u03b1_466_, lean_object* v_cmp_467_, lean_object* v_t_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___boxed(lean_object* v_00_u03b1_470_, lean_object* v_cmp_471_, lean_object* v_t_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_TreeSet_max_x3f(v_00_u03b1_470_, v_cmp_471_, v_t_472_);
lean_dec(v_t_472_);
lean_dec_ref(v_cmp_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg(lean_object* v_t_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg___boxed(lean_object* v_t_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_TreeSet_max___redArg(v_t_476_);
lean_dec(v_t_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max(lean_object* v_00_u03b1_478_, lean_object* v_cmp_479_, lean_object* v_t_480_, lean_object* v_h_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___boxed(lean_object* v_00_u03b1_483_, lean_object* v_cmp_484_, lean_object* v_t_485_, lean_object* v_h_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_TreeSet_max(v_00_u03b1_483_, v_cmp_484_, v_t_485_, v_h_486_);
lean_dec(v_t_485_);
lean_dec_ref(v_cmp_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg(lean_object* v_inst_488_, lean_object* v_t_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_488_, v_t_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg___boxed(lean_object* v_inst_491_, lean_object* v_t_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_TreeSet_max_x21___redArg(v_inst_491_, v_t_492_);
lean_dec(v_t_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21(lean_object* v_00_u03b1_494_, lean_object* v_cmp_495_, lean_object* v_inst_496_, lean_object* v_t_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_496_, v_t_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___boxed(lean_object* v_00_u03b1_499_, lean_object* v_cmp_500_, lean_object* v_inst_501_, lean_object* v_t_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_TreeSet_max_x21(v_00_u03b1_499_, v_cmp_500_, v_inst_501_, v_t_502_);
lean_dec(v_t_502_);
lean_dec_ref(v_cmp_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg(lean_object* v_t_504_, lean_object* v_fallback_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_504_, v_fallback_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg___boxed(lean_object* v_t_507_, lean_object* v_fallback_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_TreeSet_maxD___redArg(v_t_507_, v_fallback_508_);
lean_dec(v_fallback_508_);
lean_dec(v_t_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD(lean_object* v_00_u03b1_510_, lean_object* v_cmp_511_, lean_object* v_t_512_, lean_object* v_fallback_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_512_, v_fallback_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___boxed(lean_object* v_00_u03b1_515_, lean_object* v_cmp_516_, lean_object* v_t_517_, lean_object* v_fallback_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_TreeSet_maxD(v_00_u03b1_515_, v_cmp_516_, v_t_517_, v_fallback_518_);
lean_dec(v_fallback_518_);
lean_dec(v_t_517_);
lean_dec_ref(v_cmp_516_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg(lean_object* v_t_520_, lean_object* v_n_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_520_, v_n_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg___boxed(lean_object* v_t_523_, lean_object* v_n_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_TreeSet_atIdx_x3f___redArg(v_t_523_, v_n_524_);
lean_dec(v_t_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f(lean_object* v_00_u03b1_526_, lean_object* v_cmp_527_, lean_object* v_t_528_, lean_object* v_n_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_528_, v_n_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___boxed(lean_object* v_00_u03b1_531_, lean_object* v_cmp_532_, lean_object* v_t_533_, lean_object* v_n_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_TreeSet_atIdx_x3f(v_00_u03b1_531_, v_cmp_532_, v_t_533_, v_n_534_);
lean_dec(v_t_533_);
lean_dec_ref(v_cmp_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg(lean_object* v_t_536_, lean_object* v_n_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_536_, v_n_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg___boxed(lean_object* v_t_539_, lean_object* v_n_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_TreeSet_atIdx___redArg(v_t_539_, v_n_540_);
lean_dec(v_t_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx(lean_object* v_00_u03b1_542_, lean_object* v_cmp_543_, lean_object* v_t_544_, lean_object* v_n_545_, lean_object* v_h_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_544_, v_n_545_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___boxed(lean_object* v_00_u03b1_548_, lean_object* v_cmp_549_, lean_object* v_t_550_, lean_object* v_n_551_, lean_object* v_h_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_TreeSet_atIdx(v_00_u03b1_548_, v_cmp_549_, v_t_550_, v_n_551_, v_h_552_);
lean_dec(v_t_550_);
lean_dec_ref(v_cmp_549_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg(lean_object* v_inst_554_, lean_object* v_t_555_, lean_object* v_n_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_554_, v_t_555_, v_n_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg___boxed(lean_object* v_inst_558_, lean_object* v_t_559_, lean_object* v_n_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_TreeSet_atIdx_x21___redArg(v_inst_558_, v_t_559_, v_n_560_);
lean_dec(v_t_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21(lean_object* v_00_u03b1_562_, lean_object* v_cmp_563_, lean_object* v_inst_564_, lean_object* v_t_565_, lean_object* v_n_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_564_, v_t_565_, v_n_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___boxed(lean_object* v_00_u03b1_568_, lean_object* v_cmp_569_, lean_object* v_inst_570_, lean_object* v_t_571_, lean_object* v_n_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_TreeSet_atIdx_x21(v_00_u03b1_568_, v_cmp_569_, v_inst_570_, v_t_571_, v_n_572_);
lean_dec(v_t_571_);
lean_dec_ref(v_cmp_569_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg(lean_object* v_t_574_, lean_object* v_n_575_, lean_object* v_fallback_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_574_, v_n_575_, v_fallback_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg___boxed(lean_object* v_t_578_, lean_object* v_n_579_, lean_object* v_fallback_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_TreeSet_atIdxD___redArg(v_t_578_, v_n_579_, v_fallback_580_);
lean_dec(v_fallback_580_);
lean_dec(v_t_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD(lean_object* v_00_u03b1_582_, lean_object* v_cmp_583_, lean_object* v_t_584_, lean_object* v_n_585_, lean_object* v_fallback_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_584_, v_n_585_, v_fallback_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___boxed(lean_object* v_00_u03b1_588_, lean_object* v_cmp_589_, lean_object* v_t_590_, lean_object* v_n_591_, lean_object* v_fallback_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_TreeSet_atIdxD(v_00_u03b1_588_, v_cmp_589_, v_t_590_, v_n_591_, v_fallback_592_);
lean_dec(v_fallback_592_);
lean_dec(v_t_590_);
lean_dec_ref(v_cmp_589_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f___redArg(lean_object* v_cmp_594_, lean_object* v_t_595_, lean_object* v_k_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_box(0);
v___x_598_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_594_, v_k_596_, v___x_597_, v_t_595_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f(lean_object* v_00_u03b1_599_, lean_object* v_cmp_600_, lean_object* v_t_601_, lean_object* v_k_602_){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_box(0);
v___x_604_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_600_, v_k_602_, v___x_603_, v_t_601_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f___redArg(lean_object* v_cmp_605_, lean_object* v_t_606_, lean_object* v_k_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_box(0);
v___x_609_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_605_, v_k_607_, v___x_608_, v_t_606_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f(lean_object* v_00_u03b1_610_, lean_object* v_cmp_611_, lean_object* v_t_612_, lean_object* v_k_613_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_box(0);
v___x_615_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_611_, v_k_613_, v___x_614_, v_t_612_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f___redArg(lean_object* v_cmp_616_, lean_object* v_t_617_, lean_object* v_k_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_box(0);
v___x_620_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_616_, v_k_618_, v___x_619_, v_t_617_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f(lean_object* v_00_u03b1_621_, lean_object* v_cmp_622_, lean_object* v_t_623_, lean_object* v_k_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_box(0);
v___x_626_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_622_, v_k_624_, v___x_625_, v_t_623_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f___redArg(lean_object* v_cmp_627_, lean_object* v_t_628_, lean_object* v_k_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_box(0);
v___x_631_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_627_, v_k_629_, v___x_630_, v_t_628_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f(lean_object* v_00_u03b1_632_, lean_object* v_cmp_633_, lean_object* v_t_634_, lean_object* v_k_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(0);
v___x_637_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_633_, v_k_635_, v___x_636_, v_t_634_);
return v___x_637_;
}
}
static lean_object* _init_l_Std_TreeSet_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_641_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__2));
v___x_642_ = lean_unsigned_to_nat(14u);
v___x_643_ = lean_unsigned_to_nat(22u);
v___x_644_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__1));
v___x_645_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__0));
v___x_646_ = l_mkPanicMessageWithDecl(v___x_645_, v___x_644_, v___x_643_, v___x_642_, v___x_641_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___redArg(lean_object* v_cmp_647_, lean_object* v_inst_648_, lean_object* v_t_649_, lean_object* v_k_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_box(0);
v___x_652_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_647_, v_k_650_, v___x_651_, v_t_649_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_654_ = l_panic___redArg(v_inst_648_, v___x_653_);
return v___x_654_;
}
else
{
lean_object* v_val_655_; 
lean_dec(v_inst_648_);
v_val_655_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_655_);
lean_dec_ref(v___x_652_);
return v_val_655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21(lean_object* v_00_u03b1_656_, lean_object* v_cmp_657_, lean_object* v_inst_658_, lean_object* v_t_659_, lean_object* v_k_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_box(0);
v___x_662_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_657_, v_k_660_, v___x_661_, v_t_659_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg(lean_object* v_cmp_666_, lean_object* v_inst_667_, lean_object* v_t_668_, lean_object* v_k_669_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box(0);
v___x_671_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_666_, v_k_669_, v___x_670_, v_t_668_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_673_ = l_panic___redArg(v_inst_667_, v___x_672_);
return v___x_673_;
}
else
{
lean_object* v_val_674_; 
lean_dec(v_inst_667_);
v_val_674_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_val_674_);
lean_dec_ref(v___x_671_);
return v_val_674_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21(lean_object* v_00_u03b1_675_, lean_object* v_cmp_676_, lean_object* v_inst_677_, lean_object* v_t_678_, lean_object* v_k_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_box(0);
v___x_681_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_676_, v_k_679_, v___x_680_, v_t_678_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_683_ = l_panic___redArg(v_inst_677_, v___x_682_);
return v___x_683_;
}
else
{
lean_object* v_val_684_; 
lean_dec(v_inst_677_);
v_val_684_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_val_684_);
lean_dec_ref(v___x_681_);
return v_val_684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg(lean_object* v_cmp_685_, lean_object* v_inst_686_, lean_object* v_t_687_, lean_object* v_k_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_box(0);
v___x_690_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_685_, v_k_688_, v___x_689_, v_t_687_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_692_ = l_panic___redArg(v_inst_686_, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v_val_693_; 
lean_dec(v_inst_686_);
v_val_693_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_val_693_);
lean_dec_ref(v___x_690_);
return v_val_693_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21(lean_object* v_00_u03b1_694_, lean_object* v_cmp_695_, lean_object* v_inst_696_, lean_object* v_t_697_, lean_object* v_k_698_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_box(0);
v___x_700_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_695_, v_k_698_, v___x_699_, v_t_697_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_702_ = l_panic___redArg(v_inst_696_, v___x_701_);
return v___x_702_;
}
else
{
lean_object* v_val_703_; 
lean_dec(v_inst_696_);
v_val_703_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_val_703_);
lean_dec_ref(v___x_700_);
return v_val_703_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg(lean_object* v_cmp_704_, lean_object* v_inst_705_, lean_object* v_t_706_, lean_object* v_k_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_box(0);
v___x_709_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_704_, v_k_707_, v___x_708_, v_t_706_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_711_ = l_panic___redArg(v_inst_705_, v___x_710_);
return v___x_711_;
}
else
{
lean_object* v_val_712_; 
lean_dec(v_inst_705_);
v_val_712_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_val_712_);
lean_dec_ref(v___x_709_);
return v_val_712_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21(lean_object* v_00_u03b1_713_, lean_object* v_cmp_714_, lean_object* v_inst_715_, lean_object* v_t_716_, lean_object* v_k_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_box(0);
v___x_719_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_714_, v_k_717_, v___x_718_, v_t_716_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_721_ = l_panic___redArg(v_inst_715_, v___x_720_);
return v___x_721_;
}
else
{
lean_object* v_val_722_; 
lean_dec(v_inst_715_);
v_val_722_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_val_722_);
lean_dec_ref(v___x_719_);
return v_val_722_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg(lean_object* v_cmp_723_, lean_object* v_t_724_, lean_object* v_k_725_, lean_object* v_fallback_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_box(0);
v___x_728_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_723_, v_k_725_, v___x_727_, v_t_724_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_inc(v_fallback_726_);
return v_fallback_726_;
}
else
{
lean_object* v_val_729_; 
v_val_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_val_729_);
lean_dec_ref(v___x_728_);
return v_val_729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg___boxed(lean_object* v_cmp_730_, lean_object* v_t_731_, lean_object* v_k_732_, lean_object* v_fallback_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_TreeSet_getGED___redArg(v_cmp_730_, v_t_731_, v_k_732_, v_fallback_733_);
lean_dec(v_fallback_733_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED(lean_object* v_00_u03b1_735_, lean_object* v_cmp_736_, lean_object* v_t_737_, lean_object* v_k_738_, lean_object* v_fallback_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_box(0);
v___x_741_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_736_, v_k_738_, v___x_740_, v_t_737_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_inc(v_fallback_739_);
return v_fallback_739_;
}
else
{
lean_object* v_val_742_; 
v_val_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_val_742_);
lean_dec_ref(v___x_741_);
return v_val_742_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___boxed(lean_object* v_00_u03b1_743_, lean_object* v_cmp_744_, lean_object* v_t_745_, lean_object* v_k_746_, lean_object* v_fallback_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_TreeSet_getGED(v_00_u03b1_743_, v_cmp_744_, v_t_745_, v_k_746_, v_fallback_747_);
lean_dec(v_fallback_747_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg(lean_object* v_cmp_749_, lean_object* v_t_750_, lean_object* v_k_751_, lean_object* v_fallback_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_box(0);
v___x_754_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_749_, v_k_751_, v___x_753_, v_t_750_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_inc(v_fallback_752_);
return v_fallback_752_;
}
else
{
lean_object* v_val_755_; 
v_val_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_val_755_);
lean_dec_ref(v___x_754_);
return v_val_755_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg___boxed(lean_object* v_cmp_756_, lean_object* v_t_757_, lean_object* v_k_758_, lean_object* v_fallback_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_TreeSet_getGTD___redArg(v_cmp_756_, v_t_757_, v_k_758_, v_fallback_759_);
lean_dec(v_fallback_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD(lean_object* v_00_u03b1_761_, lean_object* v_cmp_762_, lean_object* v_t_763_, lean_object* v_k_764_, lean_object* v_fallback_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_box(0);
v___x_767_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_762_, v_k_764_, v___x_766_, v_t_763_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_inc(v_fallback_765_);
return v_fallback_765_;
}
else
{
lean_object* v_val_768_; 
v_val_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_val_768_);
lean_dec_ref(v___x_767_);
return v_val_768_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___boxed(lean_object* v_00_u03b1_769_, lean_object* v_cmp_770_, lean_object* v_t_771_, lean_object* v_k_772_, lean_object* v_fallback_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_TreeSet_getGTD(v_00_u03b1_769_, v_cmp_770_, v_t_771_, v_k_772_, v_fallback_773_);
lean_dec(v_fallback_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg(lean_object* v_cmp_775_, lean_object* v_t_776_, lean_object* v_k_777_, lean_object* v_fallback_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_box(0);
v___x_780_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_775_, v_k_777_, v___x_779_, v_t_776_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_inc(v_fallback_778_);
return v_fallback_778_;
}
else
{
lean_object* v_val_781_; 
v_val_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_val_781_);
lean_dec_ref(v___x_780_);
return v_val_781_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg___boxed(lean_object* v_cmp_782_, lean_object* v_t_783_, lean_object* v_k_784_, lean_object* v_fallback_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_TreeSet_getLED___redArg(v_cmp_782_, v_t_783_, v_k_784_, v_fallback_785_);
lean_dec(v_fallback_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED(lean_object* v_00_u03b1_787_, lean_object* v_cmp_788_, lean_object* v_t_789_, lean_object* v_k_790_, lean_object* v_fallback_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_box(0);
v___x_793_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_788_, v_k_790_, v___x_792_, v_t_789_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_inc(v_fallback_791_);
return v_fallback_791_;
}
else
{
lean_object* v_val_794_; 
v_val_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_val_794_);
lean_dec_ref(v___x_793_);
return v_val_794_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___boxed(lean_object* v_00_u03b1_795_, lean_object* v_cmp_796_, lean_object* v_t_797_, lean_object* v_k_798_, lean_object* v_fallback_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_TreeSet_getLED(v_00_u03b1_795_, v_cmp_796_, v_t_797_, v_k_798_, v_fallback_799_);
lean_dec(v_fallback_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg(lean_object* v_cmp_801_, lean_object* v_t_802_, lean_object* v_k_803_, lean_object* v_fallback_804_){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_box(0);
v___x_806_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_801_, v_k_803_, v___x_805_, v_t_802_);
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
lean_dec_ref(v___x_806_);
return v_val_807_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg___boxed(lean_object* v_cmp_808_, lean_object* v_t_809_, lean_object* v_k_810_, lean_object* v_fallback_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_TreeSet_getLTD___redArg(v_cmp_808_, v_t_809_, v_k_810_, v_fallback_811_);
lean_dec(v_fallback_811_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD(lean_object* v_00_u03b1_813_, lean_object* v_cmp_814_, lean_object* v_t_815_, lean_object* v_k_816_, lean_object* v_fallback_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_box(0);
v___x_819_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_814_, v_k_816_, v___x_818_, v_t_815_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_inc(v_fallback_817_);
return v_fallback_817_;
}
else
{
lean_object* v_val_820_; 
v_val_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_val_820_);
lean_dec_ref(v___x_819_);
return v_val_820_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___boxed(lean_object* v_00_u03b1_821_, lean_object* v_cmp_822_, lean_object* v_t_823_, lean_object* v_k_824_, lean_object* v_fallback_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_TreeSet_getLTD(v_00_u03b1_821_, v_cmp_822_, v_t_823_, v_k_824_, v_fallback_825_);
lean_dec(v_fallback_825_);
return v_res_826_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_filter___redArg___lam__0(lean_object* v_f_827_, lean_object* v_a_828_, lean_object* v_x_829_){
_start:
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = lean_apply_1(v_f_827_, v_a_828_);
v___x_831_ = lean_unbox(v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg___lam__0___boxed(lean_object* v_f_832_, lean_object* v_a_833_, lean_object* v_x_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Std_TreeSet_filter___redArg___lam__0(v_f_832_, v_a_833_, v_x_834_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg(lean_object* v_f_837_, lean_object* v_m_838_){
_start:
{
lean_object* v___f_839_; lean_object* v___x_840_; 
v___f_839_ = lean_alloc_closure((void*)(l_Std_TreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_839_, 0, v_f_837_);
v___x_840_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_839_, v_m_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter(lean_object* v_00_u03b1_841_, lean_object* v_cmp_842_, lean_object* v_f_843_, lean_object* v_m_844_){
_start:
{
lean_object* v___f_845_; lean_object* v___x_846_; 
v___f_845_ = lean_alloc_closure((void*)(l_Std_TreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_845_, 0, v_f_843_);
v___x_846_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_845_, v_m_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___boxed(lean_object* v_00_u03b1_847_, lean_object* v_cmp_848_, lean_object* v_f_849_, lean_object* v_m_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Std_TreeSet_filter(v_00_u03b1_847_, v_cmp_848_, v_f_849_, v_m_850_);
lean_dec_ref(v_cmp_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg___lam__0(lean_object* v_f_852_, lean_object* v_c_853_, lean_object* v_a_854_, lean_object* v_x_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lean_apply_2(v_f_852_, v_c_853_, v_a_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg(lean_object* v_inst_857_, lean_object* v_f_858_, lean_object* v_init_859_, lean_object* v_t_860_){
_start:
{
lean_object* v___f_861_; lean_object* v___x_862_; 
v___f_861_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_861_, 0, v_f_858_);
v___x_862_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_857_, v___f_861_, v_init_859_, v_t_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM(lean_object* v_00_u03b1_863_, lean_object* v_cmp_864_, lean_object* v_m_865_, lean_object* v_00_u03b4_866_, lean_object* v_inst_867_, lean_object* v_f_868_, lean_object* v_init_869_, lean_object* v_t_870_){
_start:
{
lean_object* v___f_871_; lean_object* v___x_872_; 
v___f_871_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_871_, 0, v_f_868_);
v___x_872_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_867_, v___f_871_, v_init_869_, v_t_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___boxed(lean_object* v_00_u03b1_873_, lean_object* v_cmp_874_, lean_object* v_m_875_, lean_object* v_00_u03b4_876_, lean_object* v_inst_877_, lean_object* v_f_878_, lean_object* v_init_879_, lean_object* v_t_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_TreeSet_foldlM(v_00_u03b1_873_, v_cmp_874_, v_m_875_, v_00_u03b4_876_, v_inst_877_, v_f_878_, v_init_879_, v_t_880_);
lean_dec_ref(v_cmp_874_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___redArg(lean_object* v_f_882_, lean_object* v_init_883_, lean_object* v_t_884_){
_start:
{
lean_object* v___f_885_; lean_object* v___x_886_; 
v___f_885_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_885_, 0, v_f_882_);
v___x_886_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_885_, v_init_883_, v_t_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl(lean_object* v_00_u03b1_887_, lean_object* v_cmp_888_, lean_object* v_00_u03b4_889_, lean_object* v_f_890_, lean_object* v_init_891_, lean_object* v_t_892_){
_start:
{
lean_object* v___f_893_; lean_object* v___x_894_; 
v___f_893_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_893_, 0, v_f_890_);
v___x_894_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_893_, v_init_891_, v_t_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___boxed(lean_object* v_00_u03b1_895_, lean_object* v_cmp_896_, lean_object* v_00_u03b4_897_, lean_object* v_f_898_, lean_object* v_init_899_, lean_object* v_t_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_TreeSet_foldl(v_00_u03b1_895_, v_cmp_896_, v_00_u03b4_897_, v_f_898_, v_init_899_, v_t_900_);
lean_dec_ref(v_cmp_896_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg___lam__0(lean_object* v_f_902_, lean_object* v_a_903_, lean_object* v_x_904_, lean_object* v_acc_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = lean_apply_2(v_f_902_, v_a_903_, v_acc_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg(lean_object* v_inst_907_, lean_object* v_f_908_, lean_object* v_init_909_, lean_object* v_t_910_){
_start:
{
lean_object* v___f_911_; lean_object* v___x_912_; 
v___f_911_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_911_, 0, v_f_908_);
v___x_912_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_907_, v___f_911_, v_init_909_, v_t_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM(lean_object* v_00_u03b1_913_, lean_object* v_cmp_914_, lean_object* v_m_915_, lean_object* v_00_u03b4_916_, lean_object* v_inst_917_, lean_object* v_f_918_, lean_object* v_init_919_, lean_object* v_t_920_){
_start:
{
lean_object* v___f_921_; lean_object* v___x_922_; 
v___f_921_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_921_, 0, v_f_918_);
v___x_922_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_917_, v___f_921_, v_init_919_, v_t_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___boxed(lean_object* v_00_u03b1_923_, lean_object* v_cmp_924_, lean_object* v_m_925_, lean_object* v_00_u03b4_926_, lean_object* v_inst_927_, lean_object* v_f_928_, lean_object* v_init_929_, lean_object* v_t_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_TreeSet_foldrM(v_00_u03b1_923_, v_cmp_924_, v_m_925_, v_00_u03b4_926_, v_inst_927_, v_f_928_, v_init_929_, v_t_930_);
lean_dec_ref(v_cmp_924_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg___lam__0(lean_object* v_f_932_, lean_object* v_x1_933_, lean_object* v_x2_934_, lean_object* v_x3_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = lean_apply_2(v_f_932_, v_x1_933_, v_x3_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg(lean_object* v_f_956_, lean_object* v_init_957_, lean_object* v_t_958_){
_start:
{
lean_object* v___f_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___f_959_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_959_, 0, v_f_956_);
v___x_960_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_961_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_960_, v___f_959_, v_init_957_, v_t_958_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr(lean_object* v_00_u03b1_962_, lean_object* v_cmp_963_, lean_object* v_00_u03b4_964_, lean_object* v_f_965_, lean_object* v_init_966_, lean_object* v_t_967_){
_start:
{
lean_object* v___f_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___f_968_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_968_, 0, v_f_965_);
v___x_969_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_970_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_969_, v___f_968_, v_init_966_, v_t_967_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___boxed(lean_object* v_00_u03b1_971_, lean_object* v_cmp_972_, lean_object* v_00_u03b4_973_, lean_object* v_f_974_, lean_object* v_init_975_, lean_object* v_t_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_TreeSet_foldr(v_00_u03b1_971_, v_cmp_972_, v_00_u03b4_973_, v_f_974_, v_init_975_, v_t_976_);
lean_dec_ref(v_cmp_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg___lam__0(lean_object* v_f_978_, lean_object* v_cmp_979_, lean_object* v_x_980_, lean_object* v_a_981_, lean_object* v_b_982_){
_start:
{
lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_998_; 
v_fst_983_ = lean_ctor_get(v_x_980_, 0);
v_snd_984_ = lean_ctor_get(v_x_980_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_998_ == 0)
{
v___x_986_ = v_x_980_;
v_isShared_987_ = v_isSharedCheck_998_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_snd_984_);
lean_inc(v_fst_983_);
lean_dec(v_x_980_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_998_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; uint8_t v___x_989_; 
lean_inc(v_a_981_);
v___x_988_ = lean_apply_1(v_f_978_, v_a_981_);
v___x_989_ = lean_unbox(v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_979_, v_a_981_, v_b_982_, v_snd_984_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___x_990_);
v___x_992_ = v___x_986_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_fst_983_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
else
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_979_, v_a_981_, v_b_982_, v_fst_983_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_994_);
v___x_996_ = v___x_986_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_snd_984_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg(lean_object* v_cmp_1001_, lean_object* v_f_1002_, lean_object* v_t_1003_){
_start:
{
lean_object* v___f_1004_; lean_object* v___x_1005_; lean_object* v_p_1006_; lean_object* v_fst_1007_; lean_object* v_snd_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
v___f_1004_ = lean_alloc_closure((void*)(l_Std_TreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1004_, 0, v_f_1002_);
lean_closure_set(v___f_1004_, 1, v_cmp_1001_);
v___x_1005_ = ((lean_object*)(l_Std_TreeSet_partition___redArg___closed__0));
v_p_1006_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1004_, v___x_1005_, v_t_1003_);
v_fst_1007_ = lean_ctor_get(v_p_1006_, 0);
v_snd_1008_ = lean_ctor_get(v_p_1006_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_p_1006_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v_p_1006_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_snd_1008_);
lean_inc(v_fst_1007_);
lean_dec(v_p_1006_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_fst_1007_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_snd_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition(lean_object* v_00_u03b1_1016_, lean_object* v_cmp_1017_, lean_object* v_f_1018_, lean_object* v_t_1019_){
_start:
{
lean_object* v___f_1020_; lean_object* v___x_1021_; lean_object* v_p_1022_; lean_object* v_fst_1023_; lean_object* v_snd_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v___f_1020_ = lean_alloc_closure((void*)(l_Std_TreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1020_, 0, v_f_1018_);
lean_closure_set(v___f_1020_, 1, v_cmp_1017_);
v___x_1021_ = ((lean_object*)(l_Std_TreeSet_partition___redArg___closed__0));
v_p_1022_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1020_, v___x_1021_, v_t_1019_);
v_fst_1023_ = lean_ctor_get(v_p_1022_, 0);
v_snd_1024_ = lean_ctor_get(v_p_1022_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_p_1022_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v_p_1022_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_snd_1024_);
lean_inc(v_fst_1023_);
lean_dec(v_p_1022_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_fst_1023_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_snd_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg___lam__0(lean_object* v_f_1032_, lean_object* v_x_1033_, lean_object* v_k_1034_, lean_object* v_v_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_apply_1(v_f_1032_, v_k_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg(lean_object* v_inst_1037_, lean_object* v_f_1038_, lean_object* v_t_1039_){
_start:
{
lean_object* v___f_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___f_1040_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1040_, 0, v_f_1038_);
v___x_1041_ = lean_box(0);
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1037_, v___f_1040_, v___x_1041_, v_t_1039_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM(lean_object* v_00_u03b1_1043_, lean_object* v_cmp_1044_, lean_object* v_m_1045_, lean_object* v_inst_1046_, lean_object* v_f_1047_, lean_object* v_t_1048_){
_start:
{
lean_object* v___f_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___f_1049_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1049_, 0, v_f_1047_);
v___x_1050_ = lean_box(0);
v___x_1051_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1046_, v___f_1049_, v___x_1050_, v_t_1048_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___boxed(lean_object* v_00_u03b1_1052_, lean_object* v_cmp_1053_, lean_object* v_m_1054_, lean_object* v_inst_1055_, lean_object* v_f_1056_, lean_object* v_t_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Std_TreeSet_forM(v_00_u03b1_1052_, v_cmp_1053_, v_m_1054_, v_inst_1055_, v_f_1056_, v_t_1057_);
lean_dec_ref(v_cmp_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__0(lean_object* v_f_1059_, lean_object* v_a_1060_, lean_object* v_b_1061_, lean_object* v_c_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_apply_2(v_f_1059_, v_a_1060_, v_c_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__1(lean_object* v_toPure_1064_, lean_object* v_____do__lift_1065_){
_start:
{
lean_object* v_a_1066_; lean_object* v___x_1067_; 
v_a_1066_ = lean_ctor_get(v_____do__lift_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v_____do__lift_1065_);
v___x_1067_ = lean_apply_2(v_toPure_1064_, lean_box(0), v_a_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg(lean_object* v_inst_1068_, lean_object* v_f_1069_, lean_object* v_init_1070_, lean_object* v_t_1071_){
_start:
{
lean_object* v_toApplicative_1072_; lean_object* v_toBind_1073_; lean_object* v_toPure_1074_; lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; 
v_toApplicative_1072_ = lean_ctor_get(v_inst_1068_, 0);
v_toBind_1073_ = lean_ctor_get(v_inst_1068_, 1);
lean_inc(v_toBind_1073_);
v_toPure_1074_ = lean_ctor_get(v_toApplicative_1072_, 1);
lean_inc(v_toPure_1074_);
v___f_1075_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1075_, 0, v_f_1069_);
v___x_1076_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1068_, v___f_1075_, v_init_1070_, v_t_1071_);
v___f_1077_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1077_, 0, v_toPure_1074_);
v___x_1078_ = lean_apply_4(v_toBind_1073_, lean_box(0), lean_box(0), v___x_1076_, v___f_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn(lean_object* v_00_u03b1_1079_, lean_object* v_cmp_1080_, lean_object* v_00_u03b4_1081_, lean_object* v_m_1082_, lean_object* v_inst_1083_, lean_object* v_f_1084_, lean_object* v_init_1085_, lean_object* v_t_1086_){
_start:
{
lean_object* v_toApplicative_1087_; lean_object* v_toBind_1088_; lean_object* v_toPure_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___f_1092_; lean_object* v___x_1093_; 
v_toApplicative_1087_ = lean_ctor_get(v_inst_1083_, 0);
v_toBind_1088_ = lean_ctor_get(v_inst_1083_, 1);
lean_inc(v_toBind_1088_);
v_toPure_1089_ = lean_ctor_get(v_toApplicative_1087_, 1);
lean_inc(v_toPure_1089_);
v___f_1090_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1090_, 0, v_f_1084_);
v___x_1091_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1083_, v___f_1090_, v_init_1085_, v_t_1086_);
v___f_1092_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1092_, 0, v_toPure_1089_);
v___x_1093_ = lean_apply_4(v_toBind_1088_, lean_box(0), lean_box(0), v___x_1091_, v___f_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___boxed(lean_object* v_00_u03b1_1094_, lean_object* v_cmp_1095_, lean_object* v_00_u03b4_1096_, lean_object* v_m_1097_, lean_object* v_inst_1098_, lean_object* v_f_1099_, lean_object* v_init_1100_, lean_object* v_t_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_TreeSet_forIn(v_00_u03b1_1094_, v_cmp_1095_, v_00_u03b4_1096_, v_m_1097_, v_inst_1098_, v_f_1099_, v_init_1100_, v_t_1101_);
lean_dec_ref(v_cmp_1095_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg___lam__1(lean_object* v_inst_1103_, lean_object* v_t_1104_, lean_object* v_f_1105_){
_start:
{
lean_object* v___f_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___f_1106_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1106_, 0, v_f_1105_);
v___x_1107_ = lean_box(0);
v___x_1108_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1103_, v___f_1106_, v___x_1107_, v_t_1104_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg(lean_object* v_inst_1109_){
_start:
{
lean_object* v___f_1110_; 
v___f_1110_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1110_, 0, v_inst_1109_);
return v___f_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad(lean_object* v_00_u03b1_1111_, lean_object* v_cmp_1112_, lean_object* v_m_1113_, lean_object* v_inst_1114_){
_start:
{
lean_object* v___f_1115_; 
v___f_1115_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1115_, 0, v_inst_1114_);
return v___f_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_cmp_1117_, lean_object* v_m_1118_, lean_object* v_inst_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_TreeSet_instForMOfMonad(v_00_u03b1_1116_, v_cmp_1117_, v_m_1118_, v_inst_1119_);
lean_dec_ref(v_cmp_1117_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg___lam__2(lean_object* v_inst_1121_, lean_object* v_00_u03b2_1122_, lean_object* v_m_1123_, lean_object* v_init_1124_, lean_object* v_f_1125_){
_start:
{
lean_object* v_toApplicative_1126_; lean_object* v_toBind_1127_; lean_object* v_toPure_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; 
v_toApplicative_1126_ = lean_ctor_get(v_inst_1121_, 0);
v_toBind_1127_ = lean_ctor_get(v_inst_1121_, 1);
lean_inc(v_toBind_1127_);
v_toPure_1128_ = lean_ctor_get(v_toApplicative_1126_, 1);
lean_inc(v_toPure_1128_);
v___f_1129_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1129_, 0, v_f_1125_);
v___x_1130_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1121_, v___f_1129_, v_init_1124_, v_m_1123_);
v___f_1131_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1131_, 0, v_toPure_1128_);
v___x_1132_ = lean_apply_4(v_toBind_1127_, lean_box(0), lean_box(0), v___x_1130_, v___f_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg(lean_object* v_inst_1133_){
_start:
{
lean_object* v___f_1134_; 
v___f_1134_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1134_, 0, v_inst_1133_);
return v___f_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad(lean_object* v_00_u03b1_1135_, lean_object* v_cmp_1136_, lean_object* v_m_1137_, lean_object* v_inst_1138_){
_start:
{
lean_object* v___f_1139_; 
v___f_1139_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1139_, 0, v_inst_1138_);
return v___f_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_1140_, lean_object* v_cmp_1141_, lean_object* v_m_1142_, lean_object* v_inst_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_TreeSet_instForInOfMonad(v_00_u03b1_1140_, v_cmp_1141_, v_m_1142_, v_inst_1143_);
lean_dec_ref(v_cmp_1141_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0(lean_object* v_p_1145_, lean_object* v___x_1146_, lean_object* v___x_1147_, lean_object* v_a_1148_, lean_object* v_b_1149_, lean_object* v_acc_1150_){
_start:
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_apply_1(v_p_1145_, v_a_1148_);
v___x_1152_ = lean_unbox(v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1146_);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec_ref(v___x_1146_);
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1151_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___x_1147_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0___boxed(lean_object* v_p_1157_, lean_object* v___x_1158_, lean_object* v___x_1159_, lean_object* v_a_1160_, lean_object* v_b_1161_, lean_object* v_acc_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_TreeSet_any___redArg___lam__0(v_p_1157_, v___x_1158_, v___x_1159_, v_a_1160_, v_b_1161_, v_acc_1162_);
lean_dec_ref(v_acc_1162_);
return v_res_1163_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_any___redArg(lean_object* v_t_1167_, lean_object* v_p_1168_){
_start:
{
lean_object* v___y_1170_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v_a_1180_; 
v___x_1175_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1176_ = lean_box(0);
v___x_1177_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1178_ = lean_alloc_closure((void*)(l_Std_TreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1178_, 0, v_p_1168_);
lean_closure_set(v___f_1178_, 1, v___x_1177_);
lean_closure_set(v___f_1178_, 2, v___x_1176_);
v___x_1179_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1175_, v___f_1178_, v___x_1177_, v_t_1167_);
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___y_1170_ = v_a_1180_;
goto v___jp_1169_;
v___jp_1169_:
{
lean_object* v_fst_1171_; 
v_fst_1171_ = lean_ctor_get(v___y_1170_, 0);
lean_inc(v_fst_1171_);
lean_dec_ref(v___y_1170_);
if (lean_obj_tag(v_fst_1171_) == 0)
{
uint8_t v___x_1172_; 
v___x_1172_ = 0;
return v___x_1172_;
}
else
{
lean_object* v_val_1173_; uint8_t v___x_1174_; 
v_val_1173_ = lean_ctor_get(v_fst_1171_, 0);
lean_inc(v_val_1173_);
lean_dec_ref(v_fst_1171_);
v___x_1174_ = lean_unbox(v_val_1173_);
lean_dec(v_val_1173_);
return v___x_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___boxed(lean_object* v_t_1181_, lean_object* v_p_1182_){
_start:
{
uint8_t v_res_1183_; lean_object* v_r_1184_; 
v_res_1183_ = l_Std_TreeSet_any___redArg(v_t_1181_, v_p_1182_);
v_r_1184_ = lean_box(v_res_1183_);
return v_r_1184_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_any(lean_object* v_00_u03b1_1185_, lean_object* v_cmp_1186_, lean_object* v_t_1187_, lean_object* v_p_1188_){
_start:
{
lean_object* v___y_1190_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___f_1198_; lean_object* v___x_1199_; lean_object* v_a_1200_; 
v___x_1195_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1196_ = lean_box(0);
v___x_1197_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1198_ = lean_alloc_closure((void*)(l_Std_TreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1198_, 0, v_p_1188_);
lean_closure_set(v___f_1198_, 1, v___x_1197_);
lean_closure_set(v___f_1198_, 2, v___x_1196_);
v___x_1199_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1195_, v___f_1198_, v___x_1197_, v_t_1187_);
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___y_1190_ = v_a_1200_;
goto v___jp_1189_;
v___jp_1189_:
{
lean_object* v_fst_1191_; 
v_fst_1191_ = lean_ctor_get(v___y_1190_, 0);
lean_inc(v_fst_1191_);
lean_dec_ref(v___y_1190_);
if (lean_obj_tag(v_fst_1191_) == 0)
{
uint8_t v___x_1192_; 
v___x_1192_ = 0;
return v___x_1192_;
}
else
{
lean_object* v_val_1193_; uint8_t v___x_1194_; 
v_val_1193_ = lean_ctor_get(v_fst_1191_, 0);
lean_inc(v_val_1193_);
lean_dec_ref(v_fst_1191_);
v___x_1194_ = lean_unbox(v_val_1193_);
lean_dec(v_val_1193_);
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___boxed(lean_object* v_00_u03b1_1201_, lean_object* v_cmp_1202_, lean_object* v_t_1203_, lean_object* v_p_1204_){
_start:
{
uint8_t v_res_1205_; lean_object* v_r_1206_; 
v_res_1205_ = l_Std_TreeSet_any(v_00_u03b1_1201_, v_cmp_1202_, v_t_1203_, v_p_1204_);
lean_dec_ref(v_cmp_1202_);
v_r_1206_ = lean_box(v_res_1205_);
return v_r_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0(lean_object* v_p_1207_, lean_object* v___x_1208_, lean_object* v___x_1209_, lean_object* v_a_1210_, lean_object* v_b_1211_, lean_object* v_acc_1212_){
_start:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_apply_1(v_p_1207_, v_a_1210_);
v___x_1214_ = lean_unbox(v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v___x_1209_);
v___x_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1208_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1209_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0___boxed(lean_object* v_p_1219_, lean_object* v___x_1220_, lean_object* v___x_1221_, lean_object* v_a_1222_, lean_object* v_b_1223_, lean_object* v_acc_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Std_TreeSet_all___redArg___lam__0(v_p_1219_, v___x_1220_, v___x_1221_, v_a_1222_, v_b_1223_, v_acc_1224_);
lean_dec_ref(v_acc_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_all___redArg(lean_object* v_t_1226_, lean_object* v_p_1227_){
_start:
{
lean_object* v___y_1229_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; lean_object* v_a_1239_; 
v___x_1234_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1235_ = lean_box(0);
v___x_1236_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1237_ = lean_alloc_closure((void*)(l_Std_TreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1237_, 0, v_p_1227_);
lean_closure_set(v___f_1237_, 1, v___x_1235_);
lean_closure_set(v___f_1237_, 2, v___x_1236_);
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
v___x_1231_ = 1;
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
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___boxed(lean_object* v_t_1240_, lean_object* v_p_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Std_TreeSet_all___redArg(v_t_1240_, v_p_1241_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_all(lean_object* v_00_u03b1_1244_, lean_object* v_cmp_1245_, lean_object* v_t_1246_, lean_object* v_p_1247_){
_start:
{
lean_object* v___y_1249_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___f_1257_; lean_object* v___x_1258_; lean_object* v_a_1259_; 
v___x_1254_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1255_ = lean_box(0);
v___x_1256_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1257_ = lean_alloc_closure((void*)(l_Std_TreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1257_, 0, v_p_1247_);
lean_closure_set(v___f_1257_, 1, v___x_1255_);
lean_closure_set(v___f_1257_, 2, v___x_1256_);
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
v___x_1251_ = 1;
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
LEAN_EXPORT lean_object* l_Std_TreeSet_all___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_cmp_1261_, lean_object* v_t_1262_, lean_object* v_p_1263_){
_start:
{
uint8_t v_res_1264_; lean_object* v_r_1265_; 
v_res_1264_ = l_Std_TreeSet_all(v_00_u03b1_1260_, v_cmp_1261_, v_t_1262_, v_p_1263_);
lean_dec_ref(v_cmp_1261_);
v_r_1265_ = lean_box(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg___lam__0(lean_object* v_x1_1266_, lean_object* v_x2_1267_, lean_object* v_x3_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_x1_1266_);
lean_ctor_set(v___x_1269_, 1, v_x3_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg(lean_object* v_t_1271_){
_start:
{
lean_object* v___f_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___f_1272_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___x_1273_ = lean_box(0);
v___x_1274_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1275_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1274_, v___f_1272_, v___x_1273_, v_t_1271_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList(lean_object* v_00_u03b1_1276_, lean_object* v_cmp_1277_, lean_object* v_t_1278_){
_start:
{
lean_object* v___f_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___f_1279_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___x_1280_ = lean_box(0);
v___x_1281_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1282_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1281_, v___f_1279_, v___x_1280_, v_t_1278_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_cmp_1284_, lean_object* v_t_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_TreeSet_toList(v_00_u03b1_1283_, v_cmp_1284_, v_t_1285_);
lean_dec_ref(v_cmp_1284_);
return v_res_1286_;
}
}
static lean_object* _init_l_Std_TreeSet_ofList___auto__1(void){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__26, &l_Std_TreeSet___auto__1___closed__26_once, _init_l_Std_TreeSet___auto__1___closed__26);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(lean_object* v_cmp_1288_, lean_object* v_k_1289_, lean_object* v_v_1290_, lean_object* v_t_1291_){
_start:
{
if (lean_obj_tag(v_t_1291_) == 0)
{
lean_object* v_size_1292_; lean_object* v_k_1293_; lean_object* v_v_1294_; lean_object* v_l_1295_; lean_object* v_r_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1577_; 
v_size_1292_ = lean_ctor_get(v_t_1291_, 0);
v_k_1293_ = lean_ctor_get(v_t_1291_, 1);
v_v_1294_ = lean_ctor_get(v_t_1291_, 2);
v_l_1295_ = lean_ctor_get(v_t_1291_, 3);
v_r_1296_ = lean_ctor_get(v_t_1291_, 4);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_t_1291_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1298_ = v_t_1291_;
v_isShared_1299_ = v_isSharedCheck_1577_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_r_1296_);
lean_inc(v_l_1295_);
lean_inc(v_v_1294_);
lean_inc(v_k_1293_);
lean_inc(v_size_1292_);
lean_dec(v_t_1291_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1577_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
lean_inc_ref(v_cmp_1288_);
lean_inc(v_k_1293_);
lean_inc(v_k_1289_);
v___x_1300_ = lean_apply_2(v_cmp_1288_, v_k_1289_, v_k_1293_);
v___x_1301_ = lean_unbox(v___x_1300_);
switch(v___x_1301_)
{
case 0:
{
lean_object* v_impl_1302_; lean_object* v___x_1303_; 
lean_dec(v_size_1292_);
v_impl_1302_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1288_, v_k_1289_, v_v_1290_, v_l_1295_);
v___x_1303_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1296_) == 0)
{
lean_object* v_size_1304_; lean_object* v_size_1305_; lean_object* v_k_1306_; lean_object* v_v_1307_; lean_object* v_l_1308_; lean_object* v_r_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_size_1304_ = lean_ctor_get(v_r_1296_, 0);
v_size_1305_ = lean_ctor_get(v_impl_1302_, 0);
lean_inc(v_size_1305_);
v_k_1306_ = lean_ctor_get(v_impl_1302_, 1);
lean_inc(v_k_1306_);
v_v_1307_ = lean_ctor_get(v_impl_1302_, 2);
lean_inc(v_v_1307_);
v_l_1308_ = lean_ctor_get(v_impl_1302_, 3);
lean_inc(v_l_1308_);
v_r_1309_ = lean_ctor_get(v_impl_1302_, 4);
lean_inc(v_r_1309_);
v___x_1310_ = lean_unsigned_to_nat(3u);
v___x_1311_ = lean_nat_mul(v___x_1310_, v_size_1304_);
v___x_1312_ = lean_nat_dec_lt(v___x_1311_, v_size_1305_);
lean_dec(v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_dec(v_r_1309_);
lean_dec(v_l_1308_);
lean_dec(v_v_1307_);
lean_dec(v_k_1306_);
v___x_1313_ = lean_nat_add(v___x_1303_, v_size_1305_);
lean_dec(v_size_1305_);
v___x_1314_ = lean_nat_add(v___x_1313_, v_size_1304_);
lean_dec(v___x_1313_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 3, v_impl_1302_);
lean_ctor_set(v___x_1298_, 0, v___x_1314_);
v___x_1316_ = v___x_1298_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1317_, 3, v_impl_1302_);
lean_ctor_set(v_reuseFailAlloc_1317_, 4, v_r_1296_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
else
{
lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1383_; 
v_isSharedCheck_1383_ = !lean_is_exclusive(v_impl_1302_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; lean_object* v_unused_1385_; lean_object* v_unused_1386_; lean_object* v_unused_1387_; lean_object* v_unused_1388_; 
v_unused_1384_ = lean_ctor_get(v_impl_1302_, 4);
lean_dec(v_unused_1384_);
v_unused_1385_ = lean_ctor_get(v_impl_1302_, 3);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v_impl_1302_, 2);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_impl_1302_, 1);
lean_dec(v_unused_1387_);
v_unused_1388_ = lean_ctor_get(v_impl_1302_, 0);
lean_dec(v_unused_1388_);
v___x_1319_ = v_impl_1302_;
v_isShared_1320_ = v_isSharedCheck_1383_;
goto v_resetjp_1318_;
}
else
{
lean_dec(v_impl_1302_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1383_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_size_1321_; lean_object* v_size_1322_; lean_object* v_k_1323_; lean_object* v_v_1324_; lean_object* v_l_1325_; lean_object* v_r_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_size_1321_ = lean_ctor_get(v_l_1308_, 0);
v_size_1322_ = lean_ctor_get(v_r_1309_, 0);
v_k_1323_ = lean_ctor_get(v_r_1309_, 1);
v_v_1324_ = lean_ctor_get(v_r_1309_, 2);
v_l_1325_ = lean_ctor_get(v_r_1309_, 3);
v_r_1326_ = lean_ctor_get(v_r_1309_, 4);
v___x_1327_ = lean_unsigned_to_nat(2u);
v___x_1328_ = lean_nat_mul(v___x_1327_, v_size_1321_);
v___x_1329_ = lean_nat_dec_lt(v_size_1322_, v___x_1328_);
lean_dec(v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1358_; 
lean_inc(v_r_1326_);
lean_inc(v_l_1325_);
lean_inc(v_v_1324_);
lean_inc(v_k_1323_);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_r_1309_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; lean_object* v_unused_1360_; lean_object* v_unused_1361_; lean_object* v_unused_1362_; lean_object* v_unused_1363_; 
v_unused_1359_ = lean_ctor_get(v_r_1309_, 4);
lean_dec(v_unused_1359_);
v_unused_1360_ = lean_ctor_get(v_r_1309_, 3);
lean_dec(v_unused_1360_);
v_unused_1361_ = lean_ctor_get(v_r_1309_, 2);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_r_1309_, 1);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v_r_1309_, 0);
lean_dec(v_unused_1363_);
v___x_1331_ = v_r_1309_;
v_isShared_1332_ = v_isSharedCheck_1358_;
goto v_resetjp_1330_;
}
else
{
lean_dec(v_r_1309_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1358_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___x_1346_; lean_object* v___y_1348_; 
v___x_1333_ = lean_nat_add(v___x_1303_, v_size_1305_);
lean_dec(v_size_1305_);
v___x_1334_ = lean_nat_add(v___x_1333_, v_size_1304_);
lean_dec(v___x_1333_);
v___x_1346_ = lean_nat_add(v___x_1303_, v_size_1321_);
if (lean_obj_tag(v_l_1325_) == 0)
{
lean_object* v_size_1356_; 
v_size_1356_ = lean_ctor_get(v_l_1325_, 0);
lean_inc(v_size_1356_);
v___y_1348_ = v_size_1356_;
goto v___jp_1347_;
}
else
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_unsigned_to_nat(0u);
v___y_1348_ = v___x_1357_;
goto v___jp_1347_;
}
v___jp_1335_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = lean_nat_add(v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec(v___y_1337_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 4, v_r_1296_);
lean_ctor_set(v___x_1331_, 3, v_r_1326_);
lean_ctor_set(v___x_1331_, 2, v_v_1294_);
lean_ctor_set(v___x_1331_, 1, v_k_1293_);
lean_ctor_set(v___x_1331_, 0, v___x_1339_);
v___x_1341_ = v___x_1331_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v_r_1326_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v_r_1296_);
v___x_1341_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1343_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 4, v___x_1341_);
lean_ctor_set(v___x_1319_, 3, v___y_1336_);
lean_ctor_set(v___x_1319_, 2, v_v_1324_);
lean_ctor_set(v___x_1319_, 1, v_k_1323_);
lean_ctor_set(v___x_1319_, 0, v___x_1334_);
v___x_1343_ = v___x_1319_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_k_1323_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_v_1324_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v___y_1336_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
v___jp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_nat_add(v___x_1346_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec(v___x_1346_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_l_1325_);
lean_ctor_set(v___x_1298_, 3, v_l_1308_);
lean_ctor_set(v___x_1298_, 2, v_v_1307_);
lean_ctor_set(v___x_1298_, 1, v_k_1306_);
lean_ctor_set(v___x_1298_, 0, v___x_1349_);
v___x_1351_ = v___x_1298_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_k_1306_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_v_1307_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_l_1308_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v_l_1325_);
v___x_1351_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_nat_add(v___x_1303_, v_size_1304_);
if (lean_obj_tag(v_r_1326_) == 0)
{
lean_object* v_size_1353_; 
v_size_1353_ = lean_ctor_get(v_r_1326_, 0);
lean_inc(v_size_1353_);
v___y_1336_ = v___x_1351_;
v___y_1337_ = v___x_1352_;
v___y_1338_ = v_size_1353_;
goto v___jp_1335_;
}
else
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_unsigned_to_nat(0u);
v___y_1336_ = v___x_1351_;
v___y_1337_ = v___x_1352_;
v___y_1338_ = v___x_1354_;
goto v___jp_1335_;
}
}
}
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
lean_del_object(v___x_1298_);
v___x_1364_ = lean_nat_add(v___x_1303_, v_size_1305_);
lean_dec(v_size_1305_);
v___x_1365_ = lean_nat_add(v___x_1364_, v_size_1304_);
lean_dec(v___x_1364_);
v___x_1366_ = lean_nat_add(v___x_1303_, v_size_1304_);
v___x_1367_ = lean_nat_add(v___x_1366_, v_size_1322_);
lean_dec(v___x_1366_);
lean_inc_ref(v_r_1296_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 4, v_r_1296_);
lean_ctor_set(v___x_1319_, 3, v_r_1309_);
lean_ctor_set(v___x_1319_, 2, v_v_1294_);
lean_ctor_set(v___x_1319_, 1, v_k_1293_);
lean_ctor_set(v___x_1319_, 0, v___x_1367_);
v___x_1369_ = v___x_1319_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_r_1309_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v_r_1296_);
v___x_1369_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_isSharedCheck_1376_ = !lean_is_exclusive(v_r_1296_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; lean_object* v_unused_1378_; lean_object* v_unused_1379_; lean_object* v_unused_1380_; lean_object* v_unused_1381_; 
v_unused_1377_ = lean_ctor_get(v_r_1296_, 4);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_r_1296_, 3);
lean_dec(v_unused_1378_);
v_unused_1379_ = lean_ctor_get(v_r_1296_, 2);
lean_dec(v_unused_1379_);
v_unused_1380_ = lean_ctor_get(v_r_1296_, 1);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v_r_1296_, 0);
lean_dec(v_unused_1381_);
v___x_1371_ = v_r_1296_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_r_1296_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v___x_1369_);
lean_ctor_set(v___x_1371_, 3, v_l_1308_);
lean_ctor_set(v___x_1371_, 2, v_v_1307_);
lean_ctor_set(v___x_1371_, 1, v_k_1306_);
lean_ctor_set(v___x_1371_, 0, v___x_1365_);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_k_1306_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_v_1307_);
lean_ctor_set(v_reuseFailAlloc_1375_, 3, v_l_1308_);
lean_ctor_set(v_reuseFailAlloc_1375_, 4, v___x_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1389_; 
v_l_1389_ = lean_ctor_get(v_impl_1302_, 3);
lean_inc(v_l_1389_);
if (lean_obj_tag(v_l_1389_) == 0)
{
lean_object* v_r_1390_; lean_object* v_k_1391_; lean_object* v_v_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1403_; 
v_r_1390_ = lean_ctor_get(v_impl_1302_, 4);
v_k_1391_ = lean_ctor_get(v_impl_1302_, 1);
v_v_1392_ = lean_ctor_get(v_impl_1302_, 2);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_impl_1302_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; lean_object* v_unused_1405_; 
v_unused_1404_ = lean_ctor_get(v_impl_1302_, 3);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_impl_1302_, 0);
lean_dec(v_unused_1405_);
v___x_1394_ = v_impl_1302_;
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_r_1390_);
lean_inc(v_v_1392_);
lean_inc(v_k_1391_);
lean_dec(v_impl_1302_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1390_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 3, v_r_1390_);
lean_ctor_set(v___x_1394_, 2, v_v_1294_);
lean_ctor_set(v___x_1394_, 1, v_k_1293_);
lean_ctor_set(v___x_1394_, 0, v___x_1303_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_r_1390_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v_r_1390_);
v___x_1398_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1400_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v___x_1398_);
lean_ctor_set(v___x_1298_, 3, v_l_1389_);
lean_ctor_set(v___x_1298_, 2, v_v_1392_);
lean_ctor_set(v___x_1298_, 1, v_k_1391_);
lean_ctor_set(v___x_1298_, 0, v___x_1396_);
v___x_1400_ = v___x_1298_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_l_1389_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
else
{
lean_object* v_r_1406_; 
v_r_1406_ = lean_ctor_get(v_impl_1302_, 4);
lean_inc(v_r_1406_);
if (lean_obj_tag(v_r_1406_) == 0)
{
lean_object* v_k_1407_; lean_object* v_v_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1431_; 
v_k_1407_ = lean_ctor_get(v_impl_1302_, 1);
v_v_1408_ = lean_ctor_get(v_impl_1302_, 2);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_impl_1302_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; lean_object* v_unused_1433_; lean_object* v_unused_1434_; 
v_unused_1432_ = lean_ctor_get(v_impl_1302_, 4);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_impl_1302_, 3);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_impl_1302_, 0);
lean_dec(v_unused_1434_);
v___x_1410_ = v_impl_1302_;
v_isShared_1411_ = v_isSharedCheck_1431_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_v_1408_);
lean_inc(v_k_1407_);
lean_dec(v_impl_1302_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1431_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_k_1412_; lean_object* v_v_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1427_; 
v_k_1412_ = lean_ctor_get(v_r_1406_, 1);
v_v_1413_ = lean_ctor_get(v_r_1406_, 2);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_r_1406_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; lean_object* v_unused_1429_; lean_object* v_unused_1430_; 
v_unused_1428_ = lean_ctor_get(v_r_1406_, 4);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_r_1406_, 3);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_r_1406_, 0);
lean_dec(v_unused_1430_);
v___x_1415_ = v_r_1406_;
v_isShared_1416_ = v_isSharedCheck_1427_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_v_1413_);
lean_inc(v_k_1412_);
lean_dec(v_r_1406_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1427_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = lean_unsigned_to_nat(3u);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v_l_1389_);
lean_ctor_set(v___x_1415_, 3, v_l_1389_);
lean_ctor_set(v___x_1415_, 2, v_v_1408_);
lean_ctor_set(v___x_1415_, 1, v_k_1407_);
lean_ctor_set(v___x_1415_, 0, v___x_1303_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_l_1389_);
lean_ctor_set(v_reuseFailAlloc_1426_, 4, v_l_1389_);
v___x_1419_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1421_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 4, v_l_1389_);
lean_ctor_set(v___x_1410_, 2, v_v_1294_);
lean_ctor_set(v___x_1410_, 1, v_k_1293_);
lean_ctor_set(v___x_1410_, 0, v___x_1303_);
v___x_1421_ = v___x_1410_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_l_1389_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_l_1389_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v___x_1421_);
lean_ctor_set(v___x_1298_, 3, v___x_1419_);
lean_ctor_set(v___x_1298_, 2, v_v_1413_);
lean_ctor_set(v___x_1298_, 1, v_k_1412_);
lean_ctor_set(v___x_1298_, 0, v___x_1417_);
v___x_1423_ = v___x_1298_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_k_1412_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_v_1413_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1424_, 4, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = lean_unsigned_to_nat(2u);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_r_1406_);
lean_ctor_set(v___x_1298_, 3, v_impl_1302_);
lean_ctor_set(v___x_1298_, 0, v___x_1435_);
v___x_1437_ = v___x_1298_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v_impl_1302_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v_r_1406_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1440_; 
lean_dec(v_v_1294_);
lean_dec(v_k_1293_);
lean_dec_ref(v_cmp_1288_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 2, v_v_1290_);
lean_ctor_set(v___x_1298_, 1, v_k_1289_);
v___x_1440_ = v___x_1298_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_size_1292_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_k_1289_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_v_1290_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_l_1295_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_r_1296_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
default: 
{
lean_object* v_impl_1442_; lean_object* v___x_1443_; 
lean_dec(v_size_1292_);
v_impl_1442_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1288_, v_k_1289_, v_v_1290_, v_r_1296_);
v___x_1443_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1295_) == 0)
{
lean_object* v_size_1444_; lean_object* v_size_1445_; lean_object* v_k_1446_; lean_object* v_v_1447_; lean_object* v_l_1448_; lean_object* v_r_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_size_1444_ = lean_ctor_get(v_l_1295_, 0);
v_size_1445_ = lean_ctor_get(v_impl_1442_, 0);
lean_inc(v_size_1445_);
v_k_1446_ = lean_ctor_get(v_impl_1442_, 1);
lean_inc(v_k_1446_);
v_v_1447_ = lean_ctor_get(v_impl_1442_, 2);
lean_inc(v_v_1447_);
v_l_1448_ = lean_ctor_get(v_impl_1442_, 3);
lean_inc(v_l_1448_);
v_r_1449_ = lean_ctor_get(v_impl_1442_, 4);
lean_inc(v_r_1449_);
v___x_1450_ = lean_unsigned_to_nat(3u);
v___x_1451_ = lean_nat_mul(v___x_1450_, v_size_1444_);
v___x_1452_ = lean_nat_dec_lt(v___x_1451_, v_size_1445_);
lean_dec(v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
lean_dec(v_r_1449_);
lean_dec(v_l_1448_);
lean_dec(v_v_1447_);
lean_dec(v_k_1446_);
v___x_1453_ = lean_nat_add(v___x_1443_, v_size_1444_);
v___x_1454_ = lean_nat_add(v___x_1453_, v_size_1445_);
lean_dec(v_size_1445_);
lean_dec(v___x_1453_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_impl_1442_);
lean_ctor_set(v___x_1298_, 0, v___x_1454_);
v___x_1456_ = v___x_1298_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_l_1295_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_impl_1442_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
else
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1521_; 
v_isSharedCheck_1521_ = !lean_is_exclusive(v_impl_1442_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; lean_object* v_unused_1526_; 
v_unused_1522_ = lean_ctor_get(v_impl_1442_, 4);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_impl_1442_, 3);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_impl_1442_, 2);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v_impl_1442_, 1);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_impl_1442_, 0);
lean_dec(v_unused_1526_);
v___x_1459_ = v_impl_1442_;
v_isShared_1460_ = v_isSharedCheck_1521_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v_impl_1442_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1521_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v_size_1461_; lean_object* v_k_1462_; lean_object* v_v_1463_; lean_object* v_l_1464_; lean_object* v_r_1465_; lean_object* v_size_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_size_1461_ = lean_ctor_get(v_l_1448_, 0);
v_k_1462_ = lean_ctor_get(v_l_1448_, 1);
v_v_1463_ = lean_ctor_get(v_l_1448_, 2);
v_l_1464_ = lean_ctor_get(v_l_1448_, 3);
v_r_1465_ = lean_ctor_get(v_l_1448_, 4);
v_size_1466_ = lean_ctor_get(v_r_1449_, 0);
v___x_1467_ = lean_unsigned_to_nat(2u);
v___x_1468_ = lean_nat_mul(v___x_1467_, v_size_1466_);
v___x_1469_ = lean_nat_dec_lt(v_size_1461_, v___x_1468_);
lean_dec(v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1497_; 
lean_inc(v_r_1465_);
lean_inc(v_l_1464_);
lean_inc(v_v_1463_);
lean_inc(v_k_1462_);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_l_1448_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; lean_object* v_unused_1499_; lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; 
v_unused_1498_ = lean_ctor_get(v_l_1448_, 4);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_l_1448_, 3);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_l_1448_, 2);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_l_1448_, 1);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_l_1448_, 0);
lean_dec(v_unused_1502_);
v___x_1471_ = v_l_1448_;
v_isShared_1472_ = v_isSharedCheck_1497_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v_l_1448_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1497_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1487_; 
v___x_1473_ = lean_nat_add(v___x_1443_, v_size_1444_);
v___x_1474_ = lean_nat_add(v___x_1473_, v_size_1445_);
lean_dec(v_size_1445_);
if (lean_obj_tag(v_l_1464_) == 0)
{
lean_object* v_size_1495_; 
v_size_1495_ = lean_ctor_get(v_l_1464_, 0);
lean_inc(v_size_1495_);
v___y_1487_ = v_size_1495_;
goto v___jp_1486_;
}
else
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_unsigned_to_nat(0u);
v___y_1487_ = v___x_1496_;
goto v___jp_1486_;
}
v___jp_1475_:
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1479_ = lean_nat_add(v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec(v___y_1477_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 4, v_r_1449_);
lean_ctor_set(v___x_1471_, 3, v_r_1465_);
lean_ctor_set(v___x_1471_, 2, v_v_1447_);
lean_ctor_set(v___x_1471_, 1, v_k_1446_);
lean_ctor_set(v___x_1471_, 0, v___x_1479_);
v___x_1481_ = v___x_1471_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1446_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1447_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_r_1465_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_r_1449_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v___x_1481_);
lean_ctor_set(v___x_1459_, 3, v___y_1476_);
lean_ctor_set(v___x_1459_, 2, v_v_1463_);
lean_ctor_set(v___x_1459_, 1, v_k_1462_);
lean_ctor_set(v___x_1459_, 0, v___x_1474_);
v___x_1483_ = v___x_1459_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1462_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1463_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v___y_1476_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
v___jp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1488_ = lean_nat_add(v___x_1473_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec(v___x_1473_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_l_1464_);
lean_ctor_set(v___x_1298_, 0, v___x_1488_);
v___x_1490_ = v___x_1298_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v_l_1295_);
lean_ctor_set(v_reuseFailAlloc_1494_, 4, v_l_1464_);
v___x_1490_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_nat_add(v___x_1443_, v_size_1466_);
if (lean_obj_tag(v_r_1465_) == 0)
{
lean_object* v_size_1492_; 
v_size_1492_ = lean_ctor_get(v_r_1465_, 0);
lean_inc(v_size_1492_);
v___y_1476_ = v___x_1490_;
v___y_1477_ = v___x_1491_;
v___y_1478_ = v_size_1492_;
goto v___jp_1475_;
}
else
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_unsigned_to_nat(0u);
v___y_1476_ = v___x_1490_;
v___y_1477_ = v___x_1491_;
v___y_1478_ = v___x_1493_;
goto v___jp_1475_;
}
}
}
}
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
lean_del_object(v___x_1298_);
v___x_1503_ = lean_nat_add(v___x_1443_, v_size_1444_);
v___x_1504_ = lean_nat_add(v___x_1503_, v_size_1445_);
lean_dec(v_size_1445_);
v___x_1505_ = lean_nat_add(v___x_1503_, v_size_1461_);
lean_dec(v___x_1503_);
lean_inc_ref(v_l_1295_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v_l_1448_);
lean_ctor_set(v___x_1459_, 3, v_l_1295_);
lean_ctor_set(v___x_1459_, 2, v_v_1294_);
lean_ctor_set(v___x_1459_, 1, v_k_1293_);
lean_ctor_set(v___x_1459_, 0, v___x_1505_);
v___x_1507_ = v___x_1459_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_l_1295_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v_l_1448_);
v___x_1507_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
v_isSharedCheck_1514_ = !lean_is_exclusive(v_l_1295_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; 
v_unused_1515_ = lean_ctor_get(v_l_1295_, 4);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_l_1295_, 3);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_l_1295_, 2);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_l_1295_, 1);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_l_1295_, 0);
lean_dec(v_unused_1519_);
v___x_1509_ = v_l_1295_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v_l_1295_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 4, v_r_1449_);
lean_ctor_set(v___x_1509_, 3, v___x_1507_);
lean_ctor_set(v___x_1509_, 2, v_v_1447_);
lean_ctor_set(v___x_1509_, 1, v_k_1446_);
lean_ctor_set(v___x_1509_, 0, v___x_1504_);
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_k_1446_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_v_1447_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v_r_1449_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1527_; 
v_l_1527_ = lean_ctor_get(v_impl_1442_, 3);
lean_inc(v_l_1527_);
if (lean_obj_tag(v_l_1527_) == 0)
{
lean_object* v_r_1528_; lean_object* v_k_1529_; lean_object* v_v_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1553_; 
v_r_1528_ = lean_ctor_get(v_impl_1442_, 4);
v_k_1529_ = lean_ctor_get(v_impl_1442_, 1);
v_v_1530_ = lean_ctor_get(v_impl_1442_, 2);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_impl_1442_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; lean_object* v_unused_1555_; 
v_unused_1554_ = lean_ctor_get(v_impl_1442_, 3);
lean_dec(v_unused_1554_);
v_unused_1555_ = lean_ctor_get(v_impl_1442_, 0);
lean_dec(v_unused_1555_);
v___x_1532_ = v_impl_1442_;
v_isShared_1533_ = v_isSharedCheck_1553_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_r_1528_);
lean_inc(v_v_1530_);
lean_inc(v_k_1529_);
lean_dec(v_impl_1442_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1553_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v_k_1534_; lean_object* v_v_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1549_; 
v_k_1534_ = lean_ctor_get(v_l_1527_, 1);
v_v_1535_ = lean_ctor_get(v_l_1527_, 2);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_l_1527_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; lean_object* v_unused_1551_; lean_object* v_unused_1552_; 
v_unused_1550_ = lean_ctor_get(v_l_1527_, 4);
lean_dec(v_unused_1550_);
v_unused_1551_ = lean_ctor_get(v_l_1527_, 3);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v_l_1527_, 0);
lean_dec(v_unused_1552_);
v___x_1537_ = v_l_1527_;
v_isShared_1538_ = v_isSharedCheck_1549_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_v_1535_);
lean_inc(v_k_1534_);
lean_dec(v_l_1527_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1549_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1528_, 2);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 4, v_r_1528_);
lean_ctor_set(v___x_1537_, 3, v_r_1528_);
lean_ctor_set(v___x_1537_, 2, v_v_1294_);
lean_ctor_set(v___x_1537_, 1, v_k_1293_);
lean_ctor_set(v___x_1537_, 0, v___x_1443_);
v___x_1541_ = v___x_1537_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_r_1528_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_r_1528_);
v___x_1541_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1543_; 
lean_inc(v_r_1528_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 3, v_r_1528_);
lean_ctor_set(v___x_1532_, 0, v___x_1443_);
v___x_1543_ = v___x_1532_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_k_1529_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_v_1530_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_r_1528_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_r_1528_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v___x_1543_);
lean_ctor_set(v___x_1298_, 3, v___x_1541_);
lean_ctor_set(v___x_1298_, 2, v_v_1535_);
lean_ctor_set(v___x_1298_, 1, v_k_1534_);
lean_ctor_set(v___x_1298_, 0, v___x_1539_);
v___x_1545_ = v___x_1298_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_k_1534_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_v_1535_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
}
else
{
lean_object* v_r_1556_; 
v_r_1556_ = lean_ctor_get(v_impl_1442_, 4);
lean_inc(v_r_1556_);
if (lean_obj_tag(v_r_1556_) == 0)
{
lean_object* v_k_1557_; lean_object* v_v_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1569_; 
v_k_1557_ = lean_ctor_get(v_impl_1442_, 1);
v_v_1558_ = lean_ctor_get(v_impl_1442_, 2);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_impl_1442_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; lean_object* v_unused_1571_; lean_object* v_unused_1572_; 
v_unused_1570_ = lean_ctor_get(v_impl_1442_, 4);
lean_dec(v_unused_1570_);
v_unused_1571_ = lean_ctor_get(v_impl_1442_, 3);
lean_dec(v_unused_1571_);
v_unused_1572_ = lean_ctor_get(v_impl_1442_, 0);
lean_dec(v_unused_1572_);
v___x_1560_ = v_impl_1442_;
v_isShared_1561_ = v_isSharedCheck_1569_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_v_1558_);
lean_inc(v_k_1557_);
lean_dec(v_impl_1442_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1569_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = lean_unsigned_to_nat(3u);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 4, v_l_1527_);
lean_ctor_set(v___x_1560_, 2, v_v_1294_);
lean_ctor_set(v___x_1560_, 1, v_k_1293_);
lean_ctor_set(v___x_1560_, 0, v___x_1443_);
v___x_1564_ = v___x_1560_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1568_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1568_, 3, v_l_1527_);
lean_ctor_set(v_reuseFailAlloc_1568_, 4, v_l_1527_);
v___x_1564_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1566_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_r_1556_);
lean_ctor_set(v___x_1298_, 3, v___x_1564_);
lean_ctor_set(v___x_1298_, 2, v_v_1558_);
lean_ctor_set(v___x_1298_, 1, v_k_1557_);
lean_ctor_set(v___x_1298_, 0, v___x_1562_);
v___x_1566_ = v___x_1298_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_k_1557_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_v_1558_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_r_1556_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1573_ = lean_unsigned_to_nat(2u);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_impl_1442_);
lean_ctor_set(v___x_1298_, 3, v_r_1556_);
lean_ctor_set(v___x_1298_, 0, v___x_1573_);
v___x_1575_ = v___x_1298_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_k_1293_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v_v_1294_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v_r_1556_);
lean_ctor_set(v_reuseFailAlloc_1576_, 4, v_impl_1442_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
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
lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec_ref(v_cmp_1288_);
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v_k_1289_);
lean_ctor_set(v___x_1579_, 2, v_v_1290_);
lean_ctor_set(v___x_1579_, 3, v_t_1291_);
lean_ctor_set(v___x_1579_, 4, v_t_1291_);
return v___x_1579_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(lean_object* v_cmp_1580_, lean_object* v_k_1581_, lean_object* v_t_1582_){
_start:
{
if (lean_obj_tag(v_t_1582_) == 0)
{
lean_object* v_k_1583_; lean_object* v_l_1584_; lean_object* v_r_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_k_1583_ = lean_ctor_get(v_t_1582_, 1);
lean_inc(v_k_1583_);
v_l_1584_ = lean_ctor_get(v_t_1582_, 3);
lean_inc(v_l_1584_);
v_r_1585_ = lean_ctor_get(v_t_1582_, 4);
lean_inc(v_r_1585_);
lean_dec_ref(v_t_1582_);
lean_inc_ref(v_cmp_1580_);
lean_inc(v_k_1581_);
v___x_1586_ = lean_apply_2(v_cmp_1580_, v_k_1581_, v_k_1583_);
v___x_1587_ = lean_unbox(v___x_1586_);
switch(v___x_1587_)
{
case 0:
{
lean_dec(v_r_1585_);
v_t_1582_ = v_l_1584_;
goto _start;
}
case 1:
{
uint8_t v___x_1589_; 
lean_dec(v_r_1585_);
lean_dec(v_l_1584_);
lean_dec(v_k_1581_);
lean_dec_ref(v_cmp_1580_);
v___x_1589_ = 1;
return v___x_1589_;
}
default: 
{
lean_dec(v_l_1584_);
v_t_1582_ = v_r_1585_;
goto _start;
}
}
}
else
{
uint8_t v___x_1591_; 
lean_dec(v_k_1581_);
lean_dec_ref(v_cmp_1580_);
v___x_1591_ = 0;
return v___x_1591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg___boxed(lean_object* v_cmp_1592_, lean_object* v_k_1593_, lean_object* v_t_1594_){
_start:
{
uint8_t v_res_1595_; lean_object* v_r_1596_; 
v_res_1595_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1592_, v_k_1593_, v_t_1594_);
v_r_1596_ = lean_box(v_res_1595_);
return v_r_1596_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(lean_object* v_cmp_1597_, lean_object* v_as_x27_1598_, lean_object* v_b_1599_){
_start:
{
if (lean_obj_tag(v_as_x27_1598_) == 0)
{
lean_dec_ref(v_cmp_1597_);
return v_b_1599_;
}
else
{
lean_object* v_head_1600_; lean_object* v_tail_1601_; uint8_t v___x_1602_; 
v_head_1600_ = lean_ctor_get(v_as_x27_1598_, 0);
lean_inc(v_head_1600_);
v_tail_1601_ = lean_ctor_get(v_as_x27_1598_, 1);
lean_inc(v_tail_1601_);
lean_dec_ref(v_as_x27_1598_);
lean_inc(v_b_1599_);
lean_inc(v_head_1600_);
lean_inc_ref(v_cmp_1597_);
v___x_1602_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1597_, v_head_1600_, v_b_1599_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_box(0);
lean_inc_ref(v_cmp_1597_);
v___x_1604_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1597_, v_head_1600_, v___x_1603_, v_b_1599_);
v_as_x27_1598_ = v_tail_1601_;
v_b_1599_ = v___x_1604_;
goto _start;
}
else
{
lean_dec(v_head_1600_);
v_as_x27_1598_ = v_tail_1601_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___redArg(lean_object* v_l_1607_, lean_object* v_cmp_1608_){
_start:
{
lean_object* v_r_1609_; lean_object* v___x_1610_; 
v_r_1609_ = lean_box(1);
v___x_1610_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1608_, v_l_1607_, v_r_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList(lean_object* v_00_u03b1_1611_, lean_object* v_l_1612_, lean_object* v_cmp_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Std_TreeSet_ofList___redArg(v_l_1612_, v_cmp_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(lean_object* v_00_u03b1_1615_, lean_object* v_cmp_1616_, lean_object* v_00_u03b2_1617_, lean_object* v_k_1618_, lean_object* v_t_1619_){
_start:
{
uint8_t v___x_1620_; 
v___x_1620_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1616_, v_k_1618_, v_t_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___boxed(lean_object* v_00_u03b1_1621_, lean_object* v_cmp_1622_, lean_object* v_00_u03b2_1623_, lean_object* v_k_1624_, lean_object* v_t_1625_){
_start:
{
uint8_t v_res_1626_; lean_object* v_r_1627_; 
v_res_1626_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(v_00_u03b1_1621_, v_cmp_1622_, v_00_u03b2_1623_, v_k_1624_, v_t_1625_);
v_r_1627_ = lean_box(v_res_1626_);
return v_r_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1(lean_object* v_00_u03b1_1628_, lean_object* v_cmp_1629_, lean_object* v_00_u03b2_1630_, lean_object* v_k_1631_, lean_object* v_v_1632_, lean_object* v_t_1633_, lean_object* v_hl_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1629_, v_k_1631_, v_v_1632_, v_t_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(lean_object* v_00_u03b1_1636_, lean_object* v_cmp_1637_, lean_object* v_as_1638_, lean_object* v_as_x27_1639_, lean_object* v_b_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1637_, v_as_x27_1639_, v_b_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___boxed(lean_object* v_00_u03b1_1643_, lean_object* v_cmp_1644_, lean_object* v_as_1645_, lean_object* v_as_x27_1646_, lean_object* v_b_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(v_00_u03b1_1643_, v_cmp_1644_, v_as_1645_, v_as_x27_1646_, v_b_1647_, v_a_1648_);
lean_dec(v_as_1645_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg___lam__0(lean_object* v_l_1650_, lean_object* v_k_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_array_push(v_l_1650_, v_k_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg(lean_object* v_t_1655_){
_start:
{
lean_object* v___f_1656_; lean_object* v___y_1658_; 
v___f_1656_ = ((lean_object*)(l_Std_TreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1655_) == 0)
{
lean_object* v_size_1661_; 
v_size_1661_ = lean_ctor_get(v_t_1655_, 0);
lean_inc(v_size_1661_);
v___y_1658_ = v_size_1661_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_unsigned_to_nat(0u);
v___y_1658_ = v___x_1662_;
goto v___jp_1657_;
}
v___jp_1657_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = lean_mk_empty_array_with_capacity(v___y_1658_);
lean_dec(v___y_1658_);
v___x_1660_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1656_, v___x_1659_, v_t_1655_);
return v___x_1660_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray(lean_object* v_00_u03b1_1663_, lean_object* v_cmp_1664_, lean_object* v_t_1665_){
_start:
{
lean_object* v___f_1666_; lean_object* v___y_1668_; 
v___f_1666_ = ((lean_object*)(l_Std_TreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1665_) == 0)
{
lean_object* v_size_1671_; 
v_size_1671_ = lean_ctor_get(v_t_1665_, 0);
lean_inc(v_size_1671_);
v___y_1668_ = v_size_1671_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_unsigned_to_nat(0u);
v___y_1668_ = v___x_1672_;
goto v___jp_1667_;
}
v___jp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_mk_empty_array_with_capacity(v___y_1668_);
lean_dec(v___y_1668_);
v___x_1670_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1666_, v___x_1669_, v_t_1665_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___boxed(lean_object* v_00_u03b1_1673_, lean_object* v_cmp_1674_, lean_object* v_t_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Std_TreeSet_toArray(v_00_u03b1_1673_, v_cmp_1674_, v_t_1675_);
lean_dec_ref(v_cmp_1674_);
return v_res_1676_;
}
}
static lean_object* _init_l_Std_TreeSet_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__26, &l_Std_TreeSet___auto__1___closed__26_once, _init_l_Std_TreeSet___auto__1___closed__26);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(lean_object* v_cmp_1678_, lean_object* v_as_1679_, size_t v_sz_1680_, size_t v_i_1681_, lean_object* v_b_1682_){
_start:
{
lean_object* v___y_1684_; uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_lt(v_i_1681_, v_sz_1680_);
if (v___x_1688_ == 0)
{
lean_dec_ref(v_cmp_1678_);
return v_b_1682_;
}
else
{
lean_object* v_a_1689_; uint8_t v___x_1690_; 
v_a_1689_ = lean_array_uget_borrowed(v_as_1679_, v_i_1681_);
lean_inc(v_b_1682_);
lean_inc(v_a_1689_);
lean_inc_ref(v_cmp_1678_);
v___x_1690_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1678_, v_a_1689_, v_b_1682_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_box(0);
lean_inc(v_a_1689_);
lean_inc_ref(v_cmp_1678_);
v___x_1692_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1678_, v_a_1689_, v___x_1691_, v_b_1682_);
v___y_1684_ = v___x_1692_;
goto v___jp_1683_;
}
else
{
v___y_1684_ = v_b_1682_;
goto v___jp_1683_;
}
}
v___jp_1683_:
{
size_t v___x_1685_; size_t v___x_1686_; 
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1681_, v___x_1685_);
v_i_1681_ = v___x_1686_;
v_b_1682_ = v___y_1684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg___boxed(lean_object* v_cmp_1693_, lean_object* v_as_1694_, lean_object* v_sz_1695_, lean_object* v_i_1696_, lean_object* v_b_1697_){
_start:
{
size_t v_sz_boxed_1698_; size_t v_i_boxed_1699_; lean_object* v_res_1700_; 
v_sz_boxed_1698_ = lean_unbox_usize(v_sz_1695_);
lean_dec(v_sz_1695_);
v_i_boxed_1699_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1693_, v_as_1694_, v_sz_boxed_1698_, v_i_boxed_1699_, v_b_1697_);
lean_dec_ref(v_as_1694_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg(lean_object* v_a_1701_, lean_object* v_cmp_1702_){
_start:
{
lean_object* v_r_1703_; size_t v_sz_1704_; size_t v___x_1705_; lean_object* v___x_1706_; 
v_r_1703_ = lean_box(1);
v_sz_1704_ = lean_array_size(v_a_1701_);
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1702_, v_a_1701_, v_sz_1704_, v___x_1705_, v_r_1703_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg___boxed(lean_object* v_a_1707_, lean_object* v_cmp_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Std_TreeSet_ofArray___redArg(v_a_1707_, v_cmp_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray(lean_object* v_00_u03b1_1710_, lean_object* v_a_1711_, lean_object* v_cmp_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Std_TreeSet_ofArray___redArg(v_a_1711_, v_cmp_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___boxed(lean_object* v_00_u03b1_1714_, lean_object* v_a_1715_, lean_object* v_cmp_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Std_TreeSet_ofArray(v_00_u03b1_1714_, v_a_1715_, v_cmp_1716_);
lean_dec_ref(v_a_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(lean_object* v_00_u03b1_1718_, lean_object* v_cmp_1719_, lean_object* v_as_1720_, size_t v_sz_1721_, size_t v_i_1722_, lean_object* v_b_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1719_, v_as_1720_, v_sz_1721_, v_i_1722_, v_b_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___boxed(lean_object* v_00_u03b1_1725_, lean_object* v_cmp_1726_, lean_object* v_as_1727_, lean_object* v_sz_1728_, lean_object* v_i_1729_, lean_object* v_b_1730_){
_start:
{
size_t v_sz_boxed_1731_; size_t v_i_boxed_1732_; lean_object* v_res_1733_; 
v_sz_boxed_1731_ = lean_unbox_usize(v_sz_1728_);
lean_dec(v_sz_1728_);
v_i_boxed_1732_ = lean_unbox_usize(v_i_1729_);
lean_dec(v_i_1729_);
v_res_1733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(v_00_u03b1_1725_, v_cmp_1726_, v_as_1727_, v_sz_boxed_1731_, v_i_boxed_1732_, v_b_1730_);
lean_dec_ref(v_as_1727_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0(lean_object* v_b_u2082_1736_, lean_object* v_x_1737_){
_start:
{
if (lean_obj_tag(v_x_1737_) == 0)
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_b_u2082_1736_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = ((lean_object*)(l_Std_TreeSet_merge___redArg___lam__0___closed__0));
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1740_, lean_object* v_x_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Std_TreeSet_merge___redArg___lam__0(v_b_u2082_1740_, v_x_1741_);
lean_dec(v_x_1741_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__1(lean_object* v_cmp_1743_, lean_object* v_t_1744_, lean_object* v_a_1745_, lean_object* v_b_u2082_1746_){
_start:
{
lean_object* v___f_1747_; lean_object* v___x_1748_; 
v___f_1747_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1747_, 0, v_b_u2082_1746_);
v___x_1748_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_1743_, v_a_1745_, v___f_1747_, v_t_1744_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg(lean_object* v_cmp_1749_, lean_object* v_t_u2081_1750_, lean_object* v_t_u2082_1751_){
_start:
{
lean_object* v___f_1752_; lean_object* v___x_1753_; 
v___f_1752_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1752_, 0, v_cmp_1749_);
v___x_1753_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1752_, v_t_u2081_1750_, v_t_u2082_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge(lean_object* v_00_u03b1_1754_, lean_object* v_cmp_1755_, lean_object* v_t_u2081_1756_, lean_object* v_t_u2082_1757_){
_start:
{
lean_object* v___f_1758_; lean_object* v___x_1759_; 
v___f_1758_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1758_, 0, v_cmp_1755_);
v___x_1759_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1758_, v_t_u2081_1756_, v_t_u2082_1757_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg___lam__0(lean_object* v_cmp_1760_, lean_object* v_a_1761_, lean_object* v_____s_1762_){
_start:
{
uint8_t v___x_1763_; 
lean_inc(v_____s_1762_);
lean_inc(v_a_1761_);
lean_inc_ref(v_cmp_1760_);
v___x_1763_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1760_, v_a_1761_, v_____s_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = lean_box(0);
v___x_1765_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1760_, v_a_1761_, v___x_1764_, v_____s_1762_);
v___x_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; 
lean_dec(v_a_1761_);
lean_dec_ref(v_cmp_1760_);
v___x_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_____s_1762_);
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg(lean_object* v_cmp_1768_, lean_object* v_inst_1769_, lean_object* v_t_1770_, lean_object* v_l_1771_){
_start:
{
lean_object* v___f_1772_; lean_object* v___x_1773_; 
v___f_1772_ = lean_alloc_closure((void*)(l_Std_TreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1772_, 0, v_cmp_1768_);
v___x_1773_ = lean_apply_4(v_inst_1769_, lean_box(0), v_l_1771_, v_t_1770_, v___f_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany(lean_object* v_00_u03b1_1774_, lean_object* v_cmp_1775_, lean_object* v_00_u03c1_1776_, lean_object* v_inst_1777_, lean_object* v_t_1778_, lean_object* v_l_1779_){
_start:
{
lean_object* v___f_1780_; lean_object* v___x_1781_; 
v___f_1780_ = lean_alloc_closure((void*)(l_Std_TreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1780_, 0, v_cmp_1775_);
v___x_1781_ = lean_apply_4(v_inst_1777_, lean_box(0), v_l_1779_, v_t_1778_, v___f_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_union___redArg(lean_object* v_cmp_1782_, lean_object* v_t_u2081_1783_, lean_object* v_t_u2082_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1782_, v_t_u2081_1783_, v_t_u2082_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_union(lean_object* v_00_u03b1_1786_, lean_object* v_cmp_1787_, lean_object* v_t_u2081_1788_, lean_object* v_t_u2082_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1787_, v_t_u2081_1788_, v_t_u2082_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion___redArg(lean_object* v_cmp_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_alloc_closure((void*)(l_Std_TreeSet_union), 4, 2);
lean_closure_set(v___x_1792_, 0, lean_box(0));
lean_closure_set(v___x_1792_, 1, v_cmp_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion(lean_object* v_00_u03b1_1793_, lean_object* v_cmp_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_alloc_closure((void*)(l_Std_TreeSet_union), 4, 2);
lean_closure_set(v___x_1795_, 0, lean_box(0));
lean_closure_set(v___x_1795_, 1, v_cmp_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_inter___redArg(lean_object* v_cmp_1796_, lean_object* v_t_u2081_1797_, lean_object* v_t_u2082_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1796_, v_t_u2081_1797_, v_t_u2082_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_inter(lean_object* v_00_u03b1_1800_, lean_object* v_cmp_1801_, lean_object* v_t_u2081_1802_, lean_object* v_t_u2082_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1801_, v_t_u2081_1802_, v_t_u2082_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter___redArg(lean_object* v_cmp_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_alloc_closure((void*)(l_Std_TreeSet_inter), 4, 2);
lean_closure_set(v___x_1806_, 0, lean_box(0));
lean_closure_set(v___x_1806_, 1, v_cmp_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter(lean_object* v_00_u03b1_1807_, lean_object* v_cmp_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_alloc_closure((void*)(l_Std_TreeSet_inter), 4, 2);
lean_closure_set(v___x_1809_, 0, lean_box(0));
lean_closure_set(v___x_1809_, 1, v_cmp_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_cmp_1810_, lean_object* v_t_1811_, lean_object* v_k_1812_){
_start:
{
if (lean_obj_tag(v_t_1811_) == 0)
{
lean_object* v_k_1813_; lean_object* v_v_1814_; lean_object* v_l_1815_; lean_object* v_r_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v_k_1813_ = lean_ctor_get(v_t_1811_, 1);
lean_inc(v_k_1813_);
v_v_1814_ = lean_ctor_get(v_t_1811_, 2);
lean_inc(v_v_1814_);
v_l_1815_ = lean_ctor_get(v_t_1811_, 3);
lean_inc(v_l_1815_);
v_r_1816_ = lean_ctor_get(v_t_1811_, 4);
lean_inc(v_r_1816_);
lean_dec_ref(v_t_1811_);
lean_inc_ref(v_cmp_1810_);
lean_inc(v_k_1812_);
v___x_1817_ = lean_apply_2(v_cmp_1810_, v_k_1812_, v_k_1813_);
v___x_1818_ = lean_unbox(v___x_1817_);
switch(v___x_1818_)
{
case 0:
{
lean_dec(v_r_1816_);
lean_dec(v_v_1814_);
v_t_1811_ = v_l_1815_;
goto _start;
}
case 1:
{
lean_object* v___x_1820_; 
lean_dec(v_r_1816_);
lean_dec(v_l_1815_);
lean_dec(v_k_1812_);
lean_dec_ref(v_cmp_1810_);
v___x_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1820_, 0, v_v_1814_);
return v___x_1820_;
}
default: 
{
lean_dec(v_l_1815_);
lean_dec(v_v_1814_);
v_t_1811_ = v_r_1816_;
goto _start;
}
}
}
else
{
lean_object* v___x_1822_; 
lean_dec(v_k_1812_);
lean_dec_ref(v_cmp_1810_);
v___x_1822_ = lean_box(0);
return v___x_1822_;
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1823_, lean_object* v_x_1824_){
_start:
{
if (lean_obj_tag(v_x_1823_) == 0)
{
if (lean_obj_tag(v_x_1824_) == 0)
{
uint8_t v___x_1825_; 
v___x_1825_ = 1;
return v___x_1825_;
}
else
{
uint8_t v___x_1826_; 
v___x_1826_ = 0;
return v___x_1826_;
}
}
else
{
if (lean_obj_tag(v_x_1824_) == 0)
{
uint8_t v___x_1827_; 
v___x_1827_ = 0;
return v___x_1827_;
}
else
{
uint8_t v___x_1828_; 
v___x_1828_ = 1;
return v___x_1828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1829_, lean_object* v_x_1830_){
_start:
{
uint8_t v_res_1831_; lean_object* v_r_1832_; 
v_res_1831_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v_x_1829_, v_x_1830_);
lean_dec(v_x_1830_);
lean_dec(v_x_1829_);
v_r_1832_ = lean_box(v_res_1831_);
return v_r_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_cmp_1833_, lean_object* v_t_u2082_1834_, lean_object* v_init_1835_, lean_object* v_x_1836_){
_start:
{
if (lean_obj_tag(v_x_1836_) == 0)
{
lean_object* v_k_1837_; lean_object* v_v_1838_; lean_object* v_l_1839_; lean_object* v_r_1840_; lean_object* v___x_1841_; 
v_k_1837_ = lean_ctor_get(v_x_1836_, 1);
lean_inc(v_k_1837_);
v_v_1838_ = lean_ctor_get(v_x_1836_, 2);
lean_inc(v_v_1838_);
v_l_1839_ = lean_ctor_get(v_x_1836_, 3);
lean_inc(v_l_1839_);
v_r_1840_ = lean_ctor_get(v_x_1836_, 4);
lean_inc(v_r_1840_);
lean_dec_ref(v_x_1836_);
lean_inc(v_t_u2082_1834_);
lean_inc_ref(v_cmp_1833_);
v___x_1841_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_1833_, v_t_u2082_1834_, v_init_1835_, v_l_1839_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_dec(v_r_1840_);
lean_dec(v_v_1838_);
lean_dec(v_k_1837_);
lean_dec(v_t_u2082_1834_);
lean_dec_ref(v_cmp_1833_);
return v___x_1841_;
}
else
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1857_; 
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1841_, 0);
lean_dec(v_unused_1858_);
v___x_1843_ = v___x_1841_;
v_isShared_1844_ = v_isSharedCheck_1857_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v___x_1841_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1857_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1845_ = lean_box(0);
lean_inc(v_t_u2082_1834_);
lean_inc_ref(v_cmp_1833_);
v___x_1846_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1833_, v_t_u2082_1834_, v_k_1837_);
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_v_1838_);
v___x_1848_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v___x_1846_, v___x_1847_);
lean_dec_ref(v___x_1847_);
lean_dec(v___x_1846_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
lean_dec(v_r_1840_);
lean_dec(v_t_u2082_1834_);
lean_dec_ref(v_cmp_1833_);
v___x_1849_ = lean_box(v___x_1848_);
v___x_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1845_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1851_);
v___x_1853_ = v___x_1843_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
else
{
lean_object* v___x_1855_; 
lean_del_object(v___x_1843_);
v___x_1855_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v_init_1835_ = v___x_1855_;
v_x_1836_ = v_r_1840_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1859_; 
lean_dec(v_t_u2082_1834_);
lean_dec_ref(v_cmp_1833_);
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_init_1835_);
return v___x_1859_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_1860_, lean_object* v_t_u2081_1861_, lean_object* v_t_u2082_1862_){
_start:
{
lean_object* v___y_1864_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1877_; 
if (lean_obj_tag(v_t_u2081_1861_) == 0)
{
lean_object* v_size_1880_; 
v_size_1880_ = lean_ctor_get(v_t_u2081_1861_, 0);
lean_inc(v_size_1880_);
v___y_1877_ = v_size_1880_;
goto v___jp_1876_;
}
else
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_unsigned_to_nat(0u);
v___y_1877_ = v___x_1881_;
goto v___jp_1876_;
}
v___jp_1863_:
{
lean_object* v_fst_1865_; 
v_fst_1865_ = lean_ctor_get(v___y_1864_, 0);
lean_inc(v_fst_1865_);
lean_dec_ref(v___y_1864_);
if (lean_obj_tag(v_fst_1865_) == 0)
{
uint8_t v___x_1866_; 
v___x_1866_ = 1;
return v___x_1866_;
}
else
{
lean_object* v_val_1867_; uint8_t v___x_1868_; 
v_val_1867_ = lean_ctor_get(v_fst_1865_, 0);
lean_inc(v_val_1867_);
lean_dec_ref(v_fst_1865_);
v___x_1868_ = lean_unbox(v_val_1867_);
lean_dec(v_val_1867_);
return v___x_1868_;
}
}
v___jp_1869_:
{
uint8_t v___x_1872_; 
v___x_1872_ = lean_nat_dec_eq(v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec(v___y_1870_);
if (v___x_1872_ == 0)
{
lean_dec(v_t_u2082_1862_);
lean_dec(v_t_u2081_1861_);
lean_dec_ref(v_cmp_1860_);
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v_a_1875_; 
v___x_1873_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___x_1874_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_1860_, v_t_u2082_1862_, v___x_1873_, v_t_u2081_1861_);
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v___x_1874_);
v___y_1864_ = v_a_1875_;
goto v___jp_1863_;
}
}
v___jp_1876_:
{
if (lean_obj_tag(v_t_u2082_1862_) == 0)
{
lean_object* v_size_1878_; 
v_size_1878_ = lean_ctor_get(v_t_u2082_1862_, 0);
lean_inc(v_size_1878_);
v___y_1870_ = v___y_1877_;
v___y_1871_ = v_size_1878_;
goto v___jp_1869_;
}
else
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_unsigned_to_nat(0u);
v___y_1870_ = v___y_1877_;
v___y_1871_ = v___x_1879_;
goto v___jp_1869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_1882_, lean_object* v_t_u2081_1883_, lean_object* v_t_u2082_1884_){
_start:
{
uint8_t v_res_1885_; lean_object* v_r_1886_; 
v_res_1885_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1882_, v_t_u2081_1883_, v_t_u2082_1884_);
v_r_1886_ = lean_box(v_res_1885_);
return v_r_1886_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_beq___redArg(lean_object* v_cmp_1887_, lean_object* v_t_u2081_1888_, lean_object* v_t_u2082_1889_){
_start:
{
uint8_t v___x_1890_; 
v___x_1890_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1887_, v_t_u2081_1888_, v_t_u2082_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___redArg___boxed(lean_object* v_cmp_1891_, lean_object* v_t_u2081_1892_, lean_object* v_t_u2082_1893_){
_start:
{
uint8_t v_res_1894_; lean_object* v_r_1895_; 
v_res_1894_ = l_Std_TreeSet_beq___redArg(v_cmp_1891_, v_t_u2081_1892_, v_t_u2082_1893_);
v_r_1895_ = lean_box(v_res_1894_);
return v_r_1895_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_beq(lean_object* v_00_u03b1_1896_, lean_object* v_cmp_1897_, lean_object* v_t_u2081_1898_, lean_object* v_t_u2082_1899_){
_start:
{
uint8_t v___x_1900_; 
v___x_1900_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1897_, v_t_u2081_1898_, v_t_u2082_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___boxed(lean_object* v_00_u03b1_1901_, lean_object* v_cmp_1902_, lean_object* v_t_u2081_1903_, lean_object* v_t_u2082_1904_){
_start:
{
uint8_t v_res_1905_; lean_object* v_r_1906_; 
v_res_1905_ = l_Std_TreeSet_beq(v_00_u03b1_1901_, v_cmp_1902_, v_t_u2081_1903_, v_t_u2082_1904_);
v_r_1906_ = lean_box(v_res_1905_);
return v_r_1906_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(lean_object* v_cmp_1907_, lean_object* v_t_u2081_1908_, lean_object* v_t_u2082_1909_){
_start:
{
uint8_t v___x_1910_; 
v___x_1910_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1907_, v_t_u2081_1908_, v_t_u2082_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg___boxed(lean_object* v_cmp_1911_, lean_object* v_t_u2081_1912_, lean_object* v_t_u2082_1913_){
_start:
{
uint8_t v_res_1914_; lean_object* v_r_1915_; 
v_res_1914_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(v_cmp_1911_, v_t_u2081_1912_, v_t_u2082_1913_);
v_r_1915_ = lean_box(v_res_1914_);
return v_r_1915_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(lean_object* v_00_u03b1_1916_, lean_object* v_cmp_1917_, lean_object* v_t_u2081_1918_, lean_object* v_t_u2082_1919_){
_start:
{
uint8_t v___x_1920_; 
v___x_1920_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1917_, v_t_u2081_1918_, v_t_u2082_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___boxed(lean_object* v_00_u03b1_1921_, lean_object* v_cmp_1922_, lean_object* v_t_u2081_1923_, lean_object* v_t_u2082_1924_){
_start:
{
uint8_t v_res_1925_; lean_object* v_r_1926_; 
v_res_1925_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(v_00_u03b1_1921_, v_cmp_1922_, v_t_u2081_1923_, v_t_u2082_1924_);
v_r_1926_ = lean_box(v_res_1925_);
return v_r_1926_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(lean_object* v_cmp_1927_, lean_object* v_t_u2081_1928_, lean_object* v_t_u2082_1929_){
_start:
{
uint8_t v___x_1930_; 
v___x_1930_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1927_, v_t_u2081_1928_, v_t_u2082_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_1931_, lean_object* v_t_u2081_1932_, lean_object* v_t_u2082_1933_){
_start:
{
uint8_t v_res_1934_; lean_object* v_r_1935_; 
v_res_1934_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(v_cmp_1931_, v_t_u2081_1932_, v_t_u2082_1933_);
v_r_1935_ = lean_box(v_res_1934_);
return v_r_1935_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(lean_object* v_00_u03b1_1936_, lean_object* v_cmp_1937_, lean_object* v_t_u2081_1938_, lean_object* v_t_u2082_1939_){
_start:
{
uint8_t v___x_1940_; 
v___x_1940_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1937_, v_t_u2081_1938_, v_t_u2082_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1941_, lean_object* v_cmp_1942_, lean_object* v_t_u2081_1943_, lean_object* v_t_u2082_1944_){
_start:
{
uint8_t v_res_1945_; lean_object* v_r_1946_; 
v_res_1945_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(v_00_u03b1_1941_, v_cmp_1942_, v_t_u2081_1943_, v_t_u2082_1944_);
v_r_1946_ = lean_box(v_res_1945_);
return v_r_1946_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1947_, lean_object* v_cmp_1948_, lean_object* v_t_u2081_1949_, lean_object* v_t_u2082_1950_){
_start:
{
uint8_t v___x_1951_; 
v___x_1951_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1948_, v_t_u2081_1949_, v_t_u2082_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_cmp_1953_, lean_object* v_t_u2081_1954_, lean_object* v_t_u2082_1955_){
_start:
{
uint8_t v_res_1956_; lean_object* v_r_1957_; 
v_res_1956_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(v_00_u03b1_1952_, v_cmp_1953_, v_t_u2081_1954_, v_t_u2082_1955_);
v_r_1957_ = lean_box(v_res_1956_);
return v_r_1957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1958_, lean_object* v_cmp_1959_, lean_object* v_00_u03b4_1960_, lean_object* v_t_1961_, lean_object* v_k_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1959_, v_t_1961_, v_k_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1964_, lean_object* v_cmp_1965_, lean_object* v_t_u2082_1966_, lean_object* v_init_1967_, lean_object* v_x_1968_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_1965_, v_t_u2082_1966_, v_init_1967_, v_x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq___redArg(lean_object* v_cmp_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_alloc_closure((void*)(l_Std_TreeSet_beq___boxed), 4, 2);
lean_closure_set(v___x_1971_, 0, lean_box(0));
lean_closure_set(v___x_1971_, 1, v_cmp_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq(lean_object* v_00_u03b1_1972_, lean_object* v_cmp_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_closure((void*)(l_Std_TreeSet_beq___boxed), 4, 2);
lean_closure_set(v___x_1974_, 0, lean_box(0));
lean_closure_set(v___x_1974_, 1, v_cmp_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_diff___redArg(lean_object* v_cmp_1975_, lean_object* v_t_u2081_1976_, lean_object* v_t_u2082_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1975_, v_t_u2081_1976_, v_t_u2082_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_diff(lean_object* v_00_u03b1_1979_, lean_object* v_cmp_1980_, lean_object* v_t_u2081_1981_, lean_object* v_t_u2082_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_1980_, v_t_u2081_1981_, v_t_u2082_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff___redArg(lean_object* v_cmp_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_alloc_closure((void*)(l_Std_TreeSet_diff), 4, 2);
lean_closure_set(v___x_1985_, 0, lean_box(0));
lean_closure_set(v___x_1985_, 1, v_cmp_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff(lean_object* v_00_u03b1_1986_, lean_object* v_cmp_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_alloc_closure((void*)(l_Std_TreeSet_diff), 4, 2);
lean_closure_set(v___x_1988_, 0, lean_box(0));
lean_closure_set(v___x_1988_, 1, v_cmp_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg___lam__0(lean_object* v_cmp_1989_, lean_object* v_a_1990_, lean_object* v_____s_1991_){
_start:
{
lean_object* v_r_1992_; lean_object* v___x_1993_; 
v_r_1992_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_1989_, v_a_1990_, v_____s_1991_);
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_r_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg(lean_object* v_cmp_1994_, lean_object* v_inst_1995_, lean_object* v_t_1996_, lean_object* v_l_1997_){
_start:
{
lean_object* v___f_1998_; lean_object* v___x_1999_; 
v___f_1998_ = lean_alloc_closure((void*)(l_Std_TreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1998_, 0, v_cmp_1994_);
v___x_1999_ = lean_apply_4(v_inst_1995_, lean_box(0), v_l_1997_, v_t_1996_, v___f_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany(lean_object* v_00_u03b1_2000_, lean_object* v_cmp_2001_, lean_object* v_00_u03c1_2002_, lean_object* v_inst_2003_, lean_object* v_t_2004_, lean_object* v_l_2005_){
_start:
{
lean_object* v___f_2006_; lean_object* v___x_2007_; 
v___f_2006_ = lean_alloc_closure((void*)(l_Std_TreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2006_, 0, v_cmp_2001_);
v___x_2007_ = lean_apply_4(v_inst_2003_, lean_box(0), v_l_2005_, v_t_2004_, v___f_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1(lean_object* v___f_2011_, lean_object* v_inst_2012_, lean_object* v_m_2013_, lean_object* v_prec_2014_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2015_ = ((lean_object*)(l_Std_TreeSet_instRepr___redArg___lam__1___closed__1));
v___x_2016_ = lean_box(0);
v___x_2017_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_2018_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2017_, v___f_2011_, v___x_2016_, v_m_2013_);
v___x_2019_ = l_List_repr___redArg(v_inst_2012_, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2015_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = l_Repr_addAppParen(v___x_2020_, v_prec_2014_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1___boxed(lean_object* v___f_2022_, lean_object* v_inst_2023_, lean_object* v_m_2024_, lean_object* v_prec_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Std_TreeSet_instRepr___redArg___lam__1(v___f_2022_, v_inst_2023_, v_m_2024_, v_prec_2025_);
lean_dec(v_prec_2025_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg(lean_object* v_inst_2027_){
_start:
{
lean_object* v___f_2028_; lean_object* v___f_2029_; 
v___f_2028_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___f_2029_ = lean_alloc_closure((void*)(l_Std_TreeSet_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2029_, 0, v___f_2028_);
lean_closure_set(v___f_2029_, 1, v_inst_2027_);
return v___f_2029_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr(lean_object* v_00_u03b1_2030_, lean_object* v_cmp_2031_, lean_object* v_inst_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Std_TreeSet_instRepr___redArg(v_inst_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___boxed(lean_object* v_00_u03b1_2034_, lean_object* v_cmp_2035_, lean_object* v_inst_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Std_TreeSet_instRepr(v_00_u03b1_2034_, v_cmp_2035_, v_inst_2036_);
lean_dec_ref(v_cmp_2035_);
return v_res_2037_;
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
