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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___redArg(){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(1);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___redArg___boxed(lean_object* v___dummy_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_TreeSet_empty___redArg();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_empty(lean_object* v_00_u03b1_79_, lean_object* v_cmp_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(1);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___boxed(lean_object* v_00_u03b1_82_, lean_object* v_cmp_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_TreeSet_empty(v_00_u03b1_82_, v_cmp_83_);
lean_dec_ref(v_cmp_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(1);
return v___x_86_;
}
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
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___redArg___boxed(lean_object* v___dummy_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_TreeSet_instInhabited___redArg();
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited(lean_object* v_00_u03b1_99_, lean_object* v_cmp_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_box(1);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___boxed(lean_object* v_00_u03b1_102_, lean_object* v_cmp_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_TreeSet_instInhabited(v_00_u03b1_102_, v_cmp_103_);
lean_dec_ref(v_cmp_103_);
return v_res_104_;
}
}
static lean_object* _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3));
v___x_143_ = l_String_toRawSubstring_x27(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(lean_object* v_x_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__3));
lean_inc(v_x_161_);
v___x_165_ = l_Lean_Syntax_isOfKind(v_x_161_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_x_161_);
v___x_166_ = lean_box(1);
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_163_);
return v___x_167_;
}
else
{
lean_object* v_quotContext_168_; lean_object* v_currMacroScope_169_; lean_object* v_ref_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_quotContext_168_ = lean_ctor_get(v_a_162_, 1);
v_currMacroScope_169_ = lean_ctor_get(v_a_162_, 2);
v_ref_170_ = lean_ctor_get(v_a_162_, 5);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = l_Lean_Syntax_getArg(v_x_161_, v___x_171_);
v___x_173_ = lean_unsigned_to_nat(2u);
v___x_174_ = l_Lean_Syntax_getArg(v_x_161_, v___x_173_);
lean_dec(v_x_161_);
v___x_175_ = 0;
v___x_176_ = l_Lean_SourceInfo_fromRef(v_ref_170_, v___x_175_);
v___x_177_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2));
v___x_178_ = lean_obj_once(&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4, &l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4_once, _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4);
v___x_179_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_169_);
lean_inc(v_quotContext_168_);
v___x_180_ = l_Lean_addMacroScope(v_quotContext_168_, v___x_179_, v_currMacroScope_169_);
v___x_181_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10));
lean_inc_n(v___x_176_, 2);
v___x_182_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_182_, 0, v___x_176_);
lean_ctor_set(v___x_182_, 1, v___x_178_);
lean_ctor_set(v___x_182_, 2, v___x_180_);
lean_ctor_set(v___x_182_, 3, v___x_181_);
v___x_183_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__9));
v___x_184_ = l_Lean_Syntax_node2(v___x_176_, v___x_183_, v___x_172_, v___x_174_);
v___x_185_ = l_Lean_Syntax_node2(v___x_176_, v___x_177_, v___x_182_, v___x_184_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_a_163_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___boxed(lean_object* v_x_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(v_x_187_, v_a_188_, v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(lean_object* v_x_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2));
lean_inc(v_x_194_);
v___x_198_ = l_Lean_Syntax_isOfKind(v_x_194_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_x_194_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v_a_196_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = l_Lean_Syntax_getArg(v_x_194_, v___x_201_);
v___x_203_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1));
lean_inc(v___x_202_);
v___x_204_ = l_Lean_Syntax_isOfKind(v___x_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v___x_202_);
lean_dec(v_x_194_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v_a_196_);
return v___x_206_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = l_Lean_Syntax_getArg(v_x_194_, v___x_207_);
lean_dec(v_x_194_);
v___x_209_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_208_);
v___x_210_ = l_Lean_Syntax_matchesNull(v___x_208_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v___x_208_);
lean_dec(v___x_202_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v_a_196_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_ref_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_213_ = l_Lean_Syntax_getArg(v___x_208_, v___x_201_);
v___x_214_ = l_Lean_Syntax_getArg(v___x_208_, v___x_207_);
lean_dec(v___x_208_);
v_ref_215_ = l_Lean_replaceRef(v___x_202_, v_a_195_);
lean_dec(v___x_202_);
v___x_216_ = 0;
v___x_217_ = l_Lean_SourceInfo_fromRef(v_ref_215_, v___x_216_);
lean_dec(v_ref_215_);
v___x_218_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__3));
v___x_219_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__6));
lean_inc(v___x_217_);
v___x_220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_217_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = l_Lean_Syntax_node3(v___x_217_, v___x_218_, v___x_213_, v___x_220_, v___x_214_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_a_196_);
return v___x_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___boxed(lean_object* v_x_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(v_x_223_, v_a_224_, v_a_225_);
lean_dec(v_a_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insert___redArg(lean_object* v_cmp_227_, lean_object* v_l_228_, lean_object* v_a_229_){
_start:
{
uint8_t v___x_230_; 
lean_inc(v_l_228_);
lean_inc(v_a_229_);
lean_inc_ref(v_cmp_227_);
v___x_230_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_227_, v_a_229_, v_l_228_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_box(0);
v___x_232_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_227_, v_a_229_, v___x_231_, v_l_228_);
return v___x_232_;
}
else
{
lean_dec(v_a_229_);
lean_dec_ref(v_cmp_227_);
return v_l_228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insert(lean_object* v_00_u03b1_233_, lean_object* v_cmp_234_, lean_object* v_l_235_, lean_object* v_a_236_){
_start:
{
uint8_t v___x_237_; 
lean_inc(v_l_235_);
lean_inc(v_a_236_);
lean_inc_ref(v_cmp_234_);
v___x_237_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_234_, v_a_236_, v_l_235_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_box(0);
v___x_239_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_234_, v_a_236_, v___x_238_, v_l_235_);
return v___x_239_;
}
else
{
lean_dec(v_a_236_);
lean_dec_ref(v_cmp_234_);
return v_l_235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg___lam__0(lean_object* v_cmp_240_, lean_object* v_e_241_){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_box(1);
lean_inc(v_e_241_);
lean_inc_ref(v_cmp_240_);
v___x_243_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_240_, v_e_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_box(0);
v___x_245_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_240_, v_e_241_, v___x_244_, v___x_242_);
return v___x_245_;
}
else
{
lean_dec(v_e_241_);
lean_dec_ref(v_cmp_240_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg(lean_object* v_cmp_246_){
_start:
{
lean_object* v___f_247_; 
v___f_247_ = lean_alloc_closure((void*)(l_Std_TreeSet_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_247_, 0, v_cmp_246_);
return v___f_247_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton(lean_object* v_00_u03b1_248_, lean_object* v_cmp_249_){
_start:
{
lean_object* v___f_250_; 
v___f_250_ = lean_alloc_closure((void*)(l_Std_TreeSet_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_250_, 0, v_cmp_249_);
return v___f_250_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg___lam__0(lean_object* v_cmp_251_, lean_object* v_e_252_, lean_object* v_s_253_){
_start:
{
uint8_t v___x_254_; 
lean_inc(v_s_253_);
lean_inc(v_e_252_);
lean_inc_ref(v_cmp_251_);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_251_, v_e_252_, v_s_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_box(0);
v___x_256_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_251_, v_e_252_, v___x_255_, v_s_253_);
return v___x_256_;
}
else
{
lean_dec(v_e_252_);
lean_dec_ref(v_cmp_251_);
return v_s_253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg(lean_object* v_cmp_257_){
_start:
{
lean_object* v___f_258_; 
v___f_258_ = lean_alloc_closure((void*)(l_Std_TreeSet_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_258_, 0, v_cmp_257_);
return v___f_258_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert(lean_object* v_00_u03b1_259_, lean_object* v_cmp_260_){
_start:
{
lean_object* v___f_261_; 
v___f_261_ = lean_alloc_closure((void*)(l_Std_TreeSet_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_261_, 0, v_cmp_260_);
return v___f_261_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert___redArg(lean_object* v_cmp_262_, lean_object* v_t_263_, lean_object* v_a_264_){
_start:
{
uint8_t v___x_265_; 
lean_inc(v_t_263_);
lean_inc(v_a_264_);
lean_inc_ref(v_cmp_262_);
v___x_265_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_262_, v_a_264_, v_t_263_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_266_ = lean_box(0);
v___x_267_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_262_, v_a_264_, v___x_266_, v_t_263_);
v___x_268_ = lean_box(v___x_265_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec(v_a_264_);
lean_dec_ref(v_cmp_262_);
v___x_270_ = lean_box(v___x_265_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v_t_263_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert(lean_object* v_00_u03b1_272_, lean_object* v_cmp_273_, lean_object* v_t_274_, lean_object* v_a_275_){
_start:
{
uint8_t v___x_276_; 
lean_inc(v_t_274_);
lean_inc(v_a_275_);
lean_inc_ref(v_cmp_273_);
v___x_276_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_273_, v_a_275_, v_t_274_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = lean_box(0);
v___x_278_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_273_, v_a_275_, v___x_277_, v_t_274_);
v___x_279_ = lean_box(v___x_276_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v_a_275_);
lean_dec_ref(v_cmp_273_);
v___x_281_ = lean_box(v___x_276_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v_t_274_);
return v___x_282_;
}
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_contains___redArg(lean_object* v_cmp_283_, lean_object* v_l_284_, lean_object* v_a_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_283_, v_a_285_, v_l_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___redArg___boxed(lean_object* v_cmp_287_, lean_object* v_l_288_, lean_object* v_a_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Std_TreeSet_contains___redArg(v_cmp_287_, v_l_288_, v_a_289_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_contains(lean_object* v_00_u03b1_292_, lean_object* v_cmp_293_, lean_object* v_l_294_, lean_object* v_a_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_293_, v_a_295_, v_l_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___boxed(lean_object* v_00_u03b1_297_, lean_object* v_cmp_298_, lean_object* v_l_299_, lean_object* v_a_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Std_TreeSet_contains(v_00_u03b1_297_, v_cmp_298_, v_l_299_, v_a_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___redArg(){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lean_box(0);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___redArg___boxed(lean_object* v___dummy_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_TreeSet_instMembership___redArg();
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership(lean_object* v_00_u03b1_307_, lean_object* v_cmp_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = lean_box(0);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___boxed(lean_object* v_00_u03b1_310_, lean_object* v_cmp_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_TreeSet_instMembership(v_00_u03b1_310_, v_cmp_311_);
lean_dec_ref(v_cmp_311_);
return v_res_312_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableMem___redArg(lean_object* v_cmp_313_, lean_object* v_m_314_, lean_object* v_a_315_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_313_, v_a_315_, v_m_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___redArg___boxed(lean_object* v_cmp_317_, lean_object* v_m_318_, lean_object* v_a_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Std_TreeSet_instDecidableMem___redArg(v_cmp_317_, v_m_318_, v_a_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableMem(lean_object* v_00_u03b1_322_, lean_object* v_cmp_323_, lean_object* v_m_324_, lean_object* v_a_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_323_, v_a_325_, v_m_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___boxed(lean_object* v_00_u03b1_327_, lean_object* v_cmp_328_, lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Std_TreeSet_instDecidableMem(v_00_u03b1_327_, v_cmp_328_, v_m_329_, v_a_330_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg(lean_object* v_t_333_){
_start:
{
if (lean_obj_tag(v_t_333_) == 0)
{
lean_object* v_size_334_; 
v_size_334_ = lean_ctor_get(v_t_333_, 0);
lean_inc(v_size_334_);
return v_size_334_;
}
else
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(0u);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg___boxed(lean_object* v_t_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_TreeSet_size___redArg(v_t_336_);
lean_dec(v_t_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size(lean_object* v_00_u03b1_338_, lean_object* v_cmp_339_, lean_object* v_t_340_){
_start:
{
if (lean_obj_tag(v_t_340_) == 0)
{
lean_object* v_size_341_; 
v_size_341_ = lean_ctor_get(v_t_340_, 0);
lean_inc(v_size_341_);
return v_size_341_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = lean_unsigned_to_nat(0u);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___boxed(lean_object* v_00_u03b1_343_, lean_object* v_cmp_344_, lean_object* v_t_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_TreeSet_size(v_00_u03b1_343_, v_cmp_344_, v_t_345_);
lean_dec(v_t_345_);
lean_dec_ref(v_cmp_344_);
return v_res_346_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_isEmpty___redArg(lean_object* v_t_347_){
_start:
{
if (lean_obj_tag(v_t_347_) == 0)
{
uint8_t v___x_348_; 
v___x_348_ = 0;
return v___x_348_;
}
else
{
uint8_t v___x_349_; 
v___x_349_ = 1;
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___redArg___boxed(lean_object* v_t_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Std_TreeSet_isEmpty___redArg(v_t_350_);
lean_dec(v_t_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_isEmpty(lean_object* v_00_u03b1_353_, lean_object* v_cmp_354_, lean_object* v_t_355_){
_start:
{
if (lean_obj_tag(v_t_355_) == 0)
{
uint8_t v___x_356_; 
v___x_356_ = 0;
return v___x_356_;
}
else
{
uint8_t v___x_357_; 
v___x_357_ = 1;
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___boxed(lean_object* v_00_u03b1_358_, lean_object* v_cmp_359_, lean_object* v_t_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Std_TreeSet_isEmpty(v_00_u03b1_358_, v_cmp_359_, v_t_360_);
lean_dec(v_t_360_);
lean_dec_ref(v_cmp_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_erase___redArg(lean_object* v_cmp_363_, lean_object* v_t_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_363_, v_a_365_, v_t_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_erase(lean_object* v_00_u03b1_367_, lean_object* v_cmp_368_, lean_object* v_t_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_368_, v_a_370_, v_t_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f___redArg(lean_object* v_cmp_372_, lean_object* v_t_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_372_, v_t_373_, v_a_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f(lean_object* v_00_u03b1_376_, lean_object* v_cmp_377_, lean_object* v_t_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_377_, v_t_378_, v_a_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get___redArg(lean_object* v_cmp_381_, lean_object* v_t_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_381_, v_t_382_, v_a_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get(lean_object* v_00_u03b1_385_, lean_object* v_cmp_386_, lean_object* v_t_387_, lean_object* v_a_388_, lean_object* v_h_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_386_, v_t_387_, v_a_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___redArg(lean_object* v_cmp_391_, lean_object* v_inst_392_, lean_object* v_t_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_391_, v_t_393_, v_a_394_, v_inst_392_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___redArg___boxed(lean_object* v_cmp_396_, lean_object* v_inst_397_, lean_object* v_t_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Std_TreeSet_get_x21___redArg(v_cmp_396_, v_inst_397_, v_t_398_, v_a_399_);
lean_dec(v_inst_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21(lean_object* v_00_u03b1_401_, lean_object* v_cmp_402_, lean_object* v_inst_403_, lean_object* v_t_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_402_, v_t_404_, v_a_405_, v_inst_403_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___boxed(lean_object* v_00_u03b1_407_, lean_object* v_cmp_408_, lean_object* v_inst_409_, lean_object* v_t_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_TreeSet_get_x21(v_00_u03b1_407_, v_cmp_408_, v_inst_409_, v_t_410_, v_a_411_);
lean_dec(v_inst_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg(lean_object* v_cmp_413_, lean_object* v_t_414_, lean_object* v_a_415_, lean_object* v_fallback_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_413_, v_t_414_, v_a_415_, v_fallback_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg___boxed(lean_object* v_cmp_418_, lean_object* v_t_419_, lean_object* v_a_420_, lean_object* v_fallback_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Std_TreeSet_getD___redArg(v_cmp_418_, v_t_419_, v_a_420_, v_fallback_421_);
lean_dec(v_fallback_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD(lean_object* v_00_u03b1_423_, lean_object* v_cmp_424_, lean_object* v_t_425_, lean_object* v_a_426_, lean_object* v_fallback_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_424_, v_t_425_, v_a_426_, v_fallback_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___boxed(lean_object* v_00_u03b1_429_, lean_object* v_cmp_430_, lean_object* v_t_431_, lean_object* v_a_432_, lean_object* v_fallback_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_TreeSet_getD(v_00_u03b1_429_, v_cmp_430_, v_t_431_, v_a_432_, v_fallback_433_);
lean_dec(v_fallback_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg(lean_object* v_t_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg___boxed(lean_object* v_t_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_TreeSet_min_x3f___redArg(v_t_437_);
lean_dec(v_t_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f(lean_object* v_00_u03b1_439_, lean_object* v_cmp_440_, lean_object* v_t_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___boxed(lean_object* v_00_u03b1_443_, lean_object* v_cmp_444_, lean_object* v_t_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_TreeSet_min_x3f(v_00_u03b1_443_, v_cmp_444_, v_t_445_);
lean_dec(v_t_445_);
lean_dec_ref(v_cmp_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg(lean_object* v_t_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg___boxed(lean_object* v_t_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_TreeSet_min___redArg(v_t_449_);
lean_dec(v_t_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min(lean_object* v_00_u03b1_451_, lean_object* v_cmp_452_, lean_object* v_t_453_, lean_object* v_h_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___boxed(lean_object* v_00_u03b1_456_, lean_object* v_cmp_457_, lean_object* v_t_458_, lean_object* v_h_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_TreeSet_min(v_00_u03b1_456_, v_cmp_457_, v_t_458_, v_h_459_);
lean_dec(v_t_458_);
lean_dec_ref(v_cmp_457_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg(lean_object* v_inst_461_, lean_object* v_t_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_461_, v_t_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg___boxed(lean_object* v_inst_464_, lean_object* v_t_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_TreeSet_min_x21___redArg(v_inst_464_, v_t_465_);
lean_dec(v_t_465_);
lean_dec(v_inst_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21(lean_object* v_00_u03b1_467_, lean_object* v_cmp_468_, lean_object* v_inst_469_, lean_object* v_t_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_469_, v_t_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___boxed(lean_object* v_00_u03b1_472_, lean_object* v_cmp_473_, lean_object* v_inst_474_, lean_object* v_t_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_TreeSet_min_x21(v_00_u03b1_472_, v_cmp_473_, v_inst_474_, v_t_475_);
lean_dec(v_t_475_);
lean_dec(v_inst_474_);
lean_dec_ref(v_cmp_473_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg(lean_object* v_t_477_, lean_object* v_fallback_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_477_, v_fallback_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg___boxed(lean_object* v_t_480_, lean_object* v_fallback_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_TreeSet_minD___redArg(v_t_480_, v_fallback_481_);
lean_dec(v_fallback_481_);
lean_dec(v_t_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD(lean_object* v_00_u03b1_483_, lean_object* v_cmp_484_, lean_object* v_t_485_, lean_object* v_fallback_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_485_, v_fallback_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___boxed(lean_object* v_00_u03b1_488_, lean_object* v_cmp_489_, lean_object* v_t_490_, lean_object* v_fallback_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_TreeSet_minD(v_00_u03b1_488_, v_cmp_489_, v_t_490_, v_fallback_491_);
lean_dec(v_fallback_491_);
lean_dec(v_t_490_);
lean_dec_ref(v_cmp_489_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg(lean_object* v_t_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg___boxed(lean_object* v_t_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_TreeSet_max_x3f___redArg(v_t_495_);
lean_dec(v_t_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f(lean_object* v_00_u03b1_497_, lean_object* v_cmp_498_, lean_object* v_t_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___boxed(lean_object* v_00_u03b1_501_, lean_object* v_cmp_502_, lean_object* v_t_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_TreeSet_max_x3f(v_00_u03b1_501_, v_cmp_502_, v_t_503_);
lean_dec(v_t_503_);
lean_dec_ref(v_cmp_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg(lean_object* v_t_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg___boxed(lean_object* v_t_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_TreeSet_max___redArg(v_t_507_);
lean_dec(v_t_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max(lean_object* v_00_u03b1_509_, lean_object* v_cmp_510_, lean_object* v_t_511_, lean_object* v_h_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_511_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___boxed(lean_object* v_00_u03b1_514_, lean_object* v_cmp_515_, lean_object* v_t_516_, lean_object* v_h_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_TreeSet_max(v_00_u03b1_514_, v_cmp_515_, v_t_516_, v_h_517_);
lean_dec(v_t_516_);
lean_dec_ref(v_cmp_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg(lean_object* v_inst_519_, lean_object* v_t_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_519_, v_t_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg___boxed(lean_object* v_inst_522_, lean_object* v_t_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_TreeSet_max_x21___redArg(v_inst_522_, v_t_523_);
lean_dec(v_t_523_);
lean_dec(v_inst_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21(lean_object* v_00_u03b1_525_, lean_object* v_cmp_526_, lean_object* v_inst_527_, lean_object* v_t_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_527_, v_t_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___boxed(lean_object* v_00_u03b1_530_, lean_object* v_cmp_531_, lean_object* v_inst_532_, lean_object* v_t_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_TreeSet_max_x21(v_00_u03b1_530_, v_cmp_531_, v_inst_532_, v_t_533_);
lean_dec(v_t_533_);
lean_dec(v_inst_532_);
lean_dec_ref(v_cmp_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg(lean_object* v_t_535_, lean_object* v_fallback_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_535_, v_fallback_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg___boxed(lean_object* v_t_538_, lean_object* v_fallback_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_TreeSet_maxD___redArg(v_t_538_, v_fallback_539_);
lean_dec(v_fallback_539_);
lean_dec(v_t_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD(lean_object* v_00_u03b1_541_, lean_object* v_cmp_542_, lean_object* v_t_543_, lean_object* v_fallback_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_543_, v_fallback_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___boxed(lean_object* v_00_u03b1_546_, lean_object* v_cmp_547_, lean_object* v_t_548_, lean_object* v_fallback_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_TreeSet_maxD(v_00_u03b1_546_, v_cmp_547_, v_t_548_, v_fallback_549_);
lean_dec(v_fallback_549_);
lean_dec(v_t_548_);
lean_dec_ref(v_cmp_547_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg(lean_object* v_t_551_, lean_object* v_n_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_551_, v_n_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg___boxed(lean_object* v_t_554_, lean_object* v_n_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_TreeSet_atIdx_x3f___redArg(v_t_554_, v_n_555_);
lean_dec(v_t_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f(lean_object* v_00_u03b1_557_, lean_object* v_cmp_558_, lean_object* v_t_559_, lean_object* v_n_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_559_, v_n_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___boxed(lean_object* v_00_u03b1_562_, lean_object* v_cmp_563_, lean_object* v_t_564_, lean_object* v_n_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_TreeSet_atIdx_x3f(v_00_u03b1_562_, v_cmp_563_, v_t_564_, v_n_565_);
lean_dec(v_t_564_);
lean_dec_ref(v_cmp_563_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg(lean_object* v_t_567_, lean_object* v_n_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_567_, v_n_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg___boxed(lean_object* v_t_570_, lean_object* v_n_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_TreeSet_atIdx___redArg(v_t_570_, v_n_571_);
lean_dec(v_t_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx(lean_object* v_00_u03b1_573_, lean_object* v_cmp_574_, lean_object* v_t_575_, lean_object* v_n_576_, lean_object* v_h_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_575_, v_n_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___boxed(lean_object* v_00_u03b1_579_, lean_object* v_cmp_580_, lean_object* v_t_581_, lean_object* v_n_582_, lean_object* v_h_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_TreeSet_atIdx(v_00_u03b1_579_, v_cmp_580_, v_t_581_, v_n_582_, v_h_583_);
lean_dec(v_t_581_);
lean_dec_ref(v_cmp_580_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg(lean_object* v_inst_585_, lean_object* v_t_586_, lean_object* v_n_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_585_, v_t_586_, v_n_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg___boxed(lean_object* v_inst_589_, lean_object* v_t_590_, lean_object* v_n_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Std_TreeSet_atIdx_x21___redArg(v_inst_589_, v_t_590_, v_n_591_);
lean_dec(v_t_590_);
lean_dec(v_inst_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21(lean_object* v_00_u03b1_593_, lean_object* v_cmp_594_, lean_object* v_inst_595_, lean_object* v_t_596_, lean_object* v_n_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_595_, v_t_596_, v_n_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___boxed(lean_object* v_00_u03b1_599_, lean_object* v_cmp_600_, lean_object* v_inst_601_, lean_object* v_t_602_, lean_object* v_n_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_TreeSet_atIdx_x21(v_00_u03b1_599_, v_cmp_600_, v_inst_601_, v_t_602_, v_n_603_);
lean_dec(v_t_602_);
lean_dec(v_inst_601_);
lean_dec_ref(v_cmp_600_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg(lean_object* v_t_605_, lean_object* v_n_606_, lean_object* v_fallback_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_605_, v_n_606_, v_fallback_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg___boxed(lean_object* v_t_609_, lean_object* v_n_610_, lean_object* v_fallback_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_TreeSet_atIdxD___redArg(v_t_609_, v_n_610_, v_fallback_611_);
lean_dec(v_fallback_611_);
lean_dec(v_t_609_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD(lean_object* v_00_u03b1_613_, lean_object* v_cmp_614_, lean_object* v_t_615_, lean_object* v_n_616_, lean_object* v_fallback_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_615_, v_n_616_, v_fallback_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___boxed(lean_object* v_00_u03b1_619_, lean_object* v_cmp_620_, lean_object* v_t_621_, lean_object* v_n_622_, lean_object* v_fallback_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_TreeSet_atIdxD(v_00_u03b1_619_, v_cmp_620_, v_t_621_, v_n_622_, v_fallback_623_);
lean_dec(v_fallback_623_);
lean_dec(v_t_621_);
lean_dec_ref(v_cmp_620_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f___redArg(lean_object* v_cmp_625_, lean_object* v_t_626_, lean_object* v_k_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_box(0);
v___x_629_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_625_, v_k_627_, v___x_628_, v_t_626_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f(lean_object* v_00_u03b1_630_, lean_object* v_cmp_631_, lean_object* v_t_632_, lean_object* v_k_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_box(0);
v___x_635_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_631_, v_k_633_, v___x_634_, v_t_632_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f___redArg(lean_object* v_cmp_636_, lean_object* v_t_637_, lean_object* v_k_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_box(0);
v___x_640_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_636_, v_k_638_, v___x_639_, v_t_637_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f(lean_object* v_00_u03b1_641_, lean_object* v_cmp_642_, lean_object* v_t_643_, lean_object* v_k_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box(0);
v___x_646_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_642_, v_k_644_, v___x_645_, v_t_643_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f___redArg(lean_object* v_cmp_647_, lean_object* v_t_648_, lean_object* v_k_649_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_box(0);
v___x_651_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_647_, v_k_649_, v___x_650_, v_t_648_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f(lean_object* v_00_u03b1_652_, lean_object* v_cmp_653_, lean_object* v_t_654_, lean_object* v_k_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_box(0);
v___x_657_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_653_, v_k_655_, v___x_656_, v_t_654_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f___redArg(lean_object* v_cmp_658_, lean_object* v_t_659_, lean_object* v_k_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_box(0);
v___x_662_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_658_, v_k_660_, v___x_661_, v_t_659_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f(lean_object* v_00_u03b1_663_, lean_object* v_cmp_664_, lean_object* v_t_665_, lean_object* v_k_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_box(0);
v___x_668_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_664_, v_k_666_, v___x_667_, v_t_665_);
return v___x_668_;
}
}
static lean_object* _init_l_Std_TreeSet_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_672_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__2));
v___x_673_ = lean_unsigned_to_nat(14u);
v___x_674_ = lean_unsigned_to_nat(22u);
v___x_675_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__1));
v___x_676_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__0));
v___x_677_ = l_mkPanicMessageWithDecl(v___x_676_, v___x_675_, v___x_674_, v___x_673_, v___x_672_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___redArg(lean_object* v_cmp_678_, lean_object* v_inst_679_, lean_object* v_t_680_, lean_object* v_k_681_){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_box(0);
v___x_683_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_678_, v_k_681_, v___x_682_, v_t_680_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_685_ = l_panic___redArg(v_inst_679_, v___x_684_);
return v___x_685_;
}
else
{
lean_object* v_val_686_; 
v_val_686_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_val_686_);
lean_dec_ref_known(v___x_683_, 1);
return v_val_686_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___redArg___boxed(lean_object* v_cmp_687_, lean_object* v_inst_688_, lean_object* v_t_689_, lean_object* v_k_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_TreeSet_getGE_x21___redArg(v_cmp_687_, v_inst_688_, v_t_689_, v_k_690_);
lean_dec(v_inst_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21(lean_object* v_00_u03b1_692_, lean_object* v_cmp_693_, lean_object* v_inst_694_, lean_object* v_t_695_, lean_object* v_k_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_box(0);
v___x_698_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_693_, v_k_696_, v___x_697_, v_t_695_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___boxed(lean_object* v_00_u03b1_702_, lean_object* v_cmp_703_, lean_object* v_inst_704_, lean_object* v_t_705_, lean_object* v_k_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_TreeSet_getGE_x21(v_00_u03b1_702_, v_cmp_703_, v_inst_704_, v_t_705_, v_k_706_);
lean_dec(v_inst_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg(lean_object* v_cmp_708_, lean_object* v_inst_709_, lean_object* v_t_710_, lean_object* v_k_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_box(0);
v___x_713_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_708_, v_k_711_, v___x_712_, v_t_710_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_715_ = l_panic___redArg(v_inst_709_, v___x_714_);
return v___x_715_;
}
else
{
lean_object* v_val_716_; 
v_val_716_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_val_716_);
lean_dec_ref_known(v___x_713_, 1);
return v_val_716_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg___boxed(lean_object* v_cmp_717_, lean_object* v_inst_718_, lean_object* v_t_719_, lean_object* v_k_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_TreeSet_getGT_x21___redArg(v_cmp_717_, v_inst_718_, v_t_719_, v_k_720_);
lean_dec(v_inst_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21(lean_object* v_00_u03b1_722_, lean_object* v_cmp_723_, lean_object* v_inst_724_, lean_object* v_t_725_, lean_object* v_k_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_box(0);
v___x_728_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_723_, v_k_726_, v___x_727_, v_t_725_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___boxed(lean_object* v_00_u03b1_732_, lean_object* v_cmp_733_, lean_object* v_inst_734_, lean_object* v_t_735_, lean_object* v_k_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_TreeSet_getGT_x21(v_00_u03b1_732_, v_cmp_733_, v_inst_734_, v_t_735_, v_k_736_);
lean_dec(v_inst_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg(lean_object* v_cmp_738_, lean_object* v_inst_739_, lean_object* v_t_740_, lean_object* v_k_741_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_box(0);
v___x_743_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_738_, v_k_741_, v___x_742_, v_t_740_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_745_ = l_panic___redArg(v_inst_739_, v___x_744_);
return v___x_745_;
}
else
{
lean_object* v_val_746_; 
v_val_746_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v___x_743_, 1);
return v_val_746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg___boxed(lean_object* v_cmp_747_, lean_object* v_inst_748_, lean_object* v_t_749_, lean_object* v_k_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_TreeSet_getLE_x21___redArg(v_cmp_747_, v_inst_748_, v_t_749_, v_k_750_);
lean_dec(v_inst_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21(lean_object* v_00_u03b1_752_, lean_object* v_cmp_753_, lean_object* v_inst_754_, lean_object* v_t_755_, lean_object* v_k_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_box(0);
v___x_758_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_753_, v_k_756_, v___x_757_, v_t_755_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_760_ = l_panic___redArg(v_inst_754_, v___x_759_);
return v___x_760_;
}
else
{
lean_object* v_val_761_; 
v_val_761_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v___x_758_, 1);
return v_val_761_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___boxed(lean_object* v_00_u03b1_762_, lean_object* v_cmp_763_, lean_object* v_inst_764_, lean_object* v_t_765_, lean_object* v_k_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_TreeSet_getLE_x21(v_00_u03b1_762_, v_cmp_763_, v_inst_764_, v_t_765_, v_k_766_);
lean_dec(v_inst_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg(lean_object* v_cmp_768_, lean_object* v_inst_769_, lean_object* v_t_770_, lean_object* v_k_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_box(0);
v___x_773_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_768_, v_k_771_, v___x_772_, v_t_770_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_775_ = l_panic___redArg(v_inst_769_, v___x_774_);
return v___x_775_;
}
else
{
lean_object* v_val_776_; 
v_val_776_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v___x_773_, 1);
return v_val_776_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg___boxed(lean_object* v_cmp_777_, lean_object* v_inst_778_, lean_object* v_t_779_, lean_object* v_k_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_TreeSet_getLT_x21___redArg(v_cmp_777_, v_inst_778_, v_t_779_, v_k_780_);
lean_dec(v_inst_778_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21(lean_object* v_00_u03b1_782_, lean_object* v_cmp_783_, lean_object* v_inst_784_, lean_object* v_t_785_, lean_object* v_k_786_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_box(0);
v___x_788_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_783_, v_k_786_, v___x_787_, v_t_785_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_790_ = l_panic___redArg(v_inst_784_, v___x_789_);
return v___x_790_;
}
else
{
lean_object* v_val_791_; 
v_val_791_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_val_791_);
lean_dec_ref_known(v___x_788_, 1);
return v_val_791_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___boxed(lean_object* v_00_u03b1_792_, lean_object* v_cmp_793_, lean_object* v_inst_794_, lean_object* v_t_795_, lean_object* v_k_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_TreeSet_getLT_x21(v_00_u03b1_792_, v_cmp_793_, v_inst_794_, v_t_795_, v_k_796_);
lean_dec(v_inst_794_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg(lean_object* v_cmp_798_, lean_object* v_t_799_, lean_object* v_k_800_, lean_object* v_fallback_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_box(0);
v___x_803_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_798_, v_k_800_, v___x_802_, v_t_799_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_inc(v_fallback_801_);
return v_fallback_801_;
}
else
{
lean_object* v_val_804_; 
v_val_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v___x_803_, 1);
return v_val_804_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg___boxed(lean_object* v_cmp_805_, lean_object* v_t_806_, lean_object* v_k_807_, lean_object* v_fallback_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_TreeSet_getGED___redArg(v_cmp_805_, v_t_806_, v_k_807_, v_fallback_808_);
lean_dec(v_fallback_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED(lean_object* v_00_u03b1_810_, lean_object* v_cmp_811_, lean_object* v_t_812_, lean_object* v_k_813_, lean_object* v_fallback_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_box(0);
v___x_816_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_811_, v_k_813_, v___x_815_, v_t_812_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_inc(v_fallback_814_);
return v_fallback_814_;
}
else
{
lean_object* v_val_817_; 
v_val_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_val_817_);
lean_dec_ref_known(v___x_816_, 1);
return v_val_817_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___boxed(lean_object* v_00_u03b1_818_, lean_object* v_cmp_819_, lean_object* v_t_820_, lean_object* v_k_821_, lean_object* v_fallback_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_TreeSet_getGED(v_00_u03b1_818_, v_cmp_819_, v_t_820_, v_k_821_, v_fallback_822_);
lean_dec(v_fallback_822_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg(lean_object* v_cmp_824_, lean_object* v_t_825_, lean_object* v_k_826_, lean_object* v_fallback_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_box(0);
v___x_829_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_824_, v_k_826_, v___x_828_, v_t_825_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_inc(v_fallback_827_);
return v_fallback_827_;
}
else
{
lean_object* v_val_830_; 
v_val_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_val_830_);
lean_dec_ref_known(v___x_829_, 1);
return v_val_830_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg___boxed(lean_object* v_cmp_831_, lean_object* v_t_832_, lean_object* v_k_833_, lean_object* v_fallback_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Std_TreeSet_getGTD___redArg(v_cmp_831_, v_t_832_, v_k_833_, v_fallback_834_);
lean_dec(v_fallback_834_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD(lean_object* v_00_u03b1_836_, lean_object* v_cmp_837_, lean_object* v_t_838_, lean_object* v_k_839_, lean_object* v_fallback_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_box(0);
v___x_842_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_837_, v_k_839_, v___x_841_, v_t_838_);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___boxed(lean_object* v_00_u03b1_844_, lean_object* v_cmp_845_, lean_object* v_t_846_, lean_object* v_k_847_, lean_object* v_fallback_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_TreeSet_getGTD(v_00_u03b1_844_, v_cmp_845_, v_t_846_, v_k_847_, v_fallback_848_);
lean_dec(v_fallback_848_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg(lean_object* v_cmp_850_, lean_object* v_t_851_, lean_object* v_k_852_, lean_object* v_fallback_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_box(0);
v___x_855_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_850_, v_k_852_, v___x_854_, v_t_851_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_inc(v_fallback_853_);
return v_fallback_853_;
}
else
{
lean_object* v_val_856_; 
v_val_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v___x_855_, 1);
return v_val_856_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg___boxed(lean_object* v_cmp_857_, lean_object* v_t_858_, lean_object* v_k_859_, lean_object* v_fallback_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_TreeSet_getLED___redArg(v_cmp_857_, v_t_858_, v_k_859_, v_fallback_860_);
lean_dec(v_fallback_860_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED(lean_object* v_00_u03b1_862_, lean_object* v_cmp_863_, lean_object* v_t_864_, lean_object* v_k_865_, lean_object* v_fallback_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_box(0);
v___x_868_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_863_, v_k_865_, v___x_867_, v_t_864_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_inc(v_fallback_866_);
return v_fallback_866_;
}
else
{
lean_object* v_val_869_; 
v_val_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v___x_868_, 1);
return v_val_869_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___boxed(lean_object* v_00_u03b1_870_, lean_object* v_cmp_871_, lean_object* v_t_872_, lean_object* v_k_873_, lean_object* v_fallback_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_TreeSet_getLED(v_00_u03b1_870_, v_cmp_871_, v_t_872_, v_k_873_, v_fallback_874_);
lean_dec(v_fallback_874_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg(lean_object* v_cmp_876_, lean_object* v_t_877_, lean_object* v_k_878_, lean_object* v_fallback_879_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_box(0);
v___x_881_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_876_, v_k_878_, v___x_880_, v_t_877_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_inc(v_fallback_879_);
return v_fallback_879_;
}
else
{
lean_object* v_val_882_; 
v_val_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v___x_881_, 1);
return v_val_882_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg___boxed(lean_object* v_cmp_883_, lean_object* v_t_884_, lean_object* v_k_885_, lean_object* v_fallback_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_TreeSet_getLTD___redArg(v_cmp_883_, v_t_884_, v_k_885_, v_fallback_886_);
lean_dec(v_fallback_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD(lean_object* v_00_u03b1_888_, lean_object* v_cmp_889_, lean_object* v_t_890_, lean_object* v_k_891_, lean_object* v_fallback_892_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_box(0);
v___x_894_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_889_, v_k_891_, v___x_893_, v_t_890_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_inc(v_fallback_892_);
return v_fallback_892_;
}
else
{
lean_object* v_val_895_; 
v_val_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_val_895_);
lean_dec_ref_known(v___x_894_, 1);
return v_val_895_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___boxed(lean_object* v_00_u03b1_896_, lean_object* v_cmp_897_, lean_object* v_t_898_, lean_object* v_k_899_, lean_object* v_fallback_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_TreeSet_getLTD(v_00_u03b1_896_, v_cmp_897_, v_t_898_, v_k_899_, v_fallback_900_);
lean_dec(v_fallback_900_);
return v_res_901_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_filter___redArg___lam__0(lean_object* v_f_902_, lean_object* v_a_903_, lean_object* v_x_904_){
_start:
{
lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = lean_apply_1(v_f_902_, v_a_903_);
v___x_906_ = lean_unbox(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg___lam__0___boxed(lean_object* v_f_907_, lean_object* v_a_908_, lean_object* v_x_909_){
_start:
{
uint8_t v_res_910_; lean_object* v_r_911_; 
v_res_910_ = l_Std_TreeSet_filter___redArg___lam__0(v_f_907_, v_a_908_, v_x_909_);
v_r_911_ = lean_box(v_res_910_);
return v_r_911_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg(lean_object* v_f_912_, lean_object* v_m_913_){
_start:
{
lean_object* v___f_914_; lean_object* v___x_915_; 
v___f_914_ = lean_alloc_closure((void*)(l_Std_TreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_914_, 0, v_f_912_);
v___x_915_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_914_, v_m_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter(lean_object* v_00_u03b1_916_, lean_object* v_cmp_917_, lean_object* v_f_918_, lean_object* v_m_919_){
_start:
{
lean_object* v___f_920_; lean_object* v___x_921_; 
v___f_920_ = lean_alloc_closure((void*)(l_Std_TreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_920_, 0, v_f_918_);
v___x_921_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_920_, v_m_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___boxed(lean_object* v_00_u03b1_922_, lean_object* v_cmp_923_, lean_object* v_f_924_, lean_object* v_m_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Std_TreeSet_filter(v_00_u03b1_922_, v_cmp_923_, v_f_924_, v_m_925_);
lean_dec_ref(v_cmp_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg___lam__0(lean_object* v_f_927_, lean_object* v_c_928_, lean_object* v_a_929_, lean_object* v_x_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = lean_apply_2(v_f_927_, v_c_928_, v_a_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg(lean_object* v_inst_932_, lean_object* v_f_933_, lean_object* v_init_934_, lean_object* v_t_935_){
_start:
{
lean_object* v___f_936_; lean_object* v___x_937_; 
v___f_936_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_936_, 0, v_f_933_);
v___x_937_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_932_, v___f_936_, v_init_934_, v_t_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM(lean_object* v_00_u03b1_938_, lean_object* v_cmp_939_, lean_object* v_m_940_, lean_object* v_00_u03b4_941_, lean_object* v_inst_942_, lean_object* v_f_943_, lean_object* v_init_944_, lean_object* v_t_945_){
_start:
{
lean_object* v___f_946_; lean_object* v___x_947_; 
v___f_946_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_946_, 0, v_f_943_);
v___x_947_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_942_, v___f_946_, v_init_944_, v_t_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___boxed(lean_object* v_00_u03b1_948_, lean_object* v_cmp_949_, lean_object* v_m_950_, lean_object* v_00_u03b4_951_, lean_object* v_inst_952_, lean_object* v_f_953_, lean_object* v_init_954_, lean_object* v_t_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_TreeSet_foldlM(v_00_u03b1_948_, v_cmp_949_, v_m_950_, v_00_u03b4_951_, v_inst_952_, v_f_953_, v_init_954_, v_t_955_);
lean_dec_ref(v_cmp_949_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___redArg(lean_object* v_f_957_, lean_object* v_init_958_, lean_object* v_t_959_){
_start:
{
lean_object* v___f_960_; lean_object* v___x_961_; 
v___f_960_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_960_, 0, v_f_957_);
v___x_961_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_960_, v_init_958_, v_t_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl(lean_object* v_00_u03b1_962_, lean_object* v_cmp_963_, lean_object* v_00_u03b4_964_, lean_object* v_f_965_, lean_object* v_init_966_, lean_object* v_t_967_){
_start:
{
lean_object* v___f_968_; lean_object* v___x_969_; 
v___f_968_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_968_, 0, v_f_965_);
v___x_969_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_968_, v_init_966_, v_t_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___boxed(lean_object* v_00_u03b1_970_, lean_object* v_cmp_971_, lean_object* v_00_u03b4_972_, lean_object* v_f_973_, lean_object* v_init_974_, lean_object* v_t_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Std_TreeSet_foldl(v_00_u03b1_970_, v_cmp_971_, v_00_u03b4_972_, v_f_973_, v_init_974_, v_t_975_);
lean_dec_ref(v_cmp_971_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg___lam__0(lean_object* v_f_977_, lean_object* v_a_978_, lean_object* v_x_979_, lean_object* v_acc_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = lean_apply_2(v_f_977_, v_a_978_, v_acc_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg(lean_object* v_inst_982_, lean_object* v_f_983_, lean_object* v_init_984_, lean_object* v_t_985_){
_start:
{
lean_object* v___f_986_; lean_object* v___x_987_; 
v___f_986_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_986_, 0, v_f_983_);
v___x_987_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_982_, v___f_986_, v_init_984_, v_t_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM(lean_object* v_00_u03b1_988_, lean_object* v_cmp_989_, lean_object* v_m_990_, lean_object* v_00_u03b4_991_, lean_object* v_inst_992_, lean_object* v_f_993_, lean_object* v_init_994_, lean_object* v_t_995_){
_start:
{
lean_object* v___f_996_; lean_object* v___x_997_; 
v___f_996_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_996_, 0, v_f_993_);
v___x_997_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_992_, v___f_996_, v_init_994_, v_t_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___boxed(lean_object* v_00_u03b1_998_, lean_object* v_cmp_999_, lean_object* v_m_1000_, lean_object* v_00_u03b4_1001_, lean_object* v_inst_1002_, lean_object* v_f_1003_, lean_object* v_init_1004_, lean_object* v_t_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Std_TreeSet_foldrM(v_00_u03b1_998_, v_cmp_999_, v_m_1000_, v_00_u03b4_1001_, v_inst_1002_, v_f_1003_, v_init_1004_, v_t_1005_);
lean_dec_ref(v_cmp_999_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg___lam__0(lean_object* v_f_1007_, lean_object* v_x1_1008_, lean_object* v_x2_1009_, lean_object* v_x3_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_apply_2(v_f_1007_, v_x1_1008_, v_x3_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg(lean_object* v_f_1031_, lean_object* v_init_1032_, lean_object* v_t_1033_){
_start:
{
lean_object* v___f_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___f_1034_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1034_, 0, v_f_1031_);
v___x_1035_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1036_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1035_, v___f_1034_, v_init_1032_, v_t_1033_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr(lean_object* v_00_u03b1_1037_, lean_object* v_cmp_1038_, lean_object* v_00_u03b4_1039_, lean_object* v_f_1040_, lean_object* v_init_1041_, lean_object* v_t_1042_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___boxed(lean_object* v_00_u03b1_1046_, lean_object* v_cmp_1047_, lean_object* v_00_u03b4_1048_, lean_object* v_f_1049_, lean_object* v_init_1050_, lean_object* v_t_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Std_TreeSet_foldr(v_00_u03b1_1046_, v_cmp_1047_, v_00_u03b4_1048_, v_f_1049_, v_init_1050_, v_t_1051_);
lean_dec_ref(v_cmp_1047_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg___lam__0(lean_object* v_f_1053_, lean_object* v_cmp_1054_, lean_object* v_x_1055_, lean_object* v_a_1056_, lean_object* v_b_1057_){
_start:
{
lean_object* v_fst_1058_; lean_object* v_snd_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1073_; 
v_fst_1058_ = lean_ctor_get(v_x_1055_, 0);
v_snd_1059_ = lean_ctor_get(v_x_1055_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_x_1055_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1061_ = v_x_1055_;
v_isShared_1062_ = v_isSharedCheck_1073_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_snd_1059_);
lean_inc(v_fst_1058_);
lean_dec(v_x_1055_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1073_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; uint8_t v___x_1064_; 
lean_inc(v_a_1056_);
v___x_1063_ = lean_apply_1(v_f_1053_, v_a_1056_);
v___x_1064_ = lean_unbox(v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1054_, v_a_1056_, v_b_1057_, v_snd_1059_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v___x_1065_);
v___x_1067_ = v___x_1061_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_fst_1058_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1069_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1054_, v_a_1056_, v_b_1057_, v_fst_1058_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1069_);
v___x_1071_ = v___x_1061_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_snd_1059_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg(lean_object* v_cmp_1076_, lean_object* v_f_1077_, lean_object* v_t_1078_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_partition(lean_object* v_00_u03b1_1091_, lean_object* v_cmp_1092_, lean_object* v_f_1093_, lean_object* v_t_1094_){
_start:
{
lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v_p_1097_; lean_object* v_fst_1098_; lean_object* v_snd_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
v___f_1095_ = lean_alloc_closure((void*)(l_Std_TreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1095_, 0, v_f_1093_);
lean_closure_set(v___f_1095_, 1, v_cmp_1092_);
v___x_1096_ = ((lean_object*)(l_Std_TreeSet_partition___redArg___closed__0));
v_p_1097_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1095_, v___x_1096_, v_t_1094_);
v_fst_1098_ = lean_ctor_get(v_p_1097_, 0);
v_snd_1099_ = lean_ctor_get(v_p_1097_, 1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_p_1097_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v_p_1097_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_snd_1099_);
lean_inc(v_fst_1098_);
lean_dec(v_p_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_fst_1098_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_snd_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg___lam__0(lean_object* v_f_1107_, lean_object* v_x_1108_, lean_object* v_k_1109_, lean_object* v_v_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_apply_1(v_f_1107_, v_k_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg(lean_object* v_inst_1112_, lean_object* v_f_1113_, lean_object* v_t_1114_){
_start:
{
lean_object* v___f_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___f_1115_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1115_, 0, v_f_1113_);
v___x_1116_ = lean_box(0);
v___x_1117_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1112_, v___f_1115_, v___x_1116_, v_t_1114_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM(lean_object* v_00_u03b1_1118_, lean_object* v_cmp_1119_, lean_object* v_m_1120_, lean_object* v_inst_1121_, lean_object* v_f_1122_, lean_object* v_t_1123_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_cmp_1128_, lean_object* v_m_1129_, lean_object* v_inst_1130_, lean_object* v_f_1131_, lean_object* v_t_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Std_TreeSet_forM(v_00_u03b1_1127_, v_cmp_1128_, v_m_1129_, v_inst_1130_, v_f_1131_, v_t_1132_);
lean_dec_ref(v_cmp_1128_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__0(lean_object* v_f_1134_, lean_object* v_a_1135_, lean_object* v_b_1136_, lean_object* v_c_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_apply_2(v_f_1134_, v_a_1135_, v_c_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__1(lean_object* v_toPure_1139_, lean_object* v_____do__lift_1140_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg(lean_object* v_inst_1143_, lean_object* v_f_1144_, lean_object* v_init_1145_, lean_object* v_t_1146_){
_start:
{
lean_object* v_toApplicative_1147_; lean_object* v_toBind_1148_; lean_object* v_toPure_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; lean_object* v___f_1152_; lean_object* v___x_1153_; 
v_toApplicative_1147_ = lean_ctor_get(v_inst_1143_, 0);
v_toBind_1148_ = lean_ctor_get(v_inst_1143_, 1);
lean_inc(v_toBind_1148_);
v_toPure_1149_ = lean_ctor_get(v_toApplicative_1147_, 1);
lean_inc(v_toPure_1149_);
v___f_1150_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1150_, 0, v_f_1144_);
v___x_1151_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1143_, v___f_1150_, v_init_1145_, v_t_1146_);
v___f_1152_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1152_, 0, v_toPure_1149_);
v___x_1153_ = lean_apply_4(v_toBind_1148_, lean_box(0), lean_box(0), v___x_1151_, v___f_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn(lean_object* v_00_u03b1_1154_, lean_object* v_cmp_1155_, lean_object* v_00_u03b4_1156_, lean_object* v_m_1157_, lean_object* v_inst_1158_, lean_object* v_f_1159_, lean_object* v_init_1160_, lean_object* v_t_1161_){
_start:
{
lean_object* v_toApplicative_1162_; lean_object* v_toBind_1163_; lean_object* v_toPure_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___f_1167_; lean_object* v___x_1168_; 
v_toApplicative_1162_ = lean_ctor_get(v_inst_1158_, 0);
v_toBind_1163_ = lean_ctor_get(v_inst_1158_, 1);
lean_inc(v_toBind_1163_);
v_toPure_1164_ = lean_ctor_get(v_toApplicative_1162_, 1);
lean_inc(v_toPure_1164_);
v___f_1165_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1165_, 0, v_f_1159_);
v___x_1166_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1158_, v___f_1165_, v_init_1160_, v_t_1161_);
v___f_1167_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1167_, 0, v_toPure_1164_);
v___x_1168_ = lean_apply_4(v_toBind_1163_, lean_box(0), lean_box(0), v___x_1166_, v___f_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_cmp_1170_, lean_object* v_00_u03b4_1171_, lean_object* v_m_1172_, lean_object* v_inst_1173_, lean_object* v_f_1174_, lean_object* v_init_1175_, lean_object* v_t_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_TreeSet_forIn(v_00_u03b1_1169_, v_cmp_1170_, v_00_u03b4_1171_, v_m_1172_, v_inst_1173_, v_f_1174_, v_init_1175_, v_t_1176_);
lean_dec_ref(v_cmp_1170_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg___lam__1(lean_object* v_inst_1178_, lean_object* v_t_1179_, lean_object* v_f_1180_){
_start:
{
lean_object* v___f_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___f_1181_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1181_, 0, v_f_1180_);
v___x_1182_ = lean_box(0);
v___x_1183_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1178_, v___f_1181_, v___x_1182_, v_t_1179_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg(lean_object* v_inst_1184_){
_start:
{
lean_object* v___f_1185_; 
v___f_1185_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1185_, 0, v_inst_1184_);
return v___f_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad(lean_object* v_00_u03b1_1186_, lean_object* v_cmp_1187_, lean_object* v_m_1188_, lean_object* v_inst_1189_){
_start:
{
lean_object* v___f_1190_; 
v___f_1190_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1190_, 0, v_inst_1189_);
return v___f_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___boxed(lean_object* v_00_u03b1_1191_, lean_object* v_cmp_1192_, lean_object* v_m_1193_, lean_object* v_inst_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Std_TreeSet_instForMOfMonad(v_00_u03b1_1191_, v_cmp_1192_, v_m_1193_, v_inst_1194_);
lean_dec_ref(v_cmp_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg___lam__2(lean_object* v_inst_1196_, lean_object* v_00_u03b2_1197_, lean_object* v_m_1198_, lean_object* v_init_1199_, lean_object* v_f_1200_){
_start:
{
lean_object* v_toApplicative_1201_; lean_object* v_toBind_1202_; lean_object* v_toPure_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; 
v_toApplicative_1201_ = lean_ctor_get(v_inst_1196_, 0);
v_toBind_1202_ = lean_ctor_get(v_inst_1196_, 1);
lean_inc(v_toBind_1202_);
v_toPure_1203_ = lean_ctor_get(v_toApplicative_1201_, 1);
lean_inc(v_toPure_1203_);
v___f_1204_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1204_, 0, v_f_1200_);
v___x_1205_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1196_, v___f_1204_, v_init_1199_, v_m_1198_);
v___f_1206_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1206_, 0, v_toPure_1203_);
v___x_1207_ = lean_apply_4(v_toBind_1202_, lean_box(0), lean_box(0), v___x_1205_, v___f_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg(lean_object* v_inst_1208_){
_start:
{
lean_object* v___f_1209_; 
v___f_1209_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1209_, 0, v_inst_1208_);
return v___f_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad(lean_object* v_00_u03b1_1210_, lean_object* v_cmp_1211_, lean_object* v_m_1212_, lean_object* v_inst_1213_){
_start:
{
lean_object* v___f_1214_; 
v___f_1214_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1214_, 0, v_inst_1213_);
return v___f_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_1215_, lean_object* v_cmp_1216_, lean_object* v_m_1217_, lean_object* v_inst_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_TreeSet_instForInOfMonad(v_00_u03b1_1215_, v_cmp_1216_, v_m_1217_, v_inst_1218_);
lean_dec_ref(v_cmp_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0(lean_object* v_p_1220_, lean_object* v___x_1221_, lean_object* v___x_1222_, lean_object* v_a_1223_, lean_object* v_b_1224_, lean_object* v_acc_1225_){
_start:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_apply_1(v_p_1220_, v_a_1223_);
v___x_1227_ = lean_unbox(v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1221_);
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec_ref(v___x_1221_);
v___x_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1226_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v___x_1222_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0___boxed(lean_object* v_p_1232_, lean_object* v___x_1233_, lean_object* v___x_1234_, lean_object* v_a_1235_, lean_object* v_b_1236_, lean_object* v_acc_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Std_TreeSet_any___redArg___lam__0(v_p_1232_, v___x_1233_, v___x_1234_, v_a_1235_, v_b_1236_, v_acc_1237_);
lean_dec_ref(v_acc_1237_);
return v_res_1238_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_any___redArg(lean_object* v_t_1242_, lean_object* v_p_1243_){
_start:
{
lean_object* v___y_1245_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___f_1253_; lean_object* v___x_1254_; lean_object* v_a_1255_; 
v___x_1250_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1251_ = lean_box(0);
v___x_1252_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1253_ = lean_alloc_closure((void*)(l_Std_TreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1253_, 0, v_p_1243_);
lean_closure_set(v___f_1253_, 1, v___x_1252_);
lean_closure_set(v___f_1253_, 2, v___x_1251_);
v___x_1254_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1250_, v___f_1253_, v___x_1252_, v_t_1242_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___y_1245_ = v_a_1255_;
goto v___jp_1244_;
v___jp_1244_:
{
lean_object* v_fst_1246_; 
v_fst_1246_ = lean_ctor_get(v___y_1245_, 0);
lean_inc(v_fst_1246_);
lean_dec_ref(v___y_1245_);
if (lean_obj_tag(v_fst_1246_) == 0)
{
uint8_t v___x_1247_; 
v___x_1247_ = 0;
return v___x_1247_;
}
else
{
lean_object* v_val_1248_; uint8_t v___x_1249_; 
v_val_1248_ = lean_ctor_get(v_fst_1246_, 0);
lean_inc(v_val_1248_);
lean_dec_ref_known(v_fst_1246_, 1);
v___x_1249_ = lean_unbox(v_val_1248_);
lean_dec(v_val_1248_);
return v___x_1249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___boxed(lean_object* v_t_1256_, lean_object* v_p_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l_Std_TreeSet_any___redArg(v_t_1256_, v_p_1257_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_any(lean_object* v_00_u03b1_1260_, lean_object* v_cmp_1261_, lean_object* v_t_1262_, lean_object* v_p_1263_){
_start:
{
lean_object* v___y_1265_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___f_1273_; lean_object* v___x_1274_; lean_object* v_a_1275_; 
v___x_1270_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1271_ = lean_box(0);
v___x_1272_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1273_ = lean_alloc_closure((void*)(l_Std_TreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1273_, 0, v_p_1263_);
lean_closure_set(v___f_1273_, 1, v___x_1272_);
lean_closure_set(v___f_1273_, 2, v___x_1271_);
v___x_1274_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1270_, v___f_1273_, v___x_1272_, v_t_1262_);
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___y_1265_ = v_a_1275_;
goto v___jp_1264_;
v___jp_1264_:
{
lean_object* v_fst_1266_; 
v_fst_1266_ = lean_ctor_get(v___y_1265_, 0);
lean_inc(v_fst_1266_);
lean_dec_ref(v___y_1265_);
if (lean_obj_tag(v_fst_1266_) == 0)
{
uint8_t v___x_1267_; 
v___x_1267_ = 0;
return v___x_1267_;
}
else
{
lean_object* v_val_1268_; uint8_t v___x_1269_; 
v_val_1268_ = lean_ctor_get(v_fst_1266_, 0);
lean_inc(v_val_1268_);
lean_dec_ref_known(v_fst_1266_, 1);
v___x_1269_ = lean_unbox(v_val_1268_);
lean_dec(v_val_1268_);
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___boxed(lean_object* v_00_u03b1_1276_, lean_object* v_cmp_1277_, lean_object* v_t_1278_, lean_object* v_p_1279_){
_start:
{
uint8_t v_res_1280_; lean_object* v_r_1281_; 
v_res_1280_ = l_Std_TreeSet_any(v_00_u03b1_1276_, v_cmp_1277_, v_t_1278_, v_p_1279_);
lean_dec_ref(v_cmp_1277_);
v_r_1281_ = lean_box(v_res_1280_);
return v_r_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0(lean_object* v_p_1282_, lean_object* v___x_1283_, lean_object* v___x_1284_, lean_object* v_a_1285_, lean_object* v_b_1286_, lean_object* v_acc_1287_){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = lean_apply_1(v_p_1282_, v_a_1285_);
v___x_1289_ = lean_unbox(v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec_ref(v___x_1284_);
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1283_);
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1284_);
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0___boxed(lean_object* v_p_1294_, lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v_a_1297_, lean_object* v_b_1298_, lean_object* v_acc_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Std_TreeSet_all___redArg___lam__0(v_p_1294_, v___x_1295_, v___x_1296_, v_a_1297_, v_b_1298_, v_acc_1299_);
lean_dec_ref(v_acc_1299_);
return v_res_1300_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_all___redArg(lean_object* v_t_1301_, lean_object* v_p_1302_){
_start:
{
lean_object* v___y_1304_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___f_1312_; lean_object* v___x_1313_; lean_object* v_a_1314_; 
v___x_1309_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1310_ = lean_box(0);
v___x_1311_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1312_ = lean_alloc_closure((void*)(l_Std_TreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1312_, 0, v_p_1302_);
lean_closure_set(v___f_1312_, 1, v___x_1310_);
lean_closure_set(v___f_1312_, 2, v___x_1311_);
v___x_1313_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1309_, v___f_1312_, v___x_1311_, v_t_1301_);
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___y_1304_ = v_a_1314_;
goto v___jp_1303_;
v___jp_1303_:
{
lean_object* v_fst_1305_; 
v_fst_1305_ = lean_ctor_get(v___y_1304_, 0);
lean_inc(v_fst_1305_);
lean_dec_ref(v___y_1304_);
if (lean_obj_tag(v_fst_1305_) == 0)
{
uint8_t v___x_1306_; 
v___x_1306_ = 1;
return v___x_1306_;
}
else
{
lean_object* v_val_1307_; uint8_t v___x_1308_; 
v_val_1307_ = lean_ctor_get(v_fst_1305_, 0);
lean_inc(v_val_1307_);
lean_dec_ref_known(v_fst_1305_, 1);
v___x_1308_ = lean_unbox(v_val_1307_);
lean_dec(v_val_1307_);
return v___x_1308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___boxed(lean_object* v_t_1315_, lean_object* v_p_1316_){
_start:
{
uint8_t v_res_1317_; lean_object* v_r_1318_; 
v_res_1317_ = l_Std_TreeSet_all___redArg(v_t_1315_, v_p_1316_);
v_r_1318_ = lean_box(v_res_1317_);
return v_r_1318_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_all(lean_object* v_00_u03b1_1319_, lean_object* v_cmp_1320_, lean_object* v_t_1321_, lean_object* v_p_1322_){
_start:
{
lean_object* v___y_1324_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___f_1332_; lean_object* v___x_1333_; lean_object* v_a_1334_; 
v___x_1329_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1330_ = lean_box(0);
v___x_1331_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1332_ = lean_alloc_closure((void*)(l_Std_TreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1332_, 0, v_p_1322_);
lean_closure_set(v___f_1332_, 1, v___x_1330_);
lean_closure_set(v___f_1332_, 2, v___x_1331_);
v___x_1333_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1329_, v___f_1332_, v___x_1331_, v_t_1321_);
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___y_1324_ = v_a_1334_;
goto v___jp_1323_;
v___jp_1323_:
{
lean_object* v_fst_1325_; 
v_fst_1325_ = lean_ctor_get(v___y_1324_, 0);
lean_inc(v_fst_1325_);
lean_dec_ref(v___y_1324_);
if (lean_obj_tag(v_fst_1325_) == 0)
{
uint8_t v___x_1326_; 
v___x_1326_ = 1;
return v___x_1326_;
}
else
{
lean_object* v_val_1327_; uint8_t v___x_1328_; 
v_val_1327_ = lean_ctor_get(v_fst_1325_, 0);
lean_inc(v_val_1327_);
lean_dec_ref_known(v_fst_1325_, 1);
v___x_1328_ = lean_unbox(v_val_1327_);
lean_dec(v_val_1327_);
return v___x_1328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___boxed(lean_object* v_00_u03b1_1335_, lean_object* v_cmp_1336_, lean_object* v_t_1337_, lean_object* v_p_1338_){
_start:
{
uint8_t v_res_1339_; lean_object* v_r_1340_; 
v_res_1339_ = l_Std_TreeSet_all(v_00_u03b1_1335_, v_cmp_1336_, v_t_1337_, v_p_1338_);
lean_dec_ref(v_cmp_1336_);
v_r_1340_ = lean_box(v_res_1339_);
return v_r_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg___lam__0(lean_object* v_x1_1341_, lean_object* v_x2_1342_, lean_object* v_x3_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_x1_1341_);
lean_ctor_set(v___x_1344_, 1, v_x3_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg(lean_object* v_t_1346_){
_start:
{
lean_object* v___f_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___f_1347_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___x_1348_ = lean_box(0);
v___x_1349_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1350_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1349_, v___f_1347_, v___x_1348_, v_t_1346_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList(lean_object* v_00_u03b1_1351_, lean_object* v_cmp_1352_, lean_object* v_t_1353_){
_start:
{
lean_object* v___f_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___f_1354_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___x_1355_ = lean_box(0);
v___x_1356_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1357_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1356_, v___f_1354_, v___x_1355_, v_t_1353_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___boxed(lean_object* v_00_u03b1_1358_, lean_object* v_cmp_1359_, lean_object* v_t_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_TreeSet_toList(v_00_u03b1_1358_, v_cmp_1359_, v_t_1360_);
lean_dec_ref(v_cmp_1359_);
return v_res_1361_;
}
}
static lean_object* _init_l_Std_TreeSet_ofList___auto__1(void){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__26, &l_Std_TreeSet___auto__1___closed__26_once, _init_l_Std_TreeSet___auto__1___closed__26);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(lean_object* v_cmp_1363_, lean_object* v_k_1364_, lean_object* v_v_1365_, lean_object* v_t_1366_){
_start:
{
if (lean_obj_tag(v_t_1366_) == 0)
{
lean_object* v_size_1367_; lean_object* v_k_1368_; lean_object* v_v_1369_; lean_object* v_l_1370_; lean_object* v_r_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1652_; 
v_size_1367_ = lean_ctor_get(v_t_1366_, 0);
v_k_1368_ = lean_ctor_get(v_t_1366_, 1);
v_v_1369_ = lean_ctor_get(v_t_1366_, 2);
v_l_1370_ = lean_ctor_get(v_t_1366_, 3);
v_r_1371_ = lean_ctor_get(v_t_1366_, 4);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_t_1366_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1373_ = v_t_1366_;
v_isShared_1374_ = v_isSharedCheck_1652_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_r_1371_);
lean_inc(v_l_1370_);
lean_inc(v_v_1369_);
lean_inc(v_k_1368_);
lean_inc(v_size_1367_);
lean_dec(v_t_1366_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1652_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
lean_inc_ref(v_cmp_1363_);
lean_inc(v_k_1368_);
lean_inc(v_k_1364_);
v___x_1375_ = lean_apply_2(v_cmp_1363_, v_k_1364_, v_k_1368_);
v___x_1376_ = lean_unbox(v___x_1375_);
switch(v___x_1376_)
{
case 0:
{
lean_object* v_impl_1377_; lean_object* v___x_1378_; 
lean_dec(v_size_1367_);
v_impl_1377_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1363_, v_k_1364_, v_v_1365_, v_l_1370_);
v___x_1378_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1371_) == 0)
{
lean_object* v_size_1379_; lean_object* v_size_1380_; lean_object* v_k_1381_; lean_object* v_v_1382_; lean_object* v_l_1383_; lean_object* v_r_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_size_1379_ = lean_ctor_get(v_r_1371_, 0);
v_size_1380_ = lean_ctor_get(v_impl_1377_, 0);
lean_inc(v_size_1380_);
v_k_1381_ = lean_ctor_get(v_impl_1377_, 1);
lean_inc(v_k_1381_);
v_v_1382_ = lean_ctor_get(v_impl_1377_, 2);
lean_inc(v_v_1382_);
v_l_1383_ = lean_ctor_get(v_impl_1377_, 3);
lean_inc(v_l_1383_);
v_r_1384_ = lean_ctor_get(v_impl_1377_, 4);
lean_inc(v_r_1384_);
v___x_1385_ = lean_unsigned_to_nat(3u);
v___x_1386_ = lean_nat_mul(v___x_1385_, v_size_1379_);
v___x_1387_ = lean_nat_dec_lt(v___x_1386_, v_size_1380_);
lean_dec(v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_dec(v_r_1384_);
lean_dec(v_l_1383_);
lean_dec(v_v_1382_);
lean_dec(v_k_1381_);
v___x_1388_ = lean_nat_add(v___x_1378_, v_size_1380_);
lean_dec(v_size_1380_);
v___x_1389_ = lean_nat_add(v___x_1388_, v_size_1379_);
lean_dec(v___x_1388_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 3, v_impl_1377_);
lean_ctor_set(v___x_1373_, 0, v___x_1389_);
v___x_1391_ = v___x_1373_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_impl_1377_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v_r_1371_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
else
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1458_; 
v_isSharedCheck_1458_ = !lean_is_exclusive(v_impl_1377_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; lean_object* v_unused_1462_; lean_object* v_unused_1463_; 
v_unused_1459_ = lean_ctor_get(v_impl_1377_, 4);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_impl_1377_, 3);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_impl_1377_, 2);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_impl_1377_, 1);
lean_dec(v_unused_1462_);
v_unused_1463_ = lean_ctor_get(v_impl_1377_, 0);
lean_dec(v_unused_1463_);
v___x_1394_ = v_impl_1377_;
v_isShared_1395_ = v_isSharedCheck_1458_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v_impl_1377_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1458_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v_size_1396_; lean_object* v_size_1397_; lean_object* v_k_1398_; lean_object* v_v_1399_; lean_object* v_l_1400_; lean_object* v_r_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_size_1396_ = lean_ctor_get(v_l_1383_, 0);
v_size_1397_ = lean_ctor_get(v_r_1384_, 0);
v_k_1398_ = lean_ctor_get(v_r_1384_, 1);
v_v_1399_ = lean_ctor_get(v_r_1384_, 2);
v_l_1400_ = lean_ctor_get(v_r_1384_, 3);
v_r_1401_ = lean_ctor_get(v_r_1384_, 4);
v___x_1402_ = lean_unsigned_to_nat(2u);
v___x_1403_ = lean_nat_mul(v___x_1402_, v_size_1396_);
v___x_1404_ = lean_nat_dec_lt(v_size_1397_, v___x_1403_);
lean_dec(v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1433_; 
lean_inc(v_r_1401_);
lean_inc(v_l_1400_);
lean_inc(v_v_1399_);
lean_inc(v_k_1398_);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_r_1384_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; lean_object* v_unused_1435_; lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; 
v_unused_1434_ = lean_ctor_get(v_r_1384_, 4);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_r_1384_, 3);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_r_1384_, 2);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_r_1384_, 1);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_r_1384_, 0);
lean_dec(v_unused_1438_);
v___x_1406_ = v_r_1384_;
v_isShared_1407_ = v_isSharedCheck_1433_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v_r_1384_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1433_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___x_1421_; lean_object* v___y_1423_; 
v___x_1408_ = lean_nat_add(v___x_1378_, v_size_1380_);
lean_dec(v_size_1380_);
v___x_1409_ = lean_nat_add(v___x_1408_, v_size_1379_);
lean_dec(v___x_1408_);
v___x_1421_ = lean_nat_add(v___x_1378_, v_size_1396_);
if (lean_obj_tag(v_l_1400_) == 0)
{
lean_object* v_size_1431_; 
v_size_1431_ = lean_ctor_get(v_l_1400_, 0);
lean_inc(v_size_1431_);
v___y_1423_ = v_size_1431_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_unsigned_to_nat(0u);
v___y_1423_ = v___x_1432_;
goto v___jp_1422_;
}
v___jp_1410_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_nat_add(v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec(v___y_1412_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 4, v_r_1371_);
lean_ctor_set(v___x_1406_, 3, v_r_1401_);
lean_ctor_set(v___x_1406_, 2, v_v_1369_);
lean_ctor_set(v___x_1406_, 1, v_k_1368_);
lean_ctor_set(v___x_1406_, 0, v___x_1414_);
v___x_1416_ = v___x_1406_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_r_1401_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_r_1371_);
v___x_1416_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v___x_1416_);
lean_ctor_set(v___x_1394_, 3, v___y_1411_);
lean_ctor_set(v___x_1394_, 2, v_v_1399_);
lean_ctor_set(v___x_1394_, 1, v_k_1398_);
lean_ctor_set(v___x_1394_, 0, v___x_1409_);
v___x_1418_ = v___x_1394_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_k_1398_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_v_1399_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v___y_1411_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
v___jp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = lean_nat_add(v___x_1421_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec(v___x_1421_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v_l_1400_);
lean_ctor_set(v___x_1373_, 3, v_l_1383_);
lean_ctor_set(v___x_1373_, 2, v_v_1382_);
lean_ctor_set(v___x_1373_, 1, v_k_1381_);
lean_ctor_set(v___x_1373_, 0, v___x_1424_);
v___x_1426_ = v___x_1373_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v_l_1383_);
lean_ctor_set(v_reuseFailAlloc_1430_, 4, v_l_1400_);
v___x_1426_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_nat_add(v___x_1378_, v_size_1379_);
if (lean_obj_tag(v_r_1401_) == 0)
{
lean_object* v_size_1428_; 
v_size_1428_ = lean_ctor_get(v_r_1401_, 0);
lean_inc(v_size_1428_);
v___y_1411_ = v___x_1426_;
v___y_1412_ = v___x_1427_;
v___y_1413_ = v_size_1428_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_unsigned_to_nat(0u);
v___y_1411_ = v___x_1426_;
v___y_1412_ = v___x_1427_;
v___y_1413_ = v___x_1429_;
goto v___jp_1410_;
}
}
}
}
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
lean_del_object(v___x_1373_);
v___x_1439_ = lean_nat_add(v___x_1378_, v_size_1380_);
lean_dec(v_size_1380_);
v___x_1440_ = lean_nat_add(v___x_1439_, v_size_1379_);
lean_dec(v___x_1439_);
v___x_1441_ = lean_nat_add(v___x_1378_, v_size_1379_);
v___x_1442_ = lean_nat_add(v___x_1441_, v_size_1397_);
lean_dec(v___x_1441_);
lean_inc_ref(v_r_1371_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v_r_1371_);
lean_ctor_set(v___x_1394_, 3, v_r_1384_);
lean_ctor_set(v___x_1394_, 2, v_v_1369_);
lean_ctor_set(v___x_1394_, 1, v_k_1368_);
lean_ctor_set(v___x_1394_, 0, v___x_1442_);
v___x_1444_ = v___x_1394_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_r_1384_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_r_1371_);
v___x_1444_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
v_isSharedCheck_1451_ = !lean_is_exclusive(v_r_1371_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; lean_object* v_unused_1455_; lean_object* v_unused_1456_; 
v_unused_1452_ = lean_ctor_get(v_r_1371_, 4);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_r_1371_, 3);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_r_1371_, 2);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_r_1371_, 1);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_r_1371_, 0);
lean_dec(v_unused_1456_);
v___x_1446_ = v_r_1371_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v_r_1371_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 4, v___x_1444_);
lean_ctor_set(v___x_1446_, 3, v_l_1383_);
lean_ctor_set(v___x_1446_, 2, v_v_1382_);
lean_ctor_set(v___x_1446_, 1, v_k_1381_);
lean_ctor_set(v___x_1446_, 0, v___x_1440_);
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_l_1383_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v___x_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1464_; 
v_l_1464_ = lean_ctor_get(v_impl_1377_, 3);
lean_inc(v_l_1464_);
if (lean_obj_tag(v_l_1464_) == 0)
{
lean_object* v_r_1465_; lean_object* v_k_1466_; lean_object* v_v_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1478_; 
v_r_1465_ = lean_ctor_get(v_impl_1377_, 4);
v_k_1466_ = lean_ctor_get(v_impl_1377_, 1);
v_v_1467_ = lean_ctor_get(v_impl_1377_, 2);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_impl_1377_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; lean_object* v_unused_1480_; 
v_unused_1479_ = lean_ctor_get(v_impl_1377_, 3);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_impl_1377_, 0);
lean_dec(v_unused_1480_);
v___x_1469_ = v_impl_1377_;
v_isShared_1470_ = v_isSharedCheck_1478_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_r_1465_);
lean_inc(v_v_1467_);
lean_inc(v_k_1466_);
lean_dec(v_impl_1377_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1478_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1471_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1465_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 3, v_r_1465_);
lean_ctor_set(v___x_1469_, 2, v_v_1369_);
lean_ctor_set(v___x_1469_, 1, v_k_1368_);
lean_ctor_set(v___x_1469_, 0, v___x_1378_);
v___x_1473_ = v___x_1469_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_r_1465_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_r_1465_);
v___x_1473_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1475_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v___x_1473_);
lean_ctor_set(v___x_1373_, 3, v_l_1464_);
lean_ctor_set(v___x_1373_, 2, v_v_1467_);
lean_ctor_set(v___x_1373_, 1, v_k_1466_);
lean_ctor_set(v___x_1373_, 0, v___x_1471_);
v___x_1475_ = v___x_1373_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_k_1466_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_v_1467_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_l_1464_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v_r_1481_; 
v_r_1481_ = lean_ctor_get(v_impl_1377_, 4);
lean_inc(v_r_1481_);
if (lean_obj_tag(v_r_1481_) == 0)
{
lean_object* v_k_1482_; lean_object* v_v_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1506_; 
v_k_1482_ = lean_ctor_get(v_impl_1377_, 1);
v_v_1483_ = lean_ctor_get(v_impl_1377_, 2);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_impl_1377_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; lean_object* v_unused_1508_; lean_object* v_unused_1509_; 
v_unused_1507_ = lean_ctor_get(v_impl_1377_, 4);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_impl_1377_, 3);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_impl_1377_, 0);
lean_dec(v_unused_1509_);
v___x_1485_ = v_impl_1377_;
v_isShared_1486_ = v_isSharedCheck_1506_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_v_1483_);
lean_inc(v_k_1482_);
lean_dec(v_impl_1377_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1506_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_k_1487_; lean_object* v_v_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1502_; 
v_k_1487_ = lean_ctor_get(v_r_1481_, 1);
v_v_1488_ = lean_ctor_get(v_r_1481_, 2);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_r_1481_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; 
v_unused_1503_ = lean_ctor_get(v_r_1481_, 4);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_r_1481_, 3);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_r_1481_, 0);
lean_dec(v_unused_1505_);
v___x_1490_ = v_r_1481_;
v_isShared_1491_ = v_isSharedCheck_1502_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_v_1488_);
lean_inc(v_k_1487_);
lean_dec(v_r_1481_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1502_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = lean_unsigned_to_nat(3u);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 4, v_l_1464_);
lean_ctor_set(v___x_1490_, 3, v_l_1464_);
lean_ctor_set(v___x_1490_, 2, v_v_1483_);
lean_ctor_set(v___x_1490_, 1, v_k_1482_);
lean_ctor_set(v___x_1490_, 0, v___x_1378_);
v___x_1494_ = v___x_1490_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1482_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1483_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_l_1464_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_l_1464_);
v___x_1494_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 4, v_l_1464_);
lean_ctor_set(v___x_1485_, 2, v_v_1369_);
lean_ctor_set(v___x_1485_, 1, v_k_1368_);
lean_ctor_set(v___x_1485_, 0, v___x_1378_);
v___x_1496_ = v___x_1485_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1464_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_l_1464_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v___x_1496_);
lean_ctor_set(v___x_1373_, 3, v___x_1494_);
lean_ctor_set(v___x_1373_, 2, v_v_1488_);
lean_ctor_set(v___x_1373_, 1, v_k_1487_);
lean_ctor_set(v___x_1373_, 0, v___x_1492_);
v___x_1498_ = v___x_1373_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1487_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1488_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = lean_unsigned_to_nat(2u);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v_r_1481_);
lean_ctor_set(v___x_1373_, 3, v_impl_1377_);
lean_ctor_set(v___x_1373_, 0, v___x_1510_);
v___x_1512_ = v___x_1373_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v_impl_1377_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v_r_1481_);
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
case 1:
{
lean_object* v___x_1515_; 
lean_dec(v_v_1369_);
lean_dec(v_k_1368_);
lean_dec_ref(v_cmp_1363_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 2, v_v_1365_);
lean_ctor_set(v___x_1373_, 1, v_k_1364_);
v___x_1515_ = v___x_1373_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_size_1367_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_l_1370_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v_r_1371_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
default: 
{
lean_object* v_impl_1517_; lean_object* v___x_1518_; 
lean_dec(v_size_1367_);
v_impl_1517_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1363_, v_k_1364_, v_v_1365_, v_r_1371_);
v___x_1518_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1370_) == 0)
{
lean_object* v_size_1519_; lean_object* v_size_1520_; lean_object* v_k_1521_; lean_object* v_v_1522_; lean_object* v_l_1523_; lean_object* v_r_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v_size_1519_ = lean_ctor_get(v_l_1370_, 0);
v_size_1520_ = lean_ctor_get(v_impl_1517_, 0);
lean_inc(v_size_1520_);
v_k_1521_ = lean_ctor_get(v_impl_1517_, 1);
lean_inc(v_k_1521_);
v_v_1522_ = lean_ctor_get(v_impl_1517_, 2);
lean_inc(v_v_1522_);
v_l_1523_ = lean_ctor_get(v_impl_1517_, 3);
lean_inc(v_l_1523_);
v_r_1524_ = lean_ctor_get(v_impl_1517_, 4);
lean_inc(v_r_1524_);
v___x_1525_ = lean_unsigned_to_nat(3u);
v___x_1526_ = lean_nat_mul(v___x_1525_, v_size_1519_);
v___x_1527_ = lean_nat_dec_lt(v___x_1526_, v_size_1520_);
lean_dec(v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
lean_dec(v_r_1524_);
lean_dec(v_l_1523_);
lean_dec(v_v_1522_);
lean_dec(v_k_1521_);
v___x_1528_ = lean_nat_add(v___x_1518_, v_size_1519_);
v___x_1529_ = lean_nat_add(v___x_1528_, v_size_1520_);
lean_dec(v_size_1520_);
lean_dec(v___x_1528_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v_impl_1517_);
lean_ctor_set(v___x_1373_, 0, v___x_1529_);
v___x_1531_ = v___x_1373_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_l_1370_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v_impl_1517_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
else
{
lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1596_; 
v_isSharedCheck_1596_ = !lean_is_exclusive(v_impl_1517_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; 
v_unused_1597_ = lean_ctor_get(v_impl_1517_, 4);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_impl_1517_, 3);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_impl_1517_, 2);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_impl_1517_, 1);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_impl_1517_, 0);
lean_dec(v_unused_1601_);
v___x_1534_ = v_impl_1517_;
v_isShared_1535_ = v_isSharedCheck_1596_;
goto v_resetjp_1533_;
}
else
{
lean_dec(v_impl_1517_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1596_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v_size_1536_; lean_object* v_k_1537_; lean_object* v_v_1538_; lean_object* v_l_1539_; lean_object* v_r_1540_; lean_object* v_size_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_size_1536_ = lean_ctor_get(v_l_1523_, 0);
v_k_1537_ = lean_ctor_get(v_l_1523_, 1);
v_v_1538_ = lean_ctor_get(v_l_1523_, 2);
v_l_1539_ = lean_ctor_get(v_l_1523_, 3);
v_r_1540_ = lean_ctor_get(v_l_1523_, 4);
v_size_1541_ = lean_ctor_get(v_r_1524_, 0);
v___x_1542_ = lean_unsigned_to_nat(2u);
v___x_1543_ = lean_nat_mul(v___x_1542_, v_size_1541_);
v___x_1544_ = lean_nat_dec_lt(v_size_1536_, v___x_1543_);
lean_dec(v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1572_; 
lean_inc(v_r_1540_);
lean_inc(v_l_1539_);
lean_inc(v_v_1538_);
lean_inc(v_k_1537_);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_l_1523_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; lean_object* v_unused_1574_; lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; 
v_unused_1573_ = lean_ctor_get(v_l_1523_, 4);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v_l_1523_, 3);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_l_1523_, 2);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_l_1523_, 1);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_l_1523_, 0);
lean_dec(v_unused_1577_);
v___x_1546_ = v_l_1523_;
v_isShared_1547_ = v_isSharedCheck_1572_;
goto v_resetjp_1545_;
}
else
{
lean_dec(v_l_1523_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1572_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1562_; 
v___x_1548_ = lean_nat_add(v___x_1518_, v_size_1519_);
v___x_1549_ = lean_nat_add(v___x_1548_, v_size_1520_);
lean_dec(v_size_1520_);
if (lean_obj_tag(v_l_1539_) == 0)
{
lean_object* v_size_1570_; 
v_size_1570_ = lean_ctor_get(v_l_1539_, 0);
lean_inc(v_size_1570_);
v___y_1562_ = v_size_1570_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_unsigned_to_nat(0u);
v___y_1562_ = v___x_1571_;
goto v___jp_1561_;
}
v___jp_1550_:
{
lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1554_ = lean_nat_add(v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec(v___y_1552_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 4, v_r_1524_);
lean_ctor_set(v___x_1546_, 3, v_r_1540_);
lean_ctor_set(v___x_1546_, 2, v_v_1522_);
lean_ctor_set(v___x_1546_, 1, v_k_1521_);
lean_ctor_set(v___x_1546_, 0, v___x_1554_);
v___x_1556_ = v___x_1546_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_k_1521_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_v_1522_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v_r_1540_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v_r_1524_);
v___x_1556_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1558_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 4, v___x_1556_);
lean_ctor_set(v___x_1534_, 3, v___y_1551_);
lean_ctor_set(v___x_1534_, 2, v_v_1538_);
lean_ctor_set(v___x_1534_, 1, v_k_1537_);
lean_ctor_set(v___x_1534_, 0, v___x_1549_);
v___x_1558_ = v___x_1534_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1537_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1538_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v___y_1551_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
v___jp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_nat_add(v___x_1548_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec(v___x_1548_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v_l_1539_);
lean_ctor_set(v___x_1373_, 0, v___x_1563_);
v___x_1565_ = v___x_1373_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v_l_1370_);
lean_ctor_set(v_reuseFailAlloc_1569_, 4, v_l_1539_);
v___x_1565_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_nat_add(v___x_1518_, v_size_1541_);
if (lean_obj_tag(v_r_1540_) == 0)
{
lean_object* v_size_1567_; 
v_size_1567_ = lean_ctor_get(v_r_1540_, 0);
lean_inc(v_size_1567_);
v___y_1551_ = v___x_1565_;
v___y_1552_ = v___x_1566_;
v___y_1553_ = v_size_1567_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___y_1551_ = v___x_1565_;
v___y_1552_ = v___x_1566_;
v___y_1553_ = v___x_1568_;
goto v___jp_1550_;
}
}
}
}
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
lean_del_object(v___x_1373_);
v___x_1578_ = lean_nat_add(v___x_1518_, v_size_1519_);
v___x_1579_ = lean_nat_add(v___x_1578_, v_size_1520_);
lean_dec(v_size_1520_);
v___x_1580_ = lean_nat_add(v___x_1578_, v_size_1536_);
lean_dec(v___x_1578_);
lean_inc_ref(v_l_1370_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 4, v_l_1523_);
lean_ctor_set(v___x_1534_, 3, v_l_1370_);
lean_ctor_set(v___x_1534_, 2, v_v_1369_);
lean_ctor_set(v___x_1534_, 1, v_k_1368_);
lean_ctor_set(v___x_1534_, 0, v___x_1580_);
v___x_1582_ = v___x_1534_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_l_1370_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_l_1523_);
v___x_1582_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_isSharedCheck_1589_ = !lean_is_exclusive(v_l_1370_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; lean_object* v_unused_1594_; 
v_unused_1590_ = lean_ctor_get(v_l_1370_, 4);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_l_1370_, 3);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_l_1370_, 2);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_l_1370_, 1);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_l_1370_, 0);
lean_dec(v_unused_1594_);
v___x_1584_ = v_l_1370_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v_l_1370_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 4, v_r_1524_);
lean_ctor_set(v___x_1584_, 3, v___x_1582_);
lean_ctor_set(v___x_1584_, 2, v_v_1522_);
lean_ctor_set(v___x_1584_, 1, v_k_1521_);
lean_ctor_set(v___x_1584_, 0, v___x_1579_);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_k_1521_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_v_1522_);
lean_ctor_set(v_reuseFailAlloc_1588_, 3, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1588_, 4, v_r_1524_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1602_; 
v_l_1602_ = lean_ctor_get(v_impl_1517_, 3);
lean_inc(v_l_1602_);
if (lean_obj_tag(v_l_1602_) == 0)
{
lean_object* v_r_1603_; lean_object* v_k_1604_; lean_object* v_v_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1628_; 
v_r_1603_ = lean_ctor_get(v_impl_1517_, 4);
v_k_1604_ = lean_ctor_get(v_impl_1517_, 1);
v_v_1605_ = lean_ctor_get(v_impl_1517_, 2);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_impl_1517_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; lean_object* v_unused_1630_; 
v_unused_1629_ = lean_ctor_get(v_impl_1517_, 3);
lean_dec(v_unused_1629_);
v_unused_1630_ = lean_ctor_get(v_impl_1517_, 0);
lean_dec(v_unused_1630_);
v___x_1607_ = v_impl_1517_;
v_isShared_1608_ = v_isSharedCheck_1628_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_r_1603_);
lean_inc(v_v_1605_);
lean_inc(v_k_1604_);
lean_dec(v_impl_1517_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1628_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_k_1609_; lean_object* v_v_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1624_; 
v_k_1609_ = lean_ctor_get(v_l_1602_, 1);
v_v_1610_ = lean_ctor_get(v_l_1602_, 2);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_l_1602_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; lean_object* v_unused_1626_; lean_object* v_unused_1627_; 
v_unused_1625_ = lean_ctor_get(v_l_1602_, 4);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_l_1602_, 3);
lean_dec(v_unused_1626_);
v_unused_1627_ = lean_ctor_get(v_l_1602_, 0);
lean_dec(v_unused_1627_);
v___x_1612_ = v_l_1602_;
v_isShared_1613_ = v_isSharedCheck_1624_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_v_1610_);
lean_inc(v_k_1609_);
lean_dec(v_l_1602_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1624_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1614_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1603_, 2);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 4, v_r_1603_);
lean_ctor_set(v___x_1612_, 3, v_r_1603_);
lean_ctor_set(v___x_1612_, 2, v_v_1369_);
lean_ctor_set(v___x_1612_, 1, v_k_1368_);
lean_ctor_set(v___x_1612_, 0, v___x_1518_);
v___x_1616_ = v___x_1612_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_r_1603_);
lean_ctor_set(v_reuseFailAlloc_1623_, 4, v_r_1603_);
v___x_1616_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1618_; 
lean_inc(v_r_1603_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 3, v_r_1603_);
lean_ctor_set(v___x_1607_, 0, v___x_1518_);
v___x_1618_ = v___x_1607_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_k_1604_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_v_1605_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v_r_1603_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v_r_1603_);
v___x_1618_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1620_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v___x_1618_);
lean_ctor_set(v___x_1373_, 3, v___x_1616_);
lean_ctor_set(v___x_1373_, 2, v_v_1610_);
lean_ctor_set(v___x_1373_, 1, v_k_1609_);
lean_ctor_set(v___x_1373_, 0, v___x_1614_);
v___x_1620_ = v___x_1373_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_k_1609_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_v_1610_);
lean_ctor_set(v_reuseFailAlloc_1621_, 3, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1621_, 4, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
else
{
lean_object* v_r_1631_; 
v_r_1631_ = lean_ctor_get(v_impl_1517_, 4);
lean_inc(v_r_1631_);
if (lean_obj_tag(v_r_1631_) == 0)
{
lean_object* v_k_1632_; lean_object* v_v_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1644_; 
v_k_1632_ = lean_ctor_get(v_impl_1517_, 1);
v_v_1633_ = lean_ctor_get(v_impl_1517_, 2);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_impl_1517_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; lean_object* v_unused_1646_; lean_object* v_unused_1647_; 
v_unused_1645_ = lean_ctor_get(v_impl_1517_, 4);
lean_dec(v_unused_1645_);
v_unused_1646_ = lean_ctor_get(v_impl_1517_, 3);
lean_dec(v_unused_1646_);
v_unused_1647_ = lean_ctor_get(v_impl_1517_, 0);
lean_dec(v_unused_1647_);
v___x_1635_ = v_impl_1517_;
v_isShared_1636_ = v_isSharedCheck_1644_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_v_1633_);
lean_inc(v_k_1632_);
lean_dec(v_impl_1517_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1644_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1637_ = lean_unsigned_to_nat(3u);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 4, v_l_1602_);
lean_ctor_set(v___x_1635_, 2, v_v_1369_);
lean_ctor_set(v___x_1635_, 1, v_k_1368_);
lean_ctor_set(v___x_1635_, 0, v___x_1518_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_l_1602_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v_l_1602_);
v___x_1639_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1641_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v_r_1631_);
lean_ctor_set(v___x_1373_, 3, v___x_1639_);
lean_ctor_set(v___x_1373_, 2, v_v_1633_);
lean_ctor_set(v___x_1373_, 1, v_k_1632_);
lean_ctor_set(v___x_1373_, 0, v___x_1637_);
v___x_1641_ = v___x_1373_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_k_1632_);
lean_ctor_set(v_reuseFailAlloc_1642_, 2, v_v_1633_);
lean_ctor_set(v_reuseFailAlloc_1642_, 3, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1642_, 4, v_r_1631_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = lean_unsigned_to_nat(2u);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v_impl_1517_);
lean_ctor_set(v___x_1373_, 3, v_r_1631_);
lean_ctor_set(v___x_1373_, 0, v___x_1648_);
v___x_1650_ = v___x_1373_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v_r_1631_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v_impl_1517_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
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
lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec_ref(v_cmp_1363_);
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v_k_1364_);
lean_ctor_set(v___x_1654_, 2, v_v_1365_);
lean_ctor_set(v___x_1654_, 3, v_t_1366_);
lean_ctor_set(v___x_1654_, 4, v_t_1366_);
return v___x_1654_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(lean_object* v_cmp_1655_, lean_object* v_k_1656_, lean_object* v_t_1657_){
_start:
{
if (lean_obj_tag(v_t_1657_) == 0)
{
lean_object* v_k_1658_; lean_object* v_l_1659_; lean_object* v_r_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_k_1658_ = lean_ctor_get(v_t_1657_, 1);
lean_inc(v_k_1658_);
v_l_1659_ = lean_ctor_get(v_t_1657_, 3);
lean_inc(v_l_1659_);
v_r_1660_ = lean_ctor_get(v_t_1657_, 4);
lean_inc(v_r_1660_);
lean_dec_ref_known(v_t_1657_, 5);
lean_inc_ref(v_cmp_1655_);
lean_inc(v_k_1656_);
v___x_1661_ = lean_apply_2(v_cmp_1655_, v_k_1656_, v_k_1658_);
v___x_1662_ = lean_unbox(v___x_1661_);
switch(v___x_1662_)
{
case 0:
{
lean_dec(v_r_1660_);
v_t_1657_ = v_l_1659_;
goto _start;
}
case 1:
{
uint8_t v___x_1664_; 
lean_dec(v_r_1660_);
lean_dec(v_l_1659_);
lean_dec(v_k_1656_);
lean_dec_ref(v_cmp_1655_);
v___x_1664_ = 1;
return v___x_1664_;
}
default: 
{
lean_dec(v_l_1659_);
v_t_1657_ = v_r_1660_;
goto _start;
}
}
}
else
{
uint8_t v___x_1666_; 
lean_dec(v_k_1656_);
lean_dec_ref(v_cmp_1655_);
v___x_1666_ = 0;
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg___boxed(lean_object* v_cmp_1667_, lean_object* v_k_1668_, lean_object* v_t_1669_){
_start:
{
uint8_t v_res_1670_; lean_object* v_r_1671_; 
v_res_1670_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1667_, v_k_1668_, v_t_1669_);
v_r_1671_ = lean_box(v_res_1670_);
return v_r_1671_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(lean_object* v_cmp_1672_, lean_object* v_as_x27_1673_, lean_object* v_b_1674_){
_start:
{
if (lean_obj_tag(v_as_x27_1673_) == 0)
{
lean_dec_ref(v_cmp_1672_);
return v_b_1674_;
}
else
{
lean_object* v_head_1675_; lean_object* v_tail_1676_; uint8_t v___x_1677_; 
v_head_1675_ = lean_ctor_get(v_as_x27_1673_, 0);
v_tail_1676_ = lean_ctor_get(v_as_x27_1673_, 1);
lean_inc(v_b_1674_);
lean_inc(v_head_1675_);
lean_inc_ref(v_cmp_1672_);
v___x_1677_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1672_, v_head_1675_, v_b_1674_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_box(0);
lean_inc(v_head_1675_);
lean_inc_ref(v_cmp_1672_);
v___x_1679_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1672_, v_head_1675_, v___x_1678_, v_b_1674_);
v_as_x27_1673_ = v_tail_1676_;
v_b_1674_ = v___x_1679_;
goto _start;
}
else
{
v_as_x27_1673_ = v_tail_1676_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg___boxed(lean_object* v_cmp_1682_, lean_object* v_as_x27_1683_, lean_object* v_b_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1682_, v_as_x27_1683_, v_b_1684_);
lean_dec(v_as_x27_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___redArg(lean_object* v_l_1686_, lean_object* v_cmp_1687_){
_start:
{
lean_object* v_r_1688_; lean_object* v___x_1689_; 
v_r_1688_ = lean_box(1);
v___x_1689_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1687_, v_l_1686_, v_r_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___redArg___boxed(lean_object* v_l_1690_, lean_object* v_cmp_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_TreeSet_ofList___redArg(v_l_1690_, v_cmp_1691_);
lean_dec(v_l_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList(lean_object* v_00_u03b1_1693_, lean_object* v_l_1694_, lean_object* v_cmp_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Std_TreeSet_ofList___redArg(v_l_1694_, v_cmp_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___boxed(lean_object* v_00_u03b1_1697_, lean_object* v_l_1698_, lean_object* v_cmp_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_TreeSet_ofList(v_00_u03b1_1697_, v_l_1698_, v_cmp_1699_);
lean_dec(v_l_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(lean_object* v_00_u03b1_1701_, lean_object* v_cmp_1702_, lean_object* v_00_u03b2_1703_, lean_object* v_k_1704_, lean_object* v_t_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1702_, v_k_1704_, v_t_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___boxed(lean_object* v_00_u03b1_1707_, lean_object* v_cmp_1708_, lean_object* v_00_u03b2_1709_, lean_object* v_k_1710_, lean_object* v_t_1711_){
_start:
{
uint8_t v_res_1712_; lean_object* v_r_1713_; 
v_res_1712_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(v_00_u03b1_1707_, v_cmp_1708_, v_00_u03b2_1709_, v_k_1710_, v_t_1711_);
v_r_1713_ = lean_box(v_res_1712_);
return v_r_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1(lean_object* v_00_u03b1_1714_, lean_object* v_cmp_1715_, lean_object* v_00_u03b2_1716_, lean_object* v_k_1717_, lean_object* v_v_1718_, lean_object* v_t_1719_, lean_object* v_hl_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1715_, v_k_1717_, v_v_1718_, v_t_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(lean_object* v_00_u03b1_1722_, lean_object* v_cmp_1723_, lean_object* v_as_1724_, lean_object* v_as_x27_1725_, lean_object* v_b_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1723_, v_as_x27_1725_, v_b_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_cmp_1730_, lean_object* v_as_1731_, lean_object* v_as_x27_1732_, lean_object* v_b_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(v_00_u03b1_1729_, v_cmp_1730_, v_as_1731_, v_as_x27_1732_, v_b_1733_, v_a_1734_);
lean_dec(v_as_x27_1732_);
lean_dec(v_as_1731_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg___lam__0(lean_object* v_l_1736_, lean_object* v_k_1737_, lean_object* v_x_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_array_push(v_l_1736_, v_k_1737_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg(lean_object* v_t_1741_){
_start:
{
lean_object* v___f_1742_; lean_object* v___y_1744_; 
v___f_1742_ = ((lean_object*)(l_Std_TreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1741_) == 0)
{
lean_object* v_size_1747_; 
v_size_1747_ = lean_ctor_get(v_t_1741_, 0);
lean_inc(v_size_1747_);
v___y_1744_ = v_size_1747_;
goto v___jp_1743_;
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_unsigned_to_nat(0u);
v___y_1744_ = v___x_1748_;
goto v___jp_1743_;
}
v___jp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_mk_empty_array_with_capacity(v___y_1744_);
lean_dec(v___y_1744_);
v___x_1746_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1742_, v___x_1745_, v_t_1741_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray(lean_object* v_00_u03b1_1749_, lean_object* v_cmp_1750_, lean_object* v_t_1751_){
_start:
{
lean_object* v___f_1752_; lean_object* v___y_1754_; 
v___f_1752_ = ((lean_object*)(l_Std_TreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1751_) == 0)
{
lean_object* v_size_1757_; 
v_size_1757_ = lean_ctor_get(v_t_1751_, 0);
lean_inc(v_size_1757_);
v___y_1754_ = v_size_1757_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_unsigned_to_nat(0u);
v___y_1754_ = v___x_1758_;
goto v___jp_1753_;
}
v___jp_1753_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_mk_empty_array_with_capacity(v___y_1754_);
lean_dec(v___y_1754_);
v___x_1756_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1752_, v___x_1755_, v_t_1751_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___boxed(lean_object* v_00_u03b1_1759_, lean_object* v_cmp_1760_, lean_object* v_t_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Std_TreeSet_toArray(v_00_u03b1_1759_, v_cmp_1760_, v_t_1761_);
lean_dec_ref(v_cmp_1760_);
return v_res_1762_;
}
}
static lean_object* _init_l_Std_TreeSet_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__26, &l_Std_TreeSet___auto__1___closed__26_once, _init_l_Std_TreeSet___auto__1___closed__26);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(lean_object* v_cmp_1764_, lean_object* v_as_1765_, size_t v_sz_1766_, size_t v_i_1767_, lean_object* v_b_1768_){
_start:
{
lean_object* v___y_1770_; uint8_t v___x_1774_; 
v___x_1774_ = lean_usize_dec_lt(v_i_1767_, v_sz_1766_);
if (v___x_1774_ == 0)
{
lean_dec_ref(v_cmp_1764_);
return v_b_1768_;
}
else
{
lean_object* v_a_1775_; uint8_t v___x_1776_; 
v_a_1775_ = lean_array_uget_borrowed(v_as_1765_, v_i_1767_);
lean_inc(v_b_1768_);
lean_inc(v_a_1775_);
lean_inc_ref(v_cmp_1764_);
v___x_1776_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1764_, v_a_1775_, v_b_1768_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_box(0);
lean_inc(v_a_1775_);
lean_inc_ref(v_cmp_1764_);
v___x_1778_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1764_, v_a_1775_, v___x_1777_, v_b_1768_);
v___y_1770_ = v___x_1778_;
goto v___jp_1769_;
}
else
{
v___y_1770_ = v_b_1768_;
goto v___jp_1769_;
}
}
v___jp_1769_:
{
size_t v___x_1771_; size_t v___x_1772_; 
v___x_1771_ = ((size_t)1ULL);
v___x_1772_ = lean_usize_add(v_i_1767_, v___x_1771_);
v_i_1767_ = v___x_1772_;
v_b_1768_ = v___y_1770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg___boxed(lean_object* v_cmp_1779_, lean_object* v_as_1780_, lean_object* v_sz_1781_, lean_object* v_i_1782_, lean_object* v_b_1783_){
_start:
{
size_t v_sz_boxed_1784_; size_t v_i_boxed_1785_; lean_object* v_res_1786_; 
v_sz_boxed_1784_ = lean_unbox_usize(v_sz_1781_);
lean_dec(v_sz_1781_);
v_i_boxed_1785_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_res_1786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1779_, v_as_1780_, v_sz_boxed_1784_, v_i_boxed_1785_, v_b_1783_);
lean_dec_ref(v_as_1780_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg(lean_object* v_a_1787_, lean_object* v_cmp_1788_){
_start:
{
lean_object* v_r_1789_; size_t v_sz_1790_; size_t v___x_1791_; lean_object* v___x_1792_; 
v_r_1789_ = lean_box(1);
v_sz_1790_ = lean_array_size(v_a_1787_);
v___x_1791_ = ((size_t)0ULL);
v___x_1792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1788_, v_a_1787_, v_sz_1790_, v___x_1791_, v_r_1789_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg___boxed(lean_object* v_a_1793_, lean_object* v_cmp_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Std_TreeSet_ofArray___redArg(v_a_1793_, v_cmp_1794_);
lean_dec_ref(v_a_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray(lean_object* v_00_u03b1_1796_, lean_object* v_a_1797_, lean_object* v_cmp_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Std_TreeSet_ofArray___redArg(v_a_1797_, v_cmp_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___boxed(lean_object* v_00_u03b1_1800_, lean_object* v_a_1801_, lean_object* v_cmp_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Std_TreeSet_ofArray(v_00_u03b1_1800_, v_a_1801_, v_cmp_1802_);
lean_dec_ref(v_a_1801_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(lean_object* v_00_u03b1_1804_, lean_object* v_cmp_1805_, lean_object* v_as_1806_, size_t v_sz_1807_, size_t v_i_1808_, lean_object* v_b_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1805_, v_as_1806_, v_sz_1807_, v_i_1808_, v_b_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___boxed(lean_object* v_00_u03b1_1811_, lean_object* v_cmp_1812_, lean_object* v_as_1813_, lean_object* v_sz_1814_, lean_object* v_i_1815_, lean_object* v_b_1816_){
_start:
{
size_t v_sz_boxed_1817_; size_t v_i_boxed_1818_; lean_object* v_res_1819_; 
v_sz_boxed_1817_ = lean_unbox_usize(v_sz_1814_);
lean_dec(v_sz_1814_);
v_i_boxed_1818_ = lean_unbox_usize(v_i_1815_);
lean_dec(v_i_1815_);
v_res_1819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(v_00_u03b1_1811_, v_cmp_1812_, v_as_1813_, v_sz_boxed_1817_, v_i_boxed_1818_, v_b_1816_);
lean_dec_ref(v_as_1813_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0(lean_object* v_b_u2082_1822_, lean_object* v_x_1823_){
_start:
{
if (lean_obj_tag(v_x_1823_) == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_b_u2082_1822_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; 
v___x_1825_ = ((lean_object*)(l_Std_TreeSet_merge___redArg___lam__0___closed__0));
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Std_TreeSet_merge___redArg___lam__0(v_b_u2082_1826_, v_x_1827_);
lean_dec(v_x_1827_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__1(lean_object* v_cmp_1829_, lean_object* v_t_1830_, lean_object* v_a_1831_, lean_object* v_b_u2082_1832_){
_start:
{
lean_object* v___f_1833_; lean_object* v___x_1834_; 
v___f_1833_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1833_, 0, v_b_u2082_1832_);
v___x_1834_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_1829_, v_a_1831_, v___f_1833_, v_t_1830_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg(lean_object* v_cmp_1835_, lean_object* v_t_u2081_1836_, lean_object* v_t_u2082_1837_){
_start:
{
lean_object* v___f_1838_; lean_object* v___x_1839_; 
v___f_1838_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1838_, 0, v_cmp_1835_);
v___x_1839_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1838_, v_t_u2081_1836_, v_t_u2082_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge(lean_object* v_00_u03b1_1840_, lean_object* v_cmp_1841_, lean_object* v_t_u2081_1842_, lean_object* v_t_u2082_1843_){
_start:
{
lean_object* v___f_1844_; lean_object* v___x_1845_; 
v___f_1844_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1844_, 0, v_cmp_1841_);
v___x_1845_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1844_, v_t_u2081_1842_, v_t_u2082_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg___lam__0(lean_object* v_cmp_1846_, lean_object* v_a_1847_, lean_object* v_____s_1848_){
_start:
{
uint8_t v___x_1849_; 
lean_inc(v_____s_1848_);
lean_inc(v_a_1847_);
lean_inc_ref(v_cmp_1846_);
v___x_1849_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1846_, v_a_1847_, v_____s_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_box(0);
v___x_1851_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1846_, v_a_1847_, v___x_1850_, v_____s_1848_);
v___x_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
else
{
lean_object* v___x_1853_; 
lean_dec(v_a_1847_);
lean_dec_ref(v_cmp_1846_);
v___x_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_____s_1848_);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg(lean_object* v_cmp_1854_, lean_object* v_inst_1855_, lean_object* v_t_1856_, lean_object* v_l_1857_){
_start:
{
lean_object* v___f_1858_; lean_object* v___x_1859_; 
v___f_1858_ = lean_alloc_closure((void*)(l_Std_TreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1858_, 0, v_cmp_1854_);
v___x_1859_ = lean_apply_4(v_inst_1855_, lean_box(0), v_l_1857_, v_t_1856_, v___f_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany(lean_object* v_00_u03b1_1860_, lean_object* v_cmp_1861_, lean_object* v_00_u03c1_1862_, lean_object* v_inst_1863_, lean_object* v_t_1864_, lean_object* v_l_1865_){
_start:
{
lean_object* v___f_1866_; lean_object* v___x_1867_; 
v___f_1866_ = lean_alloc_closure((void*)(l_Std_TreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1866_, 0, v_cmp_1861_);
v___x_1867_ = lean_apply_4(v_inst_1863_, lean_box(0), v_l_1865_, v_t_1864_, v___f_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_union___redArg(lean_object* v_cmp_1868_, lean_object* v_t_u2081_1869_, lean_object* v_t_u2082_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1868_, v_t_u2081_1869_, v_t_u2082_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_union(lean_object* v_00_u03b1_1872_, lean_object* v_cmp_1873_, lean_object* v_t_u2081_1874_, lean_object* v_t_u2082_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1873_, v_t_u2081_1874_, v_t_u2082_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion___redArg(lean_object* v_cmp_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_closure((void*)(l_Std_TreeSet_union), 4, 2);
lean_closure_set(v___x_1878_, 0, lean_box(0));
lean_closure_set(v___x_1878_, 1, v_cmp_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion(lean_object* v_00_u03b1_1879_, lean_object* v_cmp_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_closure((void*)(l_Std_TreeSet_union), 4, 2);
lean_closure_set(v___x_1881_, 0, lean_box(0));
lean_closure_set(v___x_1881_, 1, v_cmp_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_inter___redArg(lean_object* v_cmp_1882_, lean_object* v_t_u2081_1883_, lean_object* v_t_u2082_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1882_, v_t_u2081_1883_, v_t_u2082_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_inter(lean_object* v_00_u03b1_1886_, lean_object* v_cmp_1887_, lean_object* v_t_u2081_1888_, lean_object* v_t_u2082_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1887_, v_t_u2081_1888_, v_t_u2082_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter___redArg(lean_object* v_cmp_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_alloc_closure((void*)(l_Std_TreeSet_inter), 4, 2);
lean_closure_set(v___x_1892_, 0, lean_box(0));
lean_closure_set(v___x_1892_, 1, v_cmp_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter(lean_object* v_00_u03b1_1893_, lean_object* v_cmp_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_alloc_closure((void*)(l_Std_TreeSet_inter), 4, 2);
lean_closure_set(v___x_1895_, 0, lean_box(0));
lean_closure_set(v___x_1895_, 1, v_cmp_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_cmp_1896_, lean_object* v_t_1897_, lean_object* v_k_1898_){
_start:
{
if (lean_obj_tag(v_t_1897_) == 0)
{
lean_object* v_k_1899_; lean_object* v_v_1900_; lean_object* v_l_1901_; lean_object* v_r_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v_k_1899_ = lean_ctor_get(v_t_1897_, 1);
lean_inc(v_k_1899_);
v_v_1900_ = lean_ctor_get(v_t_1897_, 2);
lean_inc(v_v_1900_);
v_l_1901_ = lean_ctor_get(v_t_1897_, 3);
lean_inc(v_l_1901_);
v_r_1902_ = lean_ctor_get(v_t_1897_, 4);
lean_inc(v_r_1902_);
lean_dec_ref_known(v_t_1897_, 5);
lean_inc_ref(v_cmp_1896_);
lean_inc(v_k_1898_);
v___x_1903_ = lean_apply_2(v_cmp_1896_, v_k_1898_, v_k_1899_);
v___x_1904_ = lean_unbox(v___x_1903_);
switch(v___x_1904_)
{
case 0:
{
lean_dec(v_r_1902_);
lean_dec(v_v_1900_);
v_t_1897_ = v_l_1901_;
goto _start;
}
case 1:
{
lean_object* v___x_1906_; 
lean_dec(v_r_1902_);
lean_dec(v_l_1901_);
lean_dec(v_k_1898_);
lean_dec_ref(v_cmp_1896_);
v___x_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_v_1900_);
return v___x_1906_;
}
default: 
{
lean_dec(v_l_1901_);
lean_dec(v_v_1900_);
v_t_1897_ = v_r_1902_;
goto _start;
}
}
}
else
{
lean_object* v___x_1908_; 
lean_dec(v_k_1898_);
lean_dec_ref(v_cmp_1896_);
v___x_1908_ = lean_box(0);
return v___x_1908_;
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1909_, lean_object* v_x_1910_){
_start:
{
if (lean_obj_tag(v_x_1909_) == 0)
{
if (lean_obj_tag(v_x_1910_) == 0)
{
uint8_t v___x_1911_; 
v___x_1911_ = 1;
return v___x_1911_;
}
else
{
uint8_t v___x_1912_; 
v___x_1912_ = 0;
return v___x_1912_;
}
}
else
{
if (lean_obj_tag(v_x_1910_) == 0)
{
uint8_t v___x_1913_; 
v___x_1913_ = 0;
return v___x_1913_;
}
else
{
uint8_t v___x_1914_; 
v___x_1914_ = 1;
return v___x_1914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1915_, lean_object* v_x_1916_){
_start:
{
uint8_t v_res_1917_; lean_object* v_r_1918_; 
v_res_1917_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v_x_1915_, v_x_1916_);
lean_dec(v_x_1916_);
lean_dec(v_x_1915_);
v_r_1918_ = lean_box(v_res_1917_);
return v_r_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v_cmp_1921_, lean_object* v_t_u2082_1922_, lean_object* v_init_1923_, lean_object* v_x_1924_){
_start:
{
lean_object* v___x_1925_; uint8_t v___y_1927_; lean_object* v___x_1932_; uint8_t v___y_1934_; uint8_t v___x_1952_; 
v___x_1925_ = lean_box(0);
v___x_1932_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___x_1952_ = lean_nat_dec_eq(v___y_1919_, v___y_1920_);
if (v___x_1952_ == 0)
{
uint8_t v___x_1953_; 
v___x_1953_ = 1;
v___y_1934_ = v___x_1953_;
goto v___jp_1933_;
}
else
{
uint8_t v___x_1954_; 
v___x_1954_ = 0;
v___y_1934_ = v___x_1954_;
goto v___jp_1933_;
}
v___jp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1928_ = lean_box(v___y_1927_);
v___x_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
lean_ctor_set(v___x_1930_, 1, v___x_1925_);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
return v___x_1931_;
}
v___jp_1933_:
{
if (lean_obj_tag(v_x_1924_) == 0)
{
lean_object* v_k_1935_; lean_object* v_v_1936_; lean_object* v_l_1937_; lean_object* v_r_1938_; lean_object* v___x_1939_; 
v_k_1935_ = lean_ctor_get(v_x_1924_, 1);
lean_inc(v_k_1935_);
v_v_1936_ = lean_ctor_get(v_x_1924_, 2);
lean_inc(v_v_1936_);
v_l_1937_ = lean_ctor_get(v_x_1924_, 3);
lean_inc(v_l_1937_);
v_r_1938_ = lean_ctor_get(v_x_1924_, 4);
lean_inc(v_r_1938_);
lean_dec_ref_known(v_x_1924_, 5);
lean_inc(v_t_u2082_1922_);
lean_inc_ref(v_cmp_1921_);
v___x_1939_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1919_, v___y_1920_, v_cmp_1921_, v_t_u2082_1922_, v_init_1923_, v_l_1937_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_dec(v_r_1938_);
lean_dec(v_v_1936_);
lean_dec(v_k_1935_);
lean_dec(v_t_u2082_1922_);
lean_dec_ref(v_cmp_1921_);
return v___x_1939_;
}
else
{
lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1949_; 
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v___x_1939_, 0);
lean_dec(v_unused_1950_);
v___x_1941_ = v___x_1939_;
v_isShared_1942_ = v_isSharedCheck_1949_;
goto v_resetjp_1940_;
}
else
{
lean_dec(v___x_1939_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1949_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
lean_inc(v_t_u2082_1922_);
lean_inc_ref(v_cmp_1921_);
v___x_1943_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1921_, v_t_u2082_1922_, v_k_1935_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v_v_1936_);
v___x_1945_ = v___x_1941_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_v_1936_);
v___x_1945_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
uint8_t v___x_1946_; 
v___x_1946_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v___x_1943_, v___x_1945_);
lean_dec_ref(v___x_1945_);
lean_dec(v___x_1943_);
if (v___x_1946_ == 0)
{
lean_dec(v_r_1938_);
lean_dec(v_t_u2082_1922_);
lean_dec_ref(v_cmp_1921_);
v___y_1927_ = v___y_1934_;
goto v___jp_1926_;
}
else
{
if (v___y_1934_ == 0)
{
v_init_1923_ = v___x_1932_;
v_x_1924_ = v_r_1938_;
goto _start;
}
else
{
lean_dec(v_r_1938_);
lean_dec(v_t_u2082_1922_);
lean_dec_ref(v_cmp_1921_);
v___y_1927_ = v___y_1934_;
goto v___jp_1926_;
}
}
}
}
}
}
else
{
lean_object* v___x_1951_; 
lean_dec(v_t_u2082_1922_);
lean_dec_ref(v_cmp_1921_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_init_1923_);
return v___x_1951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v_cmp_1957_, lean_object* v_t_u2082_1958_, lean_object* v_init_1959_, lean_object* v_x_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1955_, v___y_1956_, v_cmp_1957_, v_t_u2082_1958_, v_init_1959_, v_x_1960_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
return v_res_1961_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_1962_, lean_object* v_t_u2081_1963_, lean_object* v_t_u2082_1964_){
_start:
{
lean_object* v___y_1966_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1979_; 
if (lean_obj_tag(v_t_u2081_1963_) == 0)
{
lean_object* v_size_1982_; 
v_size_1982_ = lean_ctor_get(v_t_u2081_1963_, 0);
lean_inc(v_size_1982_);
v___y_1979_ = v_size_1982_;
goto v___jp_1978_;
}
else
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_unsigned_to_nat(0u);
v___y_1979_ = v___x_1983_;
goto v___jp_1978_;
}
v___jp_1965_:
{
lean_object* v_fst_1967_; 
v_fst_1967_ = lean_ctor_get(v___y_1966_, 0);
lean_inc(v_fst_1967_);
lean_dec_ref(v___y_1966_);
if (lean_obj_tag(v_fst_1967_) == 0)
{
uint8_t v___x_1968_; 
v___x_1968_ = 1;
return v___x_1968_;
}
else
{
lean_object* v_val_1969_; uint8_t v___x_1970_; 
v_val_1969_ = lean_ctor_get(v_fst_1967_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v_fst_1967_, 1);
v___x_1970_ = lean_unbox(v_val_1969_);
lean_dec(v_val_1969_);
return v___x_1970_;
}
}
v___jp_1971_:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_nat_dec_eq(v___y_1972_, v___y_1973_);
if (v___x_1974_ == 0)
{
lean_dec(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec(v_t_u2082_1964_);
lean_dec(v_t_u2081_1963_);
lean_dec_ref(v_cmp_1962_);
return v___x_1974_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v_a_1977_; 
v___x_1975_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___x_1976_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1972_, v___y_1973_, v_cmp_1962_, v_t_u2082_1964_, v___x_1975_, v_t_u2081_1963_);
lean_dec(v___y_1973_);
lean_dec(v___y_1972_);
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref(v___x_1976_);
v___y_1966_ = v_a_1977_;
goto v___jp_1965_;
}
}
v___jp_1978_:
{
if (lean_obj_tag(v_t_u2082_1964_) == 0)
{
lean_object* v_size_1980_; 
v_size_1980_ = lean_ctor_get(v_t_u2082_1964_, 0);
lean_inc(v_size_1980_);
v___y_1972_ = v___y_1979_;
v___y_1973_ = v_size_1980_;
goto v___jp_1971_;
}
else
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___y_1972_ = v___y_1979_;
v___y_1973_ = v___x_1981_;
goto v___jp_1971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_1984_, lean_object* v_t_u2081_1985_, lean_object* v_t_u2082_1986_){
_start:
{
uint8_t v_res_1987_; lean_object* v_r_1988_; 
v_res_1987_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1984_, v_t_u2081_1985_, v_t_u2082_1986_);
v_r_1988_ = lean_box(v_res_1987_);
return v_r_1988_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_beq___redArg(lean_object* v_cmp_1989_, lean_object* v_t_u2081_1990_, lean_object* v_t_u2082_1991_){
_start:
{
uint8_t v___x_1992_; 
v___x_1992_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1989_, v_t_u2081_1990_, v_t_u2082_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___redArg___boxed(lean_object* v_cmp_1993_, lean_object* v_t_u2081_1994_, lean_object* v_t_u2082_1995_){
_start:
{
uint8_t v_res_1996_; lean_object* v_r_1997_; 
v_res_1996_ = l_Std_TreeSet_beq___redArg(v_cmp_1993_, v_t_u2081_1994_, v_t_u2082_1995_);
v_r_1997_ = lean_box(v_res_1996_);
return v_r_1997_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_beq(lean_object* v_00_u03b1_1998_, lean_object* v_cmp_1999_, lean_object* v_t_u2081_2000_, lean_object* v_t_u2082_2001_){
_start:
{
uint8_t v___x_2002_; 
v___x_2002_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1999_, v_t_u2081_2000_, v_t_u2082_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___boxed(lean_object* v_00_u03b1_2003_, lean_object* v_cmp_2004_, lean_object* v_t_u2081_2005_, lean_object* v_t_u2082_2006_){
_start:
{
uint8_t v_res_2007_; lean_object* v_r_2008_; 
v_res_2007_ = l_Std_TreeSet_beq(v_00_u03b1_2003_, v_cmp_2004_, v_t_u2081_2005_, v_t_u2082_2006_);
v_r_2008_ = lean_box(v_res_2007_);
return v_r_2008_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(lean_object* v_cmp_2009_, lean_object* v_t_u2081_2010_, lean_object* v_t_u2082_2011_){
_start:
{
uint8_t v___x_2012_; 
v___x_2012_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2009_, v_t_u2081_2010_, v_t_u2082_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg___boxed(lean_object* v_cmp_2013_, lean_object* v_t_u2081_2014_, lean_object* v_t_u2082_2015_){
_start:
{
uint8_t v_res_2016_; lean_object* v_r_2017_; 
v_res_2016_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(v_cmp_2013_, v_t_u2081_2014_, v_t_u2082_2015_);
v_r_2017_ = lean_box(v_res_2016_);
return v_r_2017_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(lean_object* v_00_u03b1_2018_, lean_object* v_cmp_2019_, lean_object* v_t_u2081_2020_, lean_object* v_t_u2082_2021_){
_start:
{
uint8_t v___x_2022_; 
v___x_2022_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2019_, v_t_u2081_2020_, v_t_u2082_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___boxed(lean_object* v_00_u03b1_2023_, lean_object* v_cmp_2024_, lean_object* v_t_u2081_2025_, lean_object* v_t_u2082_2026_){
_start:
{
uint8_t v_res_2027_; lean_object* v_r_2028_; 
v_res_2027_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(v_00_u03b1_2023_, v_cmp_2024_, v_t_u2081_2025_, v_t_u2082_2026_);
v_r_2028_ = lean_box(v_res_2027_);
return v_r_2028_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(lean_object* v_cmp_2029_, lean_object* v_t_u2081_2030_, lean_object* v_t_u2082_2031_){
_start:
{
uint8_t v___x_2032_; 
v___x_2032_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2029_, v_t_u2081_2030_, v_t_u2082_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_2033_, lean_object* v_t_u2081_2034_, lean_object* v_t_u2082_2035_){
_start:
{
uint8_t v_res_2036_; lean_object* v_r_2037_; 
v_res_2036_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(v_cmp_2033_, v_t_u2081_2034_, v_t_u2082_2035_);
v_r_2037_ = lean_box(v_res_2036_);
return v_r_2037_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(lean_object* v_00_u03b1_2038_, lean_object* v_cmp_2039_, lean_object* v_t_u2081_2040_, lean_object* v_t_u2082_2041_){
_start:
{
uint8_t v___x_2042_; 
v___x_2042_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2039_, v_t_u2081_2040_, v_t_u2082_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2043_, lean_object* v_cmp_2044_, lean_object* v_t_u2081_2045_, lean_object* v_t_u2082_2046_){
_start:
{
uint8_t v_res_2047_; lean_object* v_r_2048_; 
v_res_2047_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(v_00_u03b1_2043_, v_cmp_2044_, v_t_u2081_2045_, v_t_u2082_2046_);
v_r_2048_ = lean_box(v_res_2047_);
return v_r_2048_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2049_, lean_object* v_cmp_2050_, lean_object* v_t_u2081_2051_, lean_object* v_t_u2082_2052_){
_start:
{
uint8_t v___x_2053_; 
v___x_2053_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2050_, v_t_u2081_2051_, v_t_u2082_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2054_, lean_object* v_cmp_2055_, lean_object* v_t_u2081_2056_, lean_object* v_t_u2082_2057_){
_start:
{
uint8_t v_res_2058_; lean_object* v_r_2059_; 
v_res_2058_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(v_00_u03b1_2054_, v_cmp_2055_, v_t_u2081_2056_, v_t_u2082_2057_);
v_r_2059_ = lean_box(v_res_2058_);
return v_r_2059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2060_, lean_object* v_cmp_2061_, lean_object* v_00_u03b4_2062_, lean_object* v_t_2063_, lean_object* v_k_2064_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_2061_, v_t_2063_, v_k_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v_cmp_2069_, lean_object* v_t_u2082_2070_, lean_object* v_init_2071_, lean_object* v_x_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_2067_, v___y_2068_, v_cmp_2069_, v_t_u2082_2070_, v_init_2071_, v_x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v_cmp_2077_, lean_object* v_t_u2082_2078_, lean_object* v_init_2079_, lean_object* v_x_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2074_, v___y_2075_, v___y_2076_, v_cmp_2077_, v_t_u2082_2078_, v_init_2079_, v_x_2080_);
lean_dec(v___y_2076_);
lean_dec(v___y_2075_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq___redArg(lean_object* v_cmp_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_alloc_closure((void*)(l_Std_TreeSet_beq___boxed), 4, 2);
lean_closure_set(v___x_2083_, 0, lean_box(0));
lean_closure_set(v___x_2083_, 1, v_cmp_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq(lean_object* v_00_u03b1_2084_, lean_object* v_cmp_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_alloc_closure((void*)(l_Std_TreeSet_beq___boxed), 4, 2);
lean_closure_set(v___x_2086_, 0, lean_box(0));
lean_closure_set(v___x_2086_, 1, v_cmp_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_diff___redArg(lean_object* v_cmp_2087_, lean_object* v_t_u2081_2088_, lean_object* v_t_u2082_2089_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2087_, v_t_u2081_2088_, v_t_u2082_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_diff(lean_object* v_00_u03b1_2091_, lean_object* v_cmp_2092_, lean_object* v_t_u2081_2093_, lean_object* v_t_u2082_2094_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2092_, v_t_u2081_2093_, v_t_u2082_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff___redArg(lean_object* v_cmp_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = lean_alloc_closure((void*)(l_Std_TreeSet_diff), 4, 2);
lean_closure_set(v___x_2097_, 0, lean_box(0));
lean_closure_set(v___x_2097_, 1, v_cmp_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff(lean_object* v_00_u03b1_2098_, lean_object* v_cmp_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_alloc_closure((void*)(l_Std_TreeSet_diff), 4, 2);
lean_closure_set(v___x_2100_, 0, lean_box(0));
lean_closure_set(v___x_2100_, 1, v_cmp_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg___lam__0(lean_object* v_cmp_2101_, lean_object* v_a_2102_, lean_object* v_____s_2103_){
_start:
{
lean_object* v_r_2104_; lean_object* v___x_2105_; 
v_r_2104_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2101_, v_a_2102_, v_____s_2103_);
v___x_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2105_, 0, v_r_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg(lean_object* v_cmp_2106_, lean_object* v_inst_2107_, lean_object* v_t_2108_, lean_object* v_l_2109_){
_start:
{
lean_object* v___f_2110_; lean_object* v___x_2111_; 
v___f_2110_ = lean_alloc_closure((void*)(l_Std_TreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2110_, 0, v_cmp_2106_);
v___x_2111_ = lean_apply_4(v_inst_2107_, lean_box(0), v_l_2109_, v_t_2108_, v___f_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany(lean_object* v_00_u03b1_2112_, lean_object* v_cmp_2113_, lean_object* v_00_u03c1_2114_, lean_object* v_inst_2115_, lean_object* v_t_2116_, lean_object* v_l_2117_){
_start:
{
lean_object* v___f_2118_; lean_object* v___x_2119_; 
v___f_2118_ = lean_alloc_closure((void*)(l_Std_TreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2118_, 0, v_cmp_2113_);
v___x_2119_ = lean_apply_4(v_inst_2115_, lean_box(0), v_l_2117_, v_t_2116_, v___f_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1(lean_object* v___f_2123_, lean_object* v_inst_2124_, lean_object* v_m_2125_, lean_object* v_prec_2126_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2127_ = ((lean_object*)(l_Std_TreeSet_instRepr___redArg___lam__1___closed__1));
v___x_2128_ = lean_box(0);
v___x_2129_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_2130_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2129_, v___f_2123_, v___x_2128_, v_m_2125_);
v___x_2131_ = l_List_repr___redArg(v_inst_2124_, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2127_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Repr_addAppParen(v___x_2132_, v_prec_2126_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1___boxed(lean_object* v___f_2134_, lean_object* v_inst_2135_, lean_object* v_m_2136_, lean_object* v_prec_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Std_TreeSet_instRepr___redArg___lam__1(v___f_2134_, v_inst_2135_, v_m_2136_, v_prec_2137_);
lean_dec(v_prec_2137_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg(lean_object* v_inst_2139_){
_start:
{
lean_object* v___f_2140_; lean_object* v___f_2141_; 
v___f_2140_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___f_2141_ = lean_alloc_closure((void*)(l_Std_TreeSet_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2141_, 0, v___f_2140_);
lean_closure_set(v___f_2141_, 1, v_inst_2139_);
return v___f_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr(lean_object* v_00_u03b1_2142_, lean_object* v_cmp_2143_, lean_object* v_inst_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Std_TreeSet_instRepr___redArg(v_inst_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___boxed(lean_object* v_00_u03b1_2146_, lean_object* v_cmp_2147_, lean_object* v_inst_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Std_TreeSet_instRepr(v_00_u03b1_2146_, v_cmp_2147_, v_inst_2148_);
lean_dec_ref(v_cmp_2147_);
return v_res_2149_;
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
