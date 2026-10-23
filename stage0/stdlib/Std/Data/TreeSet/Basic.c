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
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(1);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___redArg___boxed(lean_object* v___dummy_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_TreeSet_empty___redArg();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_empty(lean_object* v_00_u03b1_77_, lean_object* v_cmp_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_box(1);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_empty___boxed(lean_object* v_00_u03b1_80_, lean_object* v_cmp_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_TreeSet_empty(v_00_u03b1_80_, v_cmp_81_);
lean_dec_ref(v_cmp_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(1);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_TreeSet_instEmptyCollection___redArg();
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection(lean_object* v_00_u03b1_87_, lean_object* v_cmp_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(1);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_90_, lean_object* v_cmp_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_TreeSet_instEmptyCollection(v_00_u03b1_90_, v_cmp_91_);
lean_dec_ref(v_cmp_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(1);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___redArg___boxed(lean_object* v___dummy_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_TreeSet_instInhabited___redArg();
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited(lean_object* v_00_u03b1_97_, lean_object* v_cmp_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_box(1);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInhabited___boxed(lean_object* v_00_u03b1_100_, lean_object* v_cmp_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_TreeSet_instInhabited(v_00_u03b1_100_, v_cmp_101_);
lean_dec_ref(v_cmp_101_);
return v_res_102_;
}
}
static lean_object* _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3));
v___x_141_ = l_String_toRawSubstring_x27(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(lean_object* v_x_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__3));
lean_inc(v_x_159_);
v___x_163_ = l_Lean_Syntax_isOfKind(v_x_159_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_x_159_);
v___x_164_ = lean_box(1);
v___x_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_a_161_);
return v___x_165_;
}
else
{
lean_object* v_quotContext_166_; lean_object* v_currMacroScope_167_; lean_object* v_ref_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_quotContext_166_ = lean_ctor_get(v_a_160_, 1);
v_currMacroScope_167_ = lean_ctor_get(v_a_160_, 2);
v_ref_168_ = lean_ctor_get(v_a_160_, 5);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = l_Lean_Syntax_getArg(v_x_159_, v___x_169_);
v___x_171_ = lean_unsigned_to_nat(2u);
v___x_172_ = l_Lean_Syntax_getArg(v_x_159_, v___x_171_);
lean_dec(v_x_159_);
v___x_173_ = 0;
v___x_174_ = l_Lean_SourceInfo_fromRef(v_ref_168_, v___x_173_);
v___x_175_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2));
v___x_176_ = lean_obj_once(&l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4, &l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4_once, _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4);
v___x_177_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_167_);
lean_inc(v_quotContext_166_);
v___x_178_ = l_Lean_addMacroScope(v_quotContext_166_, v___x_177_, v_currMacroScope_167_);
v___x_179_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10));
lean_inc_n(v___x_174_, 2);
v___x_180_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_180_, 0, v___x_174_);
lean_ctor_set(v___x_180_, 1, v___x_176_);
lean_ctor_set(v___x_180_, 2, v___x_178_);
lean_ctor_set(v___x_180_, 3, v___x_179_);
v___x_181_ = ((lean_object*)(l_Std_TreeSet___auto__1___closed__9));
v___x_182_ = l_Lean_Syntax_node2(v___x_174_, v___x_181_, v___x_170_, v___x_172_);
v___x_183_ = l_Lean_Syntax_node2(v___x_174_, v___x_175_, v___x_180_, v___x_182_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_a_161_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___boxed(lean_object* v_x_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(v_x_185_, v_a_186_, v_a_187_);
lean_dec_ref(v_a_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(lean_object* v_x_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2));
lean_inc(v_x_192_);
v___x_196_ = l_Lean_Syntax_isOfKind(v_x_192_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_x_192_);
v___x_197_ = lean_box(0);
v___x_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v_a_194_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = l_Lean_Syntax_getArg(v_x_192_, v___x_199_);
v___x_201_ = ((lean_object*)(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1));
lean_inc(v___x_200_);
v___x_202_ = l_Lean_Syntax_isOfKind(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v___x_200_);
lean_dec(v_x_192_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_a_194_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = l_Lean_Syntax_getArg(v_x_192_, v___x_205_);
lean_dec(v_x_192_);
v___x_207_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_206_);
v___x_208_ = l_Lean_Syntax_matchesNull(v___x_206_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v___x_206_);
lean_dec(v___x_200_);
v___x_209_ = lean_box(0);
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v_a_194_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_ref_213_; uint8_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_211_ = l_Lean_Syntax_getArg(v___x_206_, v___x_199_);
v___x_212_ = l_Lean_Syntax_getArg(v___x_206_, v___x_205_);
lean_dec(v___x_206_);
v_ref_213_ = l_Lean_replaceRef(v___x_200_, v_a_193_);
lean_dec(v___x_200_);
v___x_214_ = 0;
v___x_215_ = l_Lean_SourceInfo_fromRef(v_ref_213_, v___x_214_);
lean_dec(v_ref_213_);
v___x_216_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__3));
v___x_217_ = ((lean_object*)(l_Std_TreeSet_term___x7em___00__closed__6));
lean_inc(v___x_215_);
v___x_218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_215_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = l_Lean_Syntax_node3(v___x_215_, v___x_216_, v___x_211_, v___x_218_, v___x_212_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v_a_194_);
return v___x_220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___boxed(lean_object* v_x_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(v_x_221_, v_a_222_, v_a_223_);
lean_dec(v_a_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insert___redArg(lean_object* v_cmp_225_, lean_object* v_l_226_, lean_object* v_a_227_){
_start:
{
uint8_t v___x_228_; 
lean_inc(v_l_226_);
lean_inc(v_a_227_);
lean_inc_ref(v_cmp_225_);
v___x_228_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_225_, v_a_227_, v_l_226_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_box(0);
v___x_230_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_225_, v_a_227_, v___x_229_, v_l_226_);
return v___x_230_;
}
else
{
lean_dec(v_a_227_);
lean_dec_ref(v_cmp_225_);
return v_l_226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insert(lean_object* v_00_u03b1_231_, lean_object* v_cmp_232_, lean_object* v_l_233_, lean_object* v_a_234_){
_start:
{
uint8_t v___x_235_; 
lean_inc(v_l_233_);
lean_inc(v_a_234_);
lean_inc_ref(v_cmp_232_);
v___x_235_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_232_, v_a_234_, v_l_233_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_box(0);
v___x_237_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_232_, v_a_234_, v___x_236_, v_l_233_);
return v___x_237_;
}
else
{
lean_dec(v_a_234_);
lean_dec_ref(v_cmp_232_);
return v_l_233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg___lam__0(lean_object* v_cmp_238_, lean_object* v_e_239_){
_start:
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_box(1);
lean_inc(v_e_239_);
lean_inc_ref(v_cmp_238_);
v___x_241_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_238_, v_e_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_box(0);
v___x_243_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_238_, v_e_239_, v___x_242_, v___x_240_);
return v___x_243_;
}
else
{
lean_dec(v_e_239_);
lean_dec_ref(v_cmp_238_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton___redArg(lean_object* v_cmp_244_){
_start:
{
lean_object* v___f_245_; 
v___f_245_ = lean_alloc_closure((void*)(l_Std_TreeSet_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_245_, 0, v_cmp_244_);
return v___f_245_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSingleton(lean_object* v_00_u03b1_246_, lean_object* v_cmp_247_){
_start:
{
lean_object* v___f_248_; 
v___f_248_ = lean_alloc_closure((void*)(l_Std_TreeSet_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_248_, 0, v_cmp_247_);
return v___f_248_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg___lam__0(lean_object* v_cmp_249_, lean_object* v_e_250_, lean_object* v_s_251_){
_start:
{
uint8_t v___x_252_; 
lean_inc(v_s_251_);
lean_inc(v_e_250_);
lean_inc_ref(v_cmp_249_);
v___x_252_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_249_, v_e_250_, v_s_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_box(0);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_249_, v_e_250_, v___x_253_, v_s_251_);
return v___x_254_;
}
else
{
lean_dec(v_e_250_);
lean_dec_ref(v_cmp_249_);
return v_s_251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert___redArg(lean_object* v_cmp_255_){
_start:
{
lean_object* v___f_256_; 
v___f_256_ = lean_alloc_closure((void*)(l_Std_TreeSet_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_256_, 0, v_cmp_255_);
return v___f_256_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInsert(lean_object* v_00_u03b1_257_, lean_object* v_cmp_258_){
_start:
{
lean_object* v___f_259_; 
v___f_259_ = lean_alloc_closure((void*)(l_Std_TreeSet_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_259_, 0, v_cmp_258_);
return v___f_259_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert___redArg(lean_object* v_cmp_260_, lean_object* v_t_261_, lean_object* v_a_262_){
_start:
{
uint8_t v___x_263_; 
lean_inc(v_t_261_);
lean_inc(v_a_262_);
lean_inc_ref(v_cmp_260_);
v___x_263_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_260_, v_a_262_, v_t_261_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = lean_box(0);
v___x_265_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_260_, v_a_262_, v___x_264_, v_t_261_);
v___x_266_ = lean_box(v___x_263_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v_a_262_);
lean_dec_ref(v_cmp_260_);
v___x_268_ = lean_box(v___x_263_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_t_261_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_containsThenInsert(lean_object* v_00_u03b1_270_, lean_object* v_cmp_271_, lean_object* v_t_272_, lean_object* v_a_273_){
_start:
{
uint8_t v___x_274_; 
lean_inc(v_t_272_);
lean_inc(v_a_273_);
lean_inc_ref(v_cmp_271_);
v___x_274_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_271_, v_a_273_, v_t_272_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = lean_box(0);
v___x_276_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_271_, v_a_273_, v___x_275_, v_t_272_);
v___x_277_ = lean_box(v___x_274_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec(v_a_273_);
lean_dec_ref(v_cmp_271_);
v___x_279_ = lean_box(v___x_274_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v_t_272_);
return v___x_280_;
}
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_contains___redArg(lean_object* v_cmp_281_, lean_object* v_l_282_, lean_object* v_a_283_){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_281_, v_a_283_, v_l_282_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___redArg___boxed(lean_object* v_cmp_285_, lean_object* v_l_286_, lean_object* v_a_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_TreeSet_contains___redArg(v_cmp_285_, v_l_286_, v_a_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_contains(lean_object* v_00_u03b1_290_, lean_object* v_cmp_291_, lean_object* v_l_292_, lean_object* v_a_293_){
_start:
{
uint8_t v___x_294_; 
v___x_294_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_291_, v_a_293_, v_l_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_contains___boxed(lean_object* v_00_u03b1_295_, lean_object* v_cmp_296_, lean_object* v_l_297_, lean_object* v_a_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Std_TreeSet_contains(v_00_u03b1_295_, v_cmp_296_, v_l_297_, v_a_298_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___redArg(){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = lean_box(0);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___redArg___boxed(lean_object* v___dummy_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_TreeSet_instMembership___redArg();
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership(lean_object* v_00_u03b1_305_, lean_object* v_cmp_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_box(0);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instMembership___boxed(lean_object* v_00_u03b1_308_, lean_object* v_cmp_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_TreeSet_instMembership(v_00_u03b1_308_, v_cmp_309_);
lean_dec_ref(v_cmp_309_);
return v_res_310_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableMem___redArg(lean_object* v_cmp_311_, lean_object* v_m_312_, lean_object* v_a_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_311_, v_a_313_, v_m_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___redArg___boxed(lean_object* v_cmp_315_, lean_object* v_m_316_, lean_object* v_a_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_Std_TreeSet_instDecidableMem___redArg(v_cmp_315_, v_m_316_, v_a_317_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableMem(lean_object* v_00_u03b1_320_, lean_object* v_cmp_321_, lean_object* v_m_322_, lean_object* v_a_323_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_321_, v_a_323_, v_m_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableMem___boxed(lean_object* v_00_u03b1_325_, lean_object* v_cmp_326_, lean_object* v_m_327_, lean_object* v_a_328_){
_start:
{
uint8_t v_res_329_; lean_object* v_r_330_; 
v_res_329_ = l_Std_TreeSet_instDecidableMem(v_00_u03b1_325_, v_cmp_326_, v_m_327_, v_a_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg(lean_object* v_t_331_){
_start:
{
if (lean_obj_tag(v_t_331_) == 0)
{
lean_object* v_size_332_; 
v_size_332_ = lean_ctor_get(v_t_331_, 0);
lean_inc(v_size_332_);
return v_size_332_;
}
else
{
lean_object* v___x_333_; 
v___x_333_ = lean_unsigned_to_nat(0u);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___redArg___boxed(lean_object* v_t_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_TreeSet_size___redArg(v_t_334_);
lean_dec(v_t_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size(lean_object* v_00_u03b1_336_, lean_object* v_cmp_337_, lean_object* v_t_338_){
_start:
{
if (lean_obj_tag(v_t_338_) == 0)
{
lean_object* v_size_339_; 
v_size_339_ = lean_ctor_get(v_t_338_, 0);
lean_inc(v_size_339_);
return v_size_339_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = lean_unsigned_to_nat(0u);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_size___boxed(lean_object* v_00_u03b1_341_, lean_object* v_cmp_342_, lean_object* v_t_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_TreeSet_size(v_00_u03b1_341_, v_cmp_342_, v_t_343_);
lean_dec(v_t_343_);
lean_dec_ref(v_cmp_342_);
return v_res_344_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_isEmpty___redArg(lean_object* v_t_345_){
_start:
{
if (lean_obj_tag(v_t_345_) == 0)
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
else
{
uint8_t v___x_347_; 
v___x_347_ = 1;
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___redArg___boxed(lean_object* v_t_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Std_TreeSet_isEmpty___redArg(v_t_348_);
lean_dec(v_t_348_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_isEmpty(lean_object* v_00_u03b1_351_, lean_object* v_cmp_352_, lean_object* v_t_353_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_isEmpty___boxed(lean_object* v_00_u03b1_356_, lean_object* v_cmp_357_, lean_object* v_t_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Std_TreeSet_isEmpty(v_00_u03b1_356_, v_cmp_357_, v_t_358_);
lean_dec(v_t_358_);
lean_dec_ref(v_cmp_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_erase___redArg(lean_object* v_cmp_361_, lean_object* v_t_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_361_, v_a_363_, v_t_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_erase(lean_object* v_00_u03b1_365_, lean_object* v_cmp_366_, lean_object* v_t_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_366_, v_a_368_, v_t_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f___redArg(lean_object* v_cmp_370_, lean_object* v_t_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_370_, v_t_371_, v_a_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x3f(lean_object* v_00_u03b1_374_, lean_object* v_cmp_375_, lean_object* v_t_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_375_, v_t_376_, v_a_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get___redArg(lean_object* v_cmp_379_, lean_object* v_t_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_379_, v_t_380_, v_a_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get(lean_object* v_00_u03b1_383_, lean_object* v_cmp_384_, lean_object* v_t_385_, lean_object* v_a_386_, lean_object* v_h_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_384_, v_t_385_, v_a_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___redArg(lean_object* v_cmp_389_, lean_object* v_inst_390_, lean_object* v_t_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_389_, v_t_391_, v_a_392_, v_inst_390_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___redArg___boxed(lean_object* v_cmp_394_, lean_object* v_inst_395_, lean_object* v_t_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_TreeSet_get_x21___redArg(v_cmp_394_, v_inst_395_, v_t_396_, v_a_397_);
lean_dec(v_inst_395_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21(lean_object* v_00_u03b1_399_, lean_object* v_cmp_400_, lean_object* v_inst_401_, lean_object* v_t_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_400_, v_t_402_, v_a_403_, v_inst_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_get_x21___boxed(lean_object* v_00_u03b1_405_, lean_object* v_cmp_406_, lean_object* v_inst_407_, lean_object* v_t_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_TreeSet_get_x21(v_00_u03b1_405_, v_cmp_406_, v_inst_407_, v_t_408_, v_a_409_);
lean_dec(v_inst_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg(lean_object* v_cmp_411_, lean_object* v_t_412_, lean_object* v_a_413_, lean_object* v_fallback_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_411_, v_t_412_, v_a_413_, v_fallback_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___redArg___boxed(lean_object* v_cmp_416_, lean_object* v_t_417_, lean_object* v_a_418_, lean_object* v_fallback_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_TreeSet_getD___redArg(v_cmp_416_, v_t_417_, v_a_418_, v_fallback_419_);
lean_dec(v_fallback_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD(lean_object* v_00_u03b1_421_, lean_object* v_cmp_422_, lean_object* v_t_423_, lean_object* v_a_424_, lean_object* v_fallback_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_422_, v_t_423_, v_a_424_, v_fallback_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getD___boxed(lean_object* v_00_u03b1_427_, lean_object* v_cmp_428_, lean_object* v_t_429_, lean_object* v_a_430_, lean_object* v_fallback_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_TreeSet_getD(v_00_u03b1_427_, v_cmp_428_, v_t_429_, v_a_430_, v_fallback_431_);
lean_dec(v_fallback_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg(lean_object* v_t_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___redArg___boxed(lean_object* v_t_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_TreeSet_min_x3f___redArg(v_t_435_);
lean_dec(v_t_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f(lean_object* v_00_u03b1_437_, lean_object* v_cmp_438_, lean_object* v_t_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x3f___boxed(lean_object* v_00_u03b1_441_, lean_object* v_cmp_442_, lean_object* v_t_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_TreeSet_min_x3f(v_00_u03b1_441_, v_cmp_442_, v_t_443_);
lean_dec(v_t_443_);
lean_dec_ref(v_cmp_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg(lean_object* v_t_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___redArg___boxed(lean_object* v_t_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_TreeSet_min___redArg(v_t_447_);
lean_dec(v_t_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min(lean_object* v_00_u03b1_449_, lean_object* v_cmp_450_, lean_object* v_t_451_, lean_object* v_h_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min___boxed(lean_object* v_00_u03b1_454_, lean_object* v_cmp_455_, lean_object* v_t_456_, lean_object* v_h_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_TreeSet_min(v_00_u03b1_454_, v_cmp_455_, v_t_456_, v_h_457_);
lean_dec(v_t_456_);
lean_dec_ref(v_cmp_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg(lean_object* v_inst_459_, lean_object* v_t_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_459_, v_t_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___redArg___boxed(lean_object* v_inst_462_, lean_object* v_t_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_TreeSet_min_x21___redArg(v_inst_462_, v_t_463_);
lean_dec(v_t_463_);
lean_dec(v_inst_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21(lean_object* v_00_u03b1_465_, lean_object* v_cmp_466_, lean_object* v_inst_467_, lean_object* v_t_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_467_, v_t_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_min_x21___boxed(lean_object* v_00_u03b1_470_, lean_object* v_cmp_471_, lean_object* v_inst_472_, lean_object* v_t_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_TreeSet_min_x21(v_00_u03b1_470_, v_cmp_471_, v_inst_472_, v_t_473_);
lean_dec(v_t_473_);
lean_dec(v_inst_472_);
lean_dec_ref(v_cmp_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg(lean_object* v_t_475_, lean_object* v_fallback_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_475_, v_fallback_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___redArg___boxed(lean_object* v_t_478_, lean_object* v_fallback_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_TreeSet_minD___redArg(v_t_478_, v_fallback_479_);
lean_dec(v_fallback_479_);
lean_dec(v_t_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD(lean_object* v_00_u03b1_481_, lean_object* v_cmp_482_, lean_object* v_t_483_, lean_object* v_fallback_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_483_, v_fallback_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_minD___boxed(lean_object* v_00_u03b1_486_, lean_object* v_cmp_487_, lean_object* v_t_488_, lean_object* v_fallback_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_TreeSet_minD(v_00_u03b1_486_, v_cmp_487_, v_t_488_, v_fallback_489_);
lean_dec(v_fallback_489_);
lean_dec(v_t_488_);
lean_dec_ref(v_cmp_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg(lean_object* v_t_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___redArg___boxed(lean_object* v_t_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_TreeSet_max_x3f___redArg(v_t_493_);
lean_dec(v_t_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f(lean_object* v_00_u03b1_495_, lean_object* v_cmp_496_, lean_object* v_t_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x3f___boxed(lean_object* v_00_u03b1_499_, lean_object* v_cmp_500_, lean_object* v_t_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_TreeSet_max_x3f(v_00_u03b1_499_, v_cmp_500_, v_t_501_);
lean_dec(v_t_501_);
lean_dec_ref(v_cmp_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg(lean_object* v_t_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___redArg___boxed(lean_object* v_t_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_TreeSet_max___redArg(v_t_505_);
lean_dec(v_t_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max(lean_object* v_00_u03b1_507_, lean_object* v_cmp_508_, lean_object* v_t_509_, lean_object* v_h_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max___boxed(lean_object* v_00_u03b1_512_, lean_object* v_cmp_513_, lean_object* v_t_514_, lean_object* v_h_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_TreeSet_max(v_00_u03b1_512_, v_cmp_513_, v_t_514_, v_h_515_);
lean_dec(v_t_514_);
lean_dec_ref(v_cmp_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg(lean_object* v_inst_517_, lean_object* v_t_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_517_, v_t_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___redArg___boxed(lean_object* v_inst_520_, lean_object* v_t_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_TreeSet_max_x21___redArg(v_inst_520_, v_t_521_);
lean_dec(v_t_521_);
lean_dec(v_inst_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21(lean_object* v_00_u03b1_523_, lean_object* v_cmp_524_, lean_object* v_inst_525_, lean_object* v_t_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_525_, v_t_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_max_x21___boxed(lean_object* v_00_u03b1_528_, lean_object* v_cmp_529_, lean_object* v_inst_530_, lean_object* v_t_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_TreeSet_max_x21(v_00_u03b1_528_, v_cmp_529_, v_inst_530_, v_t_531_);
lean_dec(v_t_531_);
lean_dec(v_inst_530_);
lean_dec_ref(v_cmp_529_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg(lean_object* v_t_533_, lean_object* v_fallback_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_533_, v_fallback_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___redArg___boxed(lean_object* v_t_536_, lean_object* v_fallback_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_TreeSet_maxD___redArg(v_t_536_, v_fallback_537_);
lean_dec(v_fallback_537_);
lean_dec(v_t_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD(lean_object* v_00_u03b1_539_, lean_object* v_cmp_540_, lean_object* v_t_541_, lean_object* v_fallback_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_541_, v_fallback_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_maxD___boxed(lean_object* v_00_u03b1_544_, lean_object* v_cmp_545_, lean_object* v_t_546_, lean_object* v_fallback_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_TreeSet_maxD(v_00_u03b1_544_, v_cmp_545_, v_t_546_, v_fallback_547_);
lean_dec(v_fallback_547_);
lean_dec(v_t_546_);
lean_dec_ref(v_cmp_545_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg(lean_object* v_t_549_, lean_object* v_n_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_549_, v_n_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___redArg___boxed(lean_object* v_t_552_, lean_object* v_n_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_TreeSet_atIdx_x3f___redArg(v_t_552_, v_n_553_);
lean_dec(v_t_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f(lean_object* v_00_u03b1_555_, lean_object* v_cmp_556_, lean_object* v_t_557_, lean_object* v_n_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_557_, v_n_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x3f___boxed(lean_object* v_00_u03b1_560_, lean_object* v_cmp_561_, lean_object* v_t_562_, lean_object* v_n_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_TreeSet_atIdx_x3f(v_00_u03b1_560_, v_cmp_561_, v_t_562_, v_n_563_);
lean_dec(v_t_562_);
lean_dec_ref(v_cmp_561_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg(lean_object* v_t_565_, lean_object* v_n_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_565_, v_n_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___redArg___boxed(lean_object* v_t_568_, lean_object* v_n_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_TreeSet_atIdx___redArg(v_t_568_, v_n_569_);
lean_dec(v_t_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx(lean_object* v_00_u03b1_571_, lean_object* v_cmp_572_, lean_object* v_t_573_, lean_object* v_n_574_, lean_object* v_h_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_573_, v_n_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx___boxed(lean_object* v_00_u03b1_577_, lean_object* v_cmp_578_, lean_object* v_t_579_, lean_object* v_n_580_, lean_object* v_h_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_TreeSet_atIdx(v_00_u03b1_577_, v_cmp_578_, v_t_579_, v_n_580_, v_h_581_);
lean_dec(v_t_579_);
lean_dec_ref(v_cmp_578_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg(lean_object* v_inst_583_, lean_object* v_t_584_, lean_object* v_n_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_583_, v_t_584_, v_n_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___redArg___boxed(lean_object* v_inst_587_, lean_object* v_t_588_, lean_object* v_n_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_TreeSet_atIdx_x21___redArg(v_inst_587_, v_t_588_, v_n_589_);
lean_dec(v_t_588_);
lean_dec(v_inst_587_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21(lean_object* v_00_u03b1_591_, lean_object* v_cmp_592_, lean_object* v_inst_593_, lean_object* v_t_594_, lean_object* v_n_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_593_, v_t_594_, v_n_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdx_x21___boxed(lean_object* v_00_u03b1_597_, lean_object* v_cmp_598_, lean_object* v_inst_599_, lean_object* v_t_600_, lean_object* v_n_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_TreeSet_atIdx_x21(v_00_u03b1_597_, v_cmp_598_, v_inst_599_, v_t_600_, v_n_601_);
lean_dec(v_t_600_);
lean_dec(v_inst_599_);
lean_dec_ref(v_cmp_598_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg(lean_object* v_t_603_, lean_object* v_n_604_, lean_object* v_fallback_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_603_, v_n_604_, v_fallback_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___redArg___boxed(lean_object* v_t_607_, lean_object* v_n_608_, lean_object* v_fallback_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_TreeSet_atIdxD___redArg(v_t_607_, v_n_608_, v_fallback_609_);
lean_dec(v_fallback_609_);
lean_dec(v_t_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD(lean_object* v_00_u03b1_611_, lean_object* v_cmp_612_, lean_object* v_t_613_, lean_object* v_n_614_, lean_object* v_fallback_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_613_, v_n_614_, v_fallback_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_atIdxD___boxed(lean_object* v_00_u03b1_617_, lean_object* v_cmp_618_, lean_object* v_t_619_, lean_object* v_n_620_, lean_object* v_fallback_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Std_TreeSet_atIdxD(v_00_u03b1_617_, v_cmp_618_, v_t_619_, v_n_620_, v_fallback_621_);
lean_dec(v_fallback_621_);
lean_dec(v_t_619_);
lean_dec_ref(v_cmp_618_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f___redArg(lean_object* v_cmp_623_, lean_object* v_t_624_, lean_object* v_k_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_box(0);
v___x_627_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_623_, v_k_625_, v___x_626_, v_t_624_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x3f(lean_object* v_00_u03b1_628_, lean_object* v_cmp_629_, lean_object* v_t_630_, lean_object* v_k_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_box(0);
v___x_633_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_629_, v_k_631_, v___x_632_, v_t_630_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f___redArg(lean_object* v_cmp_634_, lean_object* v_t_635_, lean_object* v_k_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_box(0);
v___x_638_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_634_, v_k_636_, v___x_637_, v_t_635_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x3f(lean_object* v_00_u03b1_639_, lean_object* v_cmp_640_, lean_object* v_t_641_, lean_object* v_k_642_){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_box(0);
v___x_644_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_640_, v_k_642_, v___x_643_, v_t_641_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f___redArg(lean_object* v_cmp_645_, lean_object* v_t_646_, lean_object* v_k_647_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_box(0);
v___x_649_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_645_, v_k_647_, v___x_648_, v_t_646_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x3f(lean_object* v_00_u03b1_650_, lean_object* v_cmp_651_, lean_object* v_t_652_, lean_object* v_k_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_box(0);
v___x_655_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_651_, v_k_653_, v___x_654_, v_t_652_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f___redArg(lean_object* v_cmp_656_, lean_object* v_t_657_, lean_object* v_k_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_box(0);
v___x_660_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_656_, v_k_658_, v___x_659_, v_t_657_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x3f(lean_object* v_00_u03b1_661_, lean_object* v_cmp_662_, lean_object* v_t_663_, lean_object* v_k_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_box(0);
v___x_666_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_662_, v_k_664_, v___x_665_, v_t_663_);
return v___x_666_;
}
}
static lean_object* _init_l_Std_TreeSet_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_670_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__2));
v___x_671_ = lean_unsigned_to_nat(14u);
v___x_672_ = lean_unsigned_to_nat(22u);
v___x_673_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__1));
v___x_674_ = ((lean_object*)(l_Std_TreeSet_getGE_x21___redArg___closed__0));
v___x_675_ = l_mkPanicMessageWithDecl(v___x_674_, v___x_673_, v___x_672_, v___x_671_, v___x_670_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___redArg(lean_object* v_cmp_676_, lean_object* v_inst_677_, lean_object* v_t_678_, lean_object* v_k_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_box(0);
v___x_681_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_676_, v_k_679_, v___x_680_, v_t_678_);
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
v_val_684_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_val_684_);
lean_dec_ref_known(v___x_681_, 1);
return v_val_684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___redArg___boxed(lean_object* v_cmp_685_, lean_object* v_inst_686_, lean_object* v_t_687_, lean_object* v_k_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_TreeSet_getGE_x21___redArg(v_cmp_685_, v_inst_686_, v_t_687_, v_k_688_);
lean_dec(v_inst_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21(lean_object* v_00_u03b1_690_, lean_object* v_cmp_691_, lean_object* v_inst_692_, lean_object* v_t_693_, lean_object* v_k_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_box(0);
v___x_696_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_691_, v_k_694_, v___x_695_, v_t_693_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE_x21___boxed(lean_object* v_00_u03b1_700_, lean_object* v_cmp_701_, lean_object* v_inst_702_, lean_object* v_t_703_, lean_object* v_k_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Std_TreeSet_getGE_x21(v_00_u03b1_700_, v_cmp_701_, v_inst_702_, v_t_703_, v_k_704_);
lean_dec(v_inst_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg(lean_object* v_cmp_706_, lean_object* v_inst_707_, lean_object* v_t_708_, lean_object* v_k_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_box(0);
v___x_711_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_706_, v_k_709_, v___x_710_, v_t_708_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_713_ = l_panic___redArg(v_inst_707_, v___x_712_);
return v___x_713_;
}
else
{
lean_object* v_val_714_; 
v_val_714_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v___x_711_, 1);
return v_val_714_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___redArg___boxed(lean_object* v_cmp_715_, lean_object* v_inst_716_, lean_object* v_t_717_, lean_object* v_k_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_TreeSet_getGT_x21___redArg(v_cmp_715_, v_inst_716_, v_t_717_, v_k_718_);
lean_dec(v_inst_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21(lean_object* v_00_u03b1_720_, lean_object* v_cmp_721_, lean_object* v_inst_722_, lean_object* v_t_723_, lean_object* v_k_724_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_box(0);
v___x_726_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_721_, v_k_724_, v___x_725_, v_t_723_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_728_ = l_panic___redArg(v_inst_722_, v___x_727_);
return v___x_728_;
}
else
{
lean_object* v_val_729_; 
v_val_729_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_val_729_);
lean_dec_ref_known(v___x_726_, 1);
return v_val_729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT_x21___boxed(lean_object* v_00_u03b1_730_, lean_object* v_cmp_731_, lean_object* v_inst_732_, lean_object* v_t_733_, lean_object* v_k_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_TreeSet_getGT_x21(v_00_u03b1_730_, v_cmp_731_, v_inst_732_, v_t_733_, v_k_734_);
lean_dec(v_inst_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg(lean_object* v_cmp_736_, lean_object* v_inst_737_, lean_object* v_t_738_, lean_object* v_k_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_box(0);
v___x_741_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_736_, v_k_739_, v___x_740_, v_t_738_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_743_ = l_panic___redArg(v_inst_737_, v___x_742_);
return v___x_743_;
}
else
{
lean_object* v_val_744_; 
v_val_744_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___x_741_, 1);
return v_val_744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___redArg___boxed(lean_object* v_cmp_745_, lean_object* v_inst_746_, lean_object* v_t_747_, lean_object* v_k_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_TreeSet_getLE_x21___redArg(v_cmp_745_, v_inst_746_, v_t_747_, v_k_748_);
lean_dec(v_inst_746_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21(lean_object* v_00_u03b1_750_, lean_object* v_cmp_751_, lean_object* v_inst_752_, lean_object* v_t_753_, lean_object* v_k_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_box(0);
v___x_756_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_751_, v_k_754_, v___x_755_, v_t_753_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_758_ = l_panic___redArg(v_inst_752_, v___x_757_);
return v___x_758_;
}
else
{
lean_object* v_val_759_; 
v_val_759_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v___x_756_, 1);
return v_val_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE_x21___boxed(lean_object* v_00_u03b1_760_, lean_object* v_cmp_761_, lean_object* v_inst_762_, lean_object* v_t_763_, lean_object* v_k_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_TreeSet_getLE_x21(v_00_u03b1_760_, v_cmp_761_, v_inst_762_, v_t_763_, v_k_764_);
lean_dec(v_inst_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg(lean_object* v_cmp_766_, lean_object* v_inst_767_, lean_object* v_t_768_, lean_object* v_k_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_box(0);
v___x_771_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_766_, v_k_769_, v___x_770_, v_t_768_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_773_ = l_panic___redArg(v_inst_767_, v___x_772_);
return v___x_773_;
}
else
{
lean_object* v_val_774_; 
v_val_774_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_val_774_);
lean_dec_ref_known(v___x_771_, 1);
return v_val_774_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___redArg___boxed(lean_object* v_cmp_775_, lean_object* v_inst_776_, lean_object* v_t_777_, lean_object* v_k_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_TreeSet_getLT_x21___redArg(v_cmp_775_, v_inst_776_, v_t_777_, v_k_778_);
lean_dec(v_inst_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21(lean_object* v_00_u03b1_780_, lean_object* v_cmp_781_, lean_object* v_inst_782_, lean_object* v_t_783_, lean_object* v_k_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_box(0);
v___x_786_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_781_, v_k_784_, v___x_785_, v_t_783_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_obj_once(&l_Std_TreeSet_getGE_x21___redArg___closed__3, &l_Std_TreeSet_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_getGE_x21___redArg___closed__3);
v___x_788_ = l_panic___redArg(v_inst_782_, v___x_787_);
return v___x_788_;
}
else
{
lean_object* v_val_789_; 
v_val_789_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v___x_786_, 1);
return v_val_789_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT_x21___boxed(lean_object* v_00_u03b1_790_, lean_object* v_cmp_791_, lean_object* v_inst_792_, lean_object* v_t_793_, lean_object* v_k_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_TreeSet_getLT_x21(v_00_u03b1_790_, v_cmp_791_, v_inst_792_, v_t_793_, v_k_794_);
lean_dec(v_inst_792_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg(lean_object* v_cmp_796_, lean_object* v_t_797_, lean_object* v_k_798_, lean_object* v_fallback_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_box(0);
v___x_801_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_796_, v_k_798_, v___x_800_, v_t_797_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_inc(v_fallback_799_);
return v_fallback_799_;
}
else
{
lean_object* v_val_802_; 
v_val_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_val_802_);
lean_dec_ref_known(v___x_801_, 1);
return v_val_802_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___redArg___boxed(lean_object* v_cmp_803_, lean_object* v_t_804_, lean_object* v_k_805_, lean_object* v_fallback_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_TreeSet_getGED___redArg(v_cmp_803_, v_t_804_, v_k_805_, v_fallback_806_);
lean_dec(v_fallback_806_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED(lean_object* v_00_u03b1_808_, lean_object* v_cmp_809_, lean_object* v_t_810_, lean_object* v_k_811_, lean_object* v_fallback_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_box(0);
v___x_814_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_809_, v_k_811_, v___x_813_, v_t_810_);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_getGED___boxed(lean_object* v_00_u03b1_816_, lean_object* v_cmp_817_, lean_object* v_t_818_, lean_object* v_k_819_, lean_object* v_fallback_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Std_TreeSet_getGED(v_00_u03b1_816_, v_cmp_817_, v_t_818_, v_k_819_, v_fallback_820_);
lean_dec(v_fallback_820_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg(lean_object* v_cmp_822_, lean_object* v_t_823_, lean_object* v_k_824_, lean_object* v_fallback_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_box(0);
v___x_827_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_822_, v_k_824_, v___x_826_, v_t_823_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_inc(v_fallback_825_);
return v_fallback_825_;
}
else
{
lean_object* v_val_828_; 
v_val_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_val_828_);
lean_dec_ref_known(v___x_827_, 1);
return v_val_828_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___redArg___boxed(lean_object* v_cmp_829_, lean_object* v_t_830_, lean_object* v_k_831_, lean_object* v_fallback_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_TreeSet_getGTD___redArg(v_cmp_829_, v_t_830_, v_k_831_, v_fallback_832_);
lean_dec(v_fallback_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD(lean_object* v_00_u03b1_834_, lean_object* v_cmp_835_, lean_object* v_t_836_, lean_object* v_k_837_, lean_object* v_fallback_838_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_box(0);
v___x_840_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_835_, v_k_837_, v___x_839_, v_t_836_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_inc(v_fallback_838_);
return v_fallback_838_;
}
else
{
lean_object* v_val_841_; 
v_val_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v___x_840_, 1);
return v_val_841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGTD___boxed(lean_object* v_00_u03b1_842_, lean_object* v_cmp_843_, lean_object* v_t_844_, lean_object* v_k_845_, lean_object* v_fallback_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_TreeSet_getGTD(v_00_u03b1_842_, v_cmp_843_, v_t_844_, v_k_845_, v_fallback_846_);
lean_dec(v_fallback_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg(lean_object* v_cmp_848_, lean_object* v_t_849_, lean_object* v_k_850_, lean_object* v_fallback_851_){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_box(0);
v___x_853_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_848_, v_k_850_, v___x_852_, v_t_849_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_inc(v_fallback_851_);
return v_fallback_851_;
}
else
{
lean_object* v_val_854_; 
v_val_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_val_854_);
lean_dec_ref_known(v___x_853_, 1);
return v_val_854_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___redArg___boxed(lean_object* v_cmp_855_, lean_object* v_t_856_, lean_object* v_k_857_, lean_object* v_fallback_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_TreeSet_getLED___redArg(v_cmp_855_, v_t_856_, v_k_857_, v_fallback_858_);
lean_dec(v_fallback_858_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED(lean_object* v_00_u03b1_860_, lean_object* v_cmp_861_, lean_object* v_t_862_, lean_object* v_k_863_, lean_object* v_fallback_864_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_box(0);
v___x_866_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_861_, v_k_863_, v___x_865_, v_t_862_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_inc(v_fallback_864_);
return v_fallback_864_;
}
else
{
lean_object* v_val_867_; 
v_val_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_val_867_);
lean_dec_ref_known(v___x_866_, 1);
return v_val_867_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLED___boxed(lean_object* v_00_u03b1_868_, lean_object* v_cmp_869_, lean_object* v_t_870_, lean_object* v_k_871_, lean_object* v_fallback_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_TreeSet_getLED(v_00_u03b1_868_, v_cmp_869_, v_t_870_, v_k_871_, v_fallback_872_);
lean_dec(v_fallback_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg(lean_object* v_cmp_874_, lean_object* v_t_875_, lean_object* v_k_876_, lean_object* v_fallback_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_box(0);
v___x_879_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_874_, v_k_876_, v___x_878_, v_t_875_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_inc(v_fallback_877_);
return v_fallback_877_;
}
else
{
lean_object* v_val_880_; 
v_val_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_val_880_);
lean_dec_ref_known(v___x_879_, 1);
return v_val_880_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___redArg___boxed(lean_object* v_cmp_881_, lean_object* v_t_882_, lean_object* v_k_883_, lean_object* v_fallback_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_TreeSet_getLTD___redArg(v_cmp_881_, v_t_882_, v_k_883_, v_fallback_884_);
lean_dec(v_fallback_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD(lean_object* v_00_u03b1_886_, lean_object* v_cmp_887_, lean_object* v_t_888_, lean_object* v_k_889_, lean_object* v_fallback_890_){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_box(0);
v___x_892_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_887_, v_k_889_, v___x_891_, v_t_888_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_inc(v_fallback_890_);
return v_fallback_890_;
}
else
{
lean_object* v_val_893_; 
v_val_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v___x_892_, 1);
return v_val_893_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLTD___boxed(lean_object* v_00_u03b1_894_, lean_object* v_cmp_895_, lean_object* v_t_896_, lean_object* v_k_897_, lean_object* v_fallback_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_TreeSet_getLTD(v_00_u03b1_894_, v_cmp_895_, v_t_896_, v_k_897_, v_fallback_898_);
lean_dec(v_fallback_898_);
return v_res_899_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_filter___redArg___lam__0(lean_object* v_f_900_, lean_object* v_a_901_, lean_object* v_x_902_){
_start:
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = lean_apply_1(v_f_900_, v_a_901_);
v___x_904_ = lean_unbox(v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg___lam__0___boxed(lean_object* v_f_905_, lean_object* v_a_906_, lean_object* v_x_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_Std_TreeSet_filter___redArg___lam__0(v_f_905_, v_a_906_, v_x_907_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___redArg(lean_object* v_f_910_, lean_object* v_m_911_){
_start:
{
lean_object* v___f_912_; lean_object* v___x_913_; 
v___f_912_ = lean_alloc_closure((void*)(l_Std_TreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_912_, 0, v_f_910_);
v___x_913_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_912_, v_m_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter(lean_object* v_00_u03b1_914_, lean_object* v_cmp_915_, lean_object* v_f_916_, lean_object* v_m_917_){
_start:
{
lean_object* v___f_918_; lean_object* v___x_919_; 
v___f_918_ = lean_alloc_closure((void*)(l_Std_TreeSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_918_, 0, v_f_916_);
v___x_919_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_918_, v_m_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_filter___boxed(lean_object* v_00_u03b1_920_, lean_object* v_cmp_921_, lean_object* v_f_922_, lean_object* v_m_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Std_TreeSet_filter(v_00_u03b1_920_, v_cmp_921_, v_f_922_, v_m_923_);
lean_dec_ref(v_cmp_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg___lam__0(lean_object* v_f_925_, lean_object* v_c_926_, lean_object* v_a_927_, lean_object* v_x_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lean_apply_2(v_f_925_, v_c_926_, v_a_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___redArg(lean_object* v_inst_930_, lean_object* v_f_931_, lean_object* v_init_932_, lean_object* v_t_933_){
_start:
{
lean_object* v___f_934_; lean_object* v___x_935_; 
v___f_934_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_934_, 0, v_f_931_);
v___x_935_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_930_, v___f_934_, v_init_932_, v_t_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM(lean_object* v_00_u03b1_936_, lean_object* v_cmp_937_, lean_object* v_m_938_, lean_object* v_00_u03b4_939_, lean_object* v_inst_940_, lean_object* v_f_941_, lean_object* v_init_942_, lean_object* v_t_943_){
_start:
{
lean_object* v___f_944_; lean_object* v___x_945_; 
v___f_944_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_944_, 0, v_f_941_);
v___x_945_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_940_, v___f_944_, v_init_942_, v_t_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldlM___boxed(lean_object* v_00_u03b1_946_, lean_object* v_cmp_947_, lean_object* v_m_948_, lean_object* v_00_u03b4_949_, lean_object* v_inst_950_, lean_object* v_f_951_, lean_object* v_init_952_, lean_object* v_t_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_TreeSet_foldlM(v_00_u03b1_946_, v_cmp_947_, v_m_948_, v_00_u03b4_949_, v_inst_950_, v_f_951_, v_init_952_, v_t_953_);
lean_dec_ref(v_cmp_947_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___redArg(lean_object* v_f_955_, lean_object* v_init_956_, lean_object* v_t_957_){
_start:
{
lean_object* v___f_958_; lean_object* v___x_959_; 
v___f_958_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_958_, 0, v_f_955_);
v___x_959_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_958_, v_init_956_, v_t_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl(lean_object* v_00_u03b1_960_, lean_object* v_cmp_961_, lean_object* v_00_u03b4_962_, lean_object* v_f_963_, lean_object* v_init_964_, lean_object* v_t_965_){
_start:
{
lean_object* v___f_966_; lean_object* v___x_967_; 
v___f_966_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_966_, 0, v_f_963_);
v___x_967_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_966_, v_init_964_, v_t_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldl___boxed(lean_object* v_00_u03b1_968_, lean_object* v_cmp_969_, lean_object* v_00_u03b4_970_, lean_object* v_f_971_, lean_object* v_init_972_, lean_object* v_t_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Std_TreeSet_foldl(v_00_u03b1_968_, v_cmp_969_, v_00_u03b4_970_, v_f_971_, v_init_972_, v_t_973_);
lean_dec_ref(v_cmp_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg___lam__0(lean_object* v_f_975_, lean_object* v_a_976_, lean_object* v_x_977_, lean_object* v_acc_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = lean_apply_2(v_f_975_, v_a_976_, v_acc_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___redArg(lean_object* v_inst_980_, lean_object* v_f_981_, lean_object* v_init_982_, lean_object* v_t_983_){
_start:
{
lean_object* v___f_984_; lean_object* v___x_985_; 
v___f_984_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_984_, 0, v_f_981_);
v___x_985_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_980_, v___f_984_, v_init_982_, v_t_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM(lean_object* v_00_u03b1_986_, lean_object* v_cmp_987_, lean_object* v_m_988_, lean_object* v_00_u03b4_989_, lean_object* v_inst_990_, lean_object* v_f_991_, lean_object* v_init_992_, lean_object* v_t_993_){
_start:
{
lean_object* v___f_994_; lean_object* v___x_995_; 
v___f_994_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_994_, 0, v_f_991_);
v___x_995_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_990_, v___f_994_, v_init_992_, v_t_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldrM___boxed(lean_object* v_00_u03b1_996_, lean_object* v_cmp_997_, lean_object* v_m_998_, lean_object* v_00_u03b4_999_, lean_object* v_inst_1000_, lean_object* v_f_1001_, lean_object* v_init_1002_, lean_object* v_t_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_TreeSet_foldrM(v_00_u03b1_996_, v_cmp_997_, v_m_998_, v_00_u03b4_999_, v_inst_1000_, v_f_1001_, v_init_1002_, v_t_1003_);
lean_dec_ref(v_cmp_997_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg___lam__0(lean_object* v_f_1005_, lean_object* v_x1_1006_, lean_object* v_x2_1007_, lean_object* v_x3_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_apply_2(v_f_1005_, v_x1_1006_, v_x3_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___redArg(lean_object* v_f_1029_, lean_object* v_init_1030_, lean_object* v_t_1031_){
_start:
{
lean_object* v___f_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___f_1032_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1032_, 0, v_f_1029_);
v___x_1033_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1034_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1033_, v___f_1032_, v_init_1030_, v_t_1031_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr(lean_object* v_00_u03b1_1035_, lean_object* v_cmp_1036_, lean_object* v_00_u03b4_1037_, lean_object* v_f_1038_, lean_object* v_init_1039_, lean_object* v_t_1040_){
_start:
{
lean_object* v___f_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___f_1041_ = lean_alloc_closure((void*)(l_Std_TreeSet_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1041_, 0, v_f_1038_);
v___x_1042_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1043_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1042_, v___f_1041_, v_init_1039_, v_t_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_foldr___boxed(lean_object* v_00_u03b1_1044_, lean_object* v_cmp_1045_, lean_object* v_00_u03b4_1046_, lean_object* v_f_1047_, lean_object* v_init_1048_, lean_object* v_t_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Std_TreeSet_foldr(v_00_u03b1_1044_, v_cmp_1045_, v_00_u03b4_1046_, v_f_1047_, v_init_1048_, v_t_1049_);
lean_dec_ref(v_cmp_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg___lam__0(lean_object* v_f_1051_, lean_object* v_cmp_1052_, lean_object* v_x_1053_, lean_object* v_a_1054_, lean_object* v_b_1055_){
_start:
{
lean_object* v_fst_1056_; lean_object* v_snd_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1071_; 
v_fst_1056_ = lean_ctor_get(v_x_1053_, 0);
v_snd_1057_ = lean_ctor_get(v_x_1053_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_x_1053_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1059_ = v_x_1053_;
v_isShared_1060_ = v_isSharedCheck_1071_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_snd_1057_);
lean_inc(v_fst_1056_);
lean_dec(v_x_1053_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1071_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; uint8_t v___x_1062_; 
lean_inc(v_a_1054_);
v___x_1061_ = lean_apply_1(v_f_1051_, v_a_1054_);
v___x_1062_ = lean_unbox(v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1052_, v_a_1054_, v_b_1055_, v_snd_1057_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v___x_1063_);
v___x_1065_ = v___x_1059_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_fst_1056_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1052_, v_a_1054_, v_b_1055_, v_fst_1056_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1067_);
v___x_1069_ = v___x_1059_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_snd_1057_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition___redArg(lean_object* v_cmp_1074_, lean_object* v_f_1075_, lean_object* v_t_1076_){
_start:
{
lean_object* v___f_1077_; lean_object* v___x_1078_; lean_object* v_p_1079_; lean_object* v_fst_1080_; lean_object* v_snd_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
v___f_1077_ = lean_alloc_closure((void*)(l_Std_TreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1077_, 0, v_f_1075_);
lean_closure_set(v___f_1077_, 1, v_cmp_1074_);
v___x_1078_ = ((lean_object*)(l_Std_TreeSet_partition___redArg___closed__0));
v_p_1079_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1077_, v___x_1078_, v_t_1076_);
v_fst_1080_ = lean_ctor_get(v_p_1079_, 0);
v_snd_1081_ = lean_ctor_get(v_p_1079_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_p_1079_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v_p_1079_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_snd_1081_);
lean_inc(v_fst_1080_);
lean_dec(v_p_1079_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_fst_1080_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_snd_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_partition(lean_object* v_00_u03b1_1089_, lean_object* v_cmp_1090_, lean_object* v_f_1091_, lean_object* v_t_1092_){
_start:
{
lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v_p_1095_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v___f_1093_ = lean_alloc_closure((void*)(l_Std_TreeSet_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1093_, 0, v_f_1091_);
lean_closure_set(v___f_1093_, 1, v_cmp_1090_);
v___x_1094_ = ((lean_object*)(l_Std_TreeSet_partition___redArg___closed__0));
v_p_1095_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1093_, v___x_1094_, v_t_1092_);
v_fst_1096_ = lean_ctor_get(v_p_1095_, 0);
v_snd_1097_ = lean_ctor_get(v_p_1095_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_p_1095_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v_p_1095_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_snd_1097_);
lean_inc(v_fst_1096_);
lean_dec(v_p_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_fst_1096_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_snd_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg___lam__0(lean_object* v_f_1105_, lean_object* v_x_1106_, lean_object* v_k_1107_, lean_object* v_v_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_apply_1(v_f_1105_, v_k_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___redArg(lean_object* v_inst_1110_, lean_object* v_f_1111_, lean_object* v_t_1112_){
_start:
{
lean_object* v___f_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___f_1113_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1113_, 0, v_f_1111_);
v___x_1114_ = lean_box(0);
v___x_1115_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1110_, v___f_1113_, v___x_1114_, v_t_1112_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM(lean_object* v_00_u03b1_1116_, lean_object* v_cmp_1117_, lean_object* v_m_1118_, lean_object* v_inst_1119_, lean_object* v_f_1120_, lean_object* v_t_1121_){
_start:
{
lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___f_1122_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1122_, 0, v_f_1120_);
v___x_1123_ = lean_box(0);
v___x_1124_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1119_, v___f_1122_, v___x_1123_, v_t_1121_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forM___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_cmp_1126_, lean_object* v_m_1127_, lean_object* v_inst_1128_, lean_object* v_f_1129_, lean_object* v_t_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Std_TreeSet_forM(v_00_u03b1_1125_, v_cmp_1126_, v_m_1127_, v_inst_1128_, v_f_1129_, v_t_1130_);
lean_dec_ref(v_cmp_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__0(lean_object* v_f_1132_, lean_object* v_a_1133_, lean_object* v_b_1134_, lean_object* v_c_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_apply_2(v_f_1132_, v_a_1133_, v_c_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg___lam__1(lean_object* v_toPure_1137_, lean_object* v_____do__lift_1138_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___redArg(lean_object* v_inst_1141_, lean_object* v_f_1142_, lean_object* v_init_1143_, lean_object* v_t_1144_){
_start:
{
lean_object* v_toApplicative_1145_; lean_object* v_toBind_1146_; lean_object* v_toPure_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; 
v_toApplicative_1145_ = lean_ctor_get(v_inst_1141_, 0);
v_toBind_1146_ = lean_ctor_get(v_inst_1141_, 1);
lean_inc(v_toBind_1146_);
v_toPure_1147_ = lean_ctor_get(v_toApplicative_1145_, 1);
lean_inc(v_toPure_1147_);
v___f_1148_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1148_, 0, v_f_1142_);
v___x_1149_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1141_, v___f_1148_, v_init_1143_, v_t_1144_);
v___f_1150_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1150_, 0, v_toPure_1147_);
v___x_1151_ = lean_apply_4(v_toBind_1146_, lean_box(0), lean_box(0), v___x_1149_, v___f_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn(lean_object* v_00_u03b1_1152_, lean_object* v_cmp_1153_, lean_object* v_00_u03b4_1154_, lean_object* v_m_1155_, lean_object* v_inst_1156_, lean_object* v_f_1157_, lean_object* v_init_1158_, lean_object* v_t_1159_){
_start:
{
lean_object* v_toApplicative_1160_; lean_object* v_toBind_1161_; lean_object* v_toPure_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; 
v_toApplicative_1160_ = lean_ctor_get(v_inst_1156_, 0);
v_toBind_1161_ = lean_ctor_get(v_inst_1156_, 1);
lean_inc(v_toBind_1161_);
v_toPure_1162_ = lean_ctor_get(v_toApplicative_1160_, 1);
lean_inc(v_toPure_1162_);
v___f_1163_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1163_, 0, v_f_1157_);
v___x_1164_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1156_, v___f_1163_, v_init_1158_, v_t_1159_);
v___f_1165_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1165_, 0, v_toPure_1162_);
v___x_1166_ = lean_apply_4(v_toBind_1161_, lean_box(0), lean_box(0), v___x_1164_, v___f_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_forIn___boxed(lean_object* v_00_u03b1_1167_, lean_object* v_cmp_1168_, lean_object* v_00_u03b4_1169_, lean_object* v_m_1170_, lean_object* v_inst_1171_, lean_object* v_f_1172_, lean_object* v_init_1173_, lean_object* v_t_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Std_TreeSet_forIn(v_00_u03b1_1167_, v_cmp_1168_, v_00_u03b4_1169_, v_m_1170_, v_inst_1171_, v_f_1172_, v_init_1173_, v_t_1174_);
lean_dec_ref(v_cmp_1168_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg___lam__1(lean_object* v_inst_1176_, lean_object* v_t_1177_, lean_object* v_f_1178_){
_start:
{
lean_object* v___f_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___f_1179_ = lean_alloc_closure((void*)(l_Std_TreeSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1179_, 0, v_f_1178_);
v___x_1180_ = lean_box(0);
v___x_1181_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1176_, v___f_1179_, v___x_1180_, v_t_1177_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___redArg(lean_object* v_inst_1182_){
_start:
{
lean_object* v___f_1183_; 
v___f_1183_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1183_, 0, v_inst_1182_);
return v___f_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad(lean_object* v_00_u03b1_1184_, lean_object* v_cmp_1185_, lean_object* v_m_1186_, lean_object* v_inst_1187_){
_start:
{
lean_object* v___f_1188_; 
v___f_1188_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1188_, 0, v_inst_1187_);
return v___f_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForMOfMonad___boxed(lean_object* v_00_u03b1_1189_, lean_object* v_cmp_1190_, lean_object* v_m_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_TreeSet_instForMOfMonad(v_00_u03b1_1189_, v_cmp_1190_, v_m_1191_, v_inst_1192_);
lean_dec_ref(v_cmp_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg___lam__2(lean_object* v_inst_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_m_1196_, lean_object* v_init_1197_, lean_object* v_f_1198_){
_start:
{
lean_object* v_toApplicative_1199_; lean_object* v_toBind_1200_; lean_object* v_toPure_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; 
v_toApplicative_1199_ = lean_ctor_get(v_inst_1194_, 0);
v_toBind_1200_ = lean_ctor_get(v_inst_1194_, 1);
lean_inc(v_toBind_1200_);
v_toPure_1201_ = lean_ctor_get(v_toApplicative_1199_, 1);
lean_inc(v_toPure_1201_);
v___f_1202_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1202_, 0, v_f_1198_);
v___x_1203_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1194_, v___f_1202_, v_init_1197_, v_m_1196_);
v___f_1204_ = lean_alloc_closure((void*)(l_Std_TreeSet_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1204_, 0, v_toPure_1201_);
v___x_1205_ = lean_apply_4(v_toBind_1200_, lean_box(0), lean_box(0), v___x_1203_, v___f_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___redArg(lean_object* v_inst_1206_){
_start:
{
lean_object* v___f_1207_; 
v___f_1207_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1207_, 0, v_inst_1206_);
return v___f_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad(lean_object* v_00_u03b1_1208_, lean_object* v_cmp_1209_, lean_object* v_m_1210_, lean_object* v_inst_1211_){
_start:
{
lean_object* v___f_1212_; 
v___f_1212_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1212_, 0, v_inst_1211_);
return v___f_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_1213_, lean_object* v_cmp_1214_, lean_object* v_m_1215_, lean_object* v_inst_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_TreeSet_instForInOfMonad(v_00_u03b1_1213_, v_cmp_1214_, v_m_1215_, v_inst_1216_);
lean_dec_ref(v_cmp_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0(lean_object* v_p_1218_, lean_object* v___x_1219_, lean_object* v___x_1220_, lean_object* v_a_1221_, lean_object* v_b_1222_, lean_object* v_acc_1223_){
_start:
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = lean_apply_1(v_p_1218_, v_a_1221_);
v___x_1225_ = lean_unbox(v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1219_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v___x_1219_);
v___x_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1224_);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set(v___x_1228_, 1, v___x_1220_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___lam__0___boxed(lean_object* v_p_1230_, lean_object* v___x_1231_, lean_object* v___x_1232_, lean_object* v_a_1233_, lean_object* v_b_1234_, lean_object* v_acc_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_TreeSet_any___redArg___lam__0(v_p_1230_, v___x_1231_, v___x_1232_, v_a_1233_, v_b_1234_, v_acc_1235_);
lean_dec_ref(v_acc_1235_);
return v_res_1236_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_any___redArg(lean_object* v_t_1240_, lean_object* v_p_1241_){
_start:
{
lean_object* v___y_1243_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___f_1251_; lean_object* v___x_1252_; lean_object* v_a_1253_; 
v___x_1248_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1249_ = lean_box(0);
v___x_1250_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1251_ = lean_alloc_closure((void*)(l_Std_TreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1251_, 0, v_p_1241_);
lean_closure_set(v___f_1251_, 1, v___x_1250_);
lean_closure_set(v___f_1251_, 2, v___x_1249_);
v___x_1252_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1248_, v___f_1251_, v___x_1250_, v_t_1240_);
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___y_1243_ = v_a_1253_;
goto v___jp_1242_;
v___jp_1242_:
{
lean_object* v_fst_1244_; 
v_fst_1244_ = lean_ctor_get(v___y_1243_, 0);
lean_inc(v_fst_1244_);
lean_dec_ref(v___y_1243_);
if (lean_obj_tag(v_fst_1244_) == 0)
{
uint8_t v___x_1245_; 
v___x_1245_ = 0;
return v___x_1245_;
}
else
{
lean_object* v_val_1246_; uint8_t v___x_1247_; 
v_val_1246_ = lean_ctor_get(v_fst_1244_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v_fst_1244_, 1);
v___x_1247_ = lean_unbox(v_val_1246_);
lean_dec(v_val_1246_);
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___redArg___boxed(lean_object* v_t_1254_, lean_object* v_p_1255_){
_start:
{
uint8_t v_res_1256_; lean_object* v_r_1257_; 
v_res_1256_ = l_Std_TreeSet_any___redArg(v_t_1254_, v_p_1255_);
v_r_1257_ = lean_box(v_res_1256_);
return v_r_1257_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_any(lean_object* v_00_u03b1_1258_, lean_object* v_cmp_1259_, lean_object* v_t_1260_, lean_object* v_p_1261_){
_start:
{
lean_object* v___y_1263_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; lean_object* v_a_1273_; 
v___x_1268_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1269_ = lean_box(0);
v___x_1270_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1271_ = lean_alloc_closure((void*)(l_Std_TreeSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1271_, 0, v_p_1261_);
lean_closure_set(v___f_1271_, 1, v___x_1270_);
lean_closure_set(v___f_1271_, 2, v___x_1269_);
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
v___x_1265_ = 0;
return v___x_1265_;
}
else
{
lean_object* v_val_1266_; uint8_t v___x_1267_; 
v_val_1266_ = lean_ctor_get(v_fst_1264_, 0);
lean_inc(v_val_1266_);
lean_dec_ref_known(v_fst_1264_, 1);
v___x_1267_ = lean_unbox(v_val_1266_);
lean_dec(v_val_1266_);
return v___x_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_any___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_cmp_1275_, lean_object* v_t_1276_, lean_object* v_p_1277_){
_start:
{
uint8_t v_res_1278_; lean_object* v_r_1279_; 
v_res_1278_ = l_Std_TreeSet_any(v_00_u03b1_1274_, v_cmp_1275_, v_t_1276_, v_p_1277_);
lean_dec_ref(v_cmp_1275_);
v_r_1279_ = lean_box(v_res_1278_);
return v_r_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0(lean_object* v_p_1280_, lean_object* v___x_1281_, lean_object* v___x_1282_, lean_object* v_a_1283_, lean_object* v_b_1284_, lean_object* v_acc_1285_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___lam__0___boxed(lean_object* v_p_1292_, lean_object* v___x_1293_, lean_object* v___x_1294_, lean_object* v_a_1295_, lean_object* v_b_1296_, lean_object* v_acc_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Std_TreeSet_all___redArg___lam__0(v_p_1292_, v___x_1293_, v___x_1294_, v_a_1295_, v_b_1296_, v_acc_1297_);
lean_dec_ref(v_acc_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_all___redArg(lean_object* v_t_1299_, lean_object* v_p_1300_){
_start:
{
lean_object* v___y_1302_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___f_1310_; lean_object* v___x_1311_; lean_object* v_a_1312_; 
v___x_1307_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1308_ = lean_box(0);
v___x_1309_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1310_ = lean_alloc_closure((void*)(l_Std_TreeSet_all___redArg___lam__0___boxed), 6, 3);
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
lean_dec_ref_known(v_fst_1303_, 1);
v___x_1306_ = lean_unbox(v_val_1305_);
lean_dec(v_val_1305_);
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___redArg___boxed(lean_object* v_t_1313_, lean_object* v_p_1314_){
_start:
{
uint8_t v_res_1315_; lean_object* v_r_1316_; 
v_res_1315_ = l_Std_TreeSet_all___redArg(v_t_1313_, v_p_1314_);
v_r_1316_ = lean_box(v_res_1315_);
return v_r_1316_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_all(lean_object* v_00_u03b1_1317_, lean_object* v_cmp_1318_, lean_object* v_t_1319_, lean_object* v_p_1320_){
_start:
{
lean_object* v___y_1322_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___f_1330_; lean_object* v___x_1331_; lean_object* v_a_1332_; 
v___x_1327_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1328_ = lean_box(0);
v___x_1329_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___f_1330_ = lean_alloc_closure((void*)(l_Std_TreeSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1330_, 0, v_p_1320_);
lean_closure_set(v___f_1330_, 1, v___x_1328_);
lean_closure_set(v___f_1330_, 2, v___x_1329_);
v___x_1331_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1327_, v___f_1330_, v___x_1329_, v_t_1319_);
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___y_1322_ = v_a_1332_;
goto v___jp_1321_;
v___jp_1321_:
{
lean_object* v_fst_1323_; 
v_fst_1323_ = lean_ctor_get(v___y_1322_, 0);
lean_inc(v_fst_1323_);
lean_dec_ref(v___y_1322_);
if (lean_obj_tag(v_fst_1323_) == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = 1;
return v___x_1324_;
}
else
{
lean_object* v_val_1325_; uint8_t v___x_1326_; 
v_val_1325_ = lean_ctor_get(v_fst_1323_, 0);
lean_inc(v_val_1325_);
lean_dec_ref_known(v_fst_1323_, 1);
v___x_1326_ = lean_unbox(v_val_1325_);
lean_dec(v_val_1325_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_all___boxed(lean_object* v_00_u03b1_1333_, lean_object* v_cmp_1334_, lean_object* v_t_1335_, lean_object* v_p_1336_){
_start:
{
uint8_t v_res_1337_; lean_object* v_r_1338_; 
v_res_1337_ = l_Std_TreeSet_all(v_00_u03b1_1333_, v_cmp_1334_, v_t_1335_, v_p_1336_);
lean_dec_ref(v_cmp_1334_);
v_r_1338_ = lean_box(v_res_1337_);
return v_r_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg___lam__0(lean_object* v_x1_1339_, lean_object* v_x2_1340_, lean_object* v_x3_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1342_, 0, v_x1_1339_);
lean_ctor_set(v___x_1342_, 1, v_x3_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___redArg(lean_object* v_t_1344_){
_start:
{
lean_object* v___f_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___f_1345_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___x_1346_ = lean_box(0);
v___x_1347_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1348_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1347_, v___f_1345_, v___x_1346_, v_t_1344_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList(lean_object* v_00_u03b1_1349_, lean_object* v_cmp_1350_, lean_object* v_t_1351_){
_start:
{
lean_object* v___f_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___f_1352_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___x_1353_ = lean_box(0);
v___x_1354_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_1355_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1354_, v___f_1352_, v___x_1353_, v_t_1351_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toList___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_cmp_1357_, lean_object* v_t_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Std_TreeSet_toList(v_00_u03b1_1356_, v_cmp_1357_, v_t_1358_);
lean_dec_ref(v_cmp_1357_);
return v_res_1359_;
}
}
static lean_object* _init_l_Std_TreeSet_ofList___auto__1(void){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__25, &l_Std_TreeSet___auto__1___closed__25_once, _init_l_Std_TreeSet___auto__1___closed__25);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(lean_object* v_cmp_1361_, lean_object* v_k_1362_, lean_object* v_v_1363_, lean_object* v_t_1364_){
_start:
{
if (lean_obj_tag(v_t_1364_) == 0)
{
lean_object* v_size_1365_; lean_object* v_k_1366_; lean_object* v_v_1367_; lean_object* v_l_1368_; lean_object* v_r_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1650_; 
v_size_1365_ = lean_ctor_get(v_t_1364_, 0);
v_k_1366_ = lean_ctor_get(v_t_1364_, 1);
v_v_1367_ = lean_ctor_get(v_t_1364_, 2);
v_l_1368_ = lean_ctor_get(v_t_1364_, 3);
v_r_1369_ = lean_ctor_get(v_t_1364_, 4);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_t_1364_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1371_ = v_t_1364_;
v_isShared_1372_ = v_isSharedCheck_1650_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_r_1369_);
lean_inc(v_l_1368_);
lean_inc(v_v_1367_);
lean_inc(v_k_1366_);
lean_inc(v_size_1365_);
lean_dec(v_t_1364_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1650_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
lean_inc_ref(v_cmp_1361_);
lean_inc(v_k_1366_);
lean_inc(v_k_1362_);
v___x_1373_ = lean_apply_2(v_cmp_1361_, v_k_1362_, v_k_1366_);
v___x_1374_ = lean_unbox(v___x_1373_);
switch(v___x_1374_)
{
case 0:
{
lean_object* v_impl_1375_; lean_object* v___x_1376_; 
lean_dec(v_size_1365_);
v_impl_1375_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1361_, v_k_1362_, v_v_1363_, v_l_1368_);
v___x_1376_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1369_) == 0)
{
lean_object* v_size_1377_; lean_object* v_size_1378_; lean_object* v_k_1379_; lean_object* v_v_1380_; lean_object* v_l_1381_; lean_object* v_r_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_size_1377_ = lean_ctor_get(v_r_1369_, 0);
v_size_1378_ = lean_ctor_get(v_impl_1375_, 0);
v_k_1379_ = lean_ctor_get(v_impl_1375_, 1);
v_v_1380_ = lean_ctor_get(v_impl_1375_, 2);
v_l_1381_ = lean_ctor_get(v_impl_1375_, 3);
v_r_1382_ = lean_ctor_get(v_impl_1375_, 4);
lean_inc(v_r_1382_);
v___x_1383_ = lean_unsigned_to_nat(3u);
v___x_1384_ = lean_nat_mul(v___x_1383_, v_size_1377_);
v___x_1385_ = lean_nat_dec_lt(v___x_1384_, v_size_1378_);
lean_dec(v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_dec(v_r_1382_);
v___x_1386_ = lean_nat_add(v___x_1376_, v_size_1378_);
v___x_1387_ = lean_nat_add(v___x_1386_, v_size_1377_);
lean_dec(v___x_1386_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 3, v_impl_1375_);
lean_ctor_set(v___x_1371_, 0, v___x_1387_);
v___x_1389_ = v___x_1371_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_impl_1375_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_r_1369_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1456_; 
lean_inc(v_l_1381_);
lean_inc(v_v_1380_);
lean_inc(v_k_1379_);
lean_inc(v_size_1378_);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_impl_1375_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; 
v_unused_1457_ = lean_ctor_get(v_impl_1375_, 4);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_impl_1375_, 3);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_impl_1375_, 2);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_impl_1375_, 1);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_impl_1375_, 0);
lean_dec(v_unused_1461_);
v___x_1392_ = v_impl_1375_;
v_isShared_1393_ = v_isSharedCheck_1456_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v_impl_1375_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1456_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_size_1394_; lean_object* v_size_1395_; lean_object* v_k_1396_; lean_object* v_v_1397_; lean_object* v_l_1398_; lean_object* v_r_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_size_1394_ = lean_ctor_get(v_l_1381_, 0);
v_size_1395_ = lean_ctor_get(v_r_1382_, 0);
v_k_1396_ = lean_ctor_get(v_r_1382_, 1);
v_v_1397_ = lean_ctor_get(v_r_1382_, 2);
v_l_1398_ = lean_ctor_get(v_r_1382_, 3);
v_r_1399_ = lean_ctor_get(v_r_1382_, 4);
v___x_1400_ = lean_unsigned_to_nat(2u);
v___x_1401_ = lean_nat_mul(v___x_1400_, v_size_1394_);
v___x_1402_ = lean_nat_dec_lt(v_size_1395_, v___x_1401_);
lean_dec(v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1431_; 
lean_inc(v_r_1399_);
lean_inc(v_l_1398_);
lean_inc(v_v_1397_);
lean_inc(v_k_1396_);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_r_1382_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; lean_object* v_unused_1433_; lean_object* v_unused_1434_; lean_object* v_unused_1435_; lean_object* v_unused_1436_; 
v_unused_1432_ = lean_ctor_get(v_r_1382_, 4);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_r_1382_, 3);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_r_1382_, 2);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_r_1382_, 1);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_r_1382_, 0);
lean_dec(v_unused_1436_);
v___x_1404_ = v_r_1382_;
v_isShared_1405_ = v_isSharedCheck_1431_;
goto v_resetjp_1403_;
}
else
{
lean_dec(v_r_1382_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1431_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___x_1419_; lean_object* v___y_1421_; 
v___x_1406_ = lean_nat_add(v___x_1376_, v_size_1378_);
lean_dec(v_size_1378_);
v___x_1407_ = lean_nat_add(v___x_1406_, v_size_1377_);
lean_dec(v___x_1406_);
v___x_1419_ = lean_nat_add(v___x_1376_, v_size_1394_);
if (lean_obj_tag(v_l_1398_) == 0)
{
lean_object* v_size_1429_; 
v_size_1429_ = lean_ctor_get(v_l_1398_, 0);
lean_inc(v_size_1429_);
v___y_1421_ = v_size_1429_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_unsigned_to_nat(0u);
v___y_1421_ = v___x_1430_;
goto v___jp_1420_;
}
v___jp_1408_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_nat_add(v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec(v___y_1410_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_r_1369_);
lean_ctor_set(v___x_1404_, 3, v_r_1399_);
lean_ctor_set(v___x_1404_, 2, v_v_1367_);
lean_ctor_set(v___x_1404_, 1, v_k_1366_);
lean_ctor_set(v___x_1404_, 0, v___x_1412_);
v___x_1414_ = v___x_1404_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v_r_1399_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v_r_1369_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v___x_1414_);
lean_ctor_set(v___x_1392_, 3, v___y_1409_);
lean_ctor_set(v___x_1392_, 2, v_v_1397_);
lean_ctor_set(v___x_1392_, 1, v_k_1396_);
lean_ctor_set(v___x_1392_, 0, v___x_1407_);
v___x_1416_ = v___x_1392_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1396_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1397_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v___y_1409_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
v___jp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_nat_add(v___x_1419_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec(v___x_1419_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_l_1398_);
lean_ctor_set(v___x_1371_, 3, v_l_1381_);
lean_ctor_set(v___x_1371_, 2, v_v_1380_);
lean_ctor_set(v___x_1371_, 1, v_k_1379_);
lean_ctor_set(v___x_1371_, 0, v___x_1422_);
v___x_1424_ = v___x_1371_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_k_1379_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_v_1380_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_l_1381_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v_l_1398_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_nat_add(v___x_1376_, v_size_1377_);
if (lean_obj_tag(v_r_1399_) == 0)
{
lean_object* v_size_1426_; 
v_size_1426_ = lean_ctor_get(v_r_1399_, 0);
lean_inc(v_size_1426_);
v___y_1409_ = v___x_1424_;
v___y_1410_ = v___x_1425_;
v___y_1411_ = v_size_1426_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___y_1409_ = v___x_1424_;
v___y_1410_ = v___x_1425_;
v___y_1411_ = v___x_1427_;
goto v___jp_1408_;
}
}
}
}
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
lean_del_object(v___x_1371_);
v___x_1437_ = lean_nat_add(v___x_1376_, v_size_1378_);
lean_dec(v_size_1378_);
v___x_1438_ = lean_nat_add(v___x_1437_, v_size_1377_);
lean_dec(v___x_1437_);
v___x_1439_ = lean_nat_add(v___x_1376_, v_size_1377_);
v___x_1440_ = lean_nat_add(v___x_1439_, v_size_1395_);
lean_dec(v___x_1439_);
lean_inc_ref(v_r_1369_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_r_1369_);
lean_ctor_set(v___x_1392_, 3, v_r_1382_);
lean_ctor_set(v___x_1392_, 2, v_v_1367_);
lean_ctor_set(v___x_1392_, 1, v_k_1366_);
lean_ctor_set(v___x_1392_, 0, v___x_1440_);
v___x_1442_ = v___x_1392_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_r_1382_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_r_1369_);
v___x_1442_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_isSharedCheck_1449_ = !lean_is_exclusive(v_r_1369_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; 
v_unused_1450_ = lean_ctor_get(v_r_1369_, 4);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_r_1369_, 3);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_r_1369_, 2);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_r_1369_, 1);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_r_1369_, 0);
lean_dec(v_unused_1454_);
v___x_1444_ = v_r_1369_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v_r_1369_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 4, v___x_1442_);
lean_ctor_set(v___x_1444_, 3, v_l_1381_);
lean_ctor_set(v___x_1444_, 2, v_v_1380_);
lean_ctor_set(v___x_1444_, 1, v_k_1379_);
lean_ctor_set(v___x_1444_, 0, v___x_1438_);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_k_1379_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_v_1380_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_l_1381_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v___x_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1462_; 
v_l_1462_ = lean_ctor_get(v_impl_1375_, 3);
if (lean_obj_tag(v_l_1462_) == 0)
{
lean_object* v_r_1463_; lean_object* v_k_1464_; lean_object* v_v_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1476_; 
lean_inc_ref(v_l_1462_);
v_r_1463_ = lean_ctor_get(v_impl_1375_, 4);
v_k_1464_ = lean_ctor_get(v_impl_1375_, 1);
v_v_1465_ = lean_ctor_get(v_impl_1375_, 2);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_impl_1375_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; lean_object* v_unused_1478_; 
v_unused_1477_ = lean_ctor_get(v_impl_1375_, 3);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_impl_1375_, 0);
lean_dec(v_unused_1478_);
v___x_1467_ = v_impl_1375_;
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_r_1463_);
lean_inc(v_v_1465_);
lean_inc(v_k_1464_);
lean_dec(v_impl_1375_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1469_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1463_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 3, v_r_1463_);
lean_ctor_set(v___x_1467_, 2, v_v_1367_);
lean_ctor_set(v___x_1467_, 1, v_k_1366_);
lean_ctor_set(v___x_1467_, 0, v___x_1376_);
v___x_1471_ = v___x_1467_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_r_1463_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_r_1463_);
v___x_1471_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1473_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v___x_1471_);
lean_ctor_set(v___x_1371_, 3, v_l_1462_);
lean_ctor_set(v___x_1371_, 2, v_v_1465_);
lean_ctor_set(v___x_1371_, 1, v_k_1464_);
lean_ctor_set(v___x_1371_, 0, v___x_1469_);
v___x_1473_ = v___x_1371_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_k_1464_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_v_1465_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_l_1462_);
lean_ctor_set(v_reuseFailAlloc_1474_, 4, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_object* v_r_1479_; 
v_r_1479_ = lean_ctor_get(v_impl_1375_, 4);
lean_inc(v_r_1479_);
if (lean_obj_tag(v_r_1479_) == 0)
{
lean_object* v_k_1480_; lean_object* v_v_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1504_; 
lean_inc(v_l_1462_);
v_k_1480_ = lean_ctor_get(v_impl_1375_, 1);
v_v_1481_ = lean_ctor_get(v_impl_1375_, 2);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_impl_1375_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; 
v_unused_1505_ = lean_ctor_get(v_impl_1375_, 4);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_impl_1375_, 3);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_impl_1375_, 0);
lean_dec(v_unused_1507_);
v___x_1483_ = v_impl_1375_;
v_isShared_1484_ = v_isSharedCheck_1504_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_v_1481_);
lean_inc(v_k_1480_);
lean_dec(v_impl_1375_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1504_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_k_1485_; lean_object* v_v_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1500_; 
v_k_1485_ = lean_ctor_get(v_r_1479_, 1);
v_v_1486_ = lean_ctor_get(v_r_1479_, 2);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_r_1479_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; 
v_unused_1501_ = lean_ctor_get(v_r_1479_, 4);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_r_1479_, 3);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_r_1479_, 0);
lean_dec(v_unused_1503_);
v___x_1488_ = v_r_1479_;
v_isShared_1489_ = v_isSharedCheck_1500_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_v_1486_);
lean_inc(v_k_1485_);
lean_dec(v_r_1479_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1500_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = lean_unsigned_to_nat(3u);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 4, v_l_1462_);
lean_ctor_set(v___x_1488_, 3, v_l_1462_);
lean_ctor_set(v___x_1488_, 2, v_v_1481_);
lean_ctor_set(v___x_1488_, 1, v_k_1480_);
lean_ctor_set(v___x_1488_, 0, v___x_1376_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1480_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1481_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_l_1462_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_l_1462_);
v___x_1492_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1494_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v_l_1462_);
lean_ctor_set(v___x_1483_, 2, v_v_1367_);
lean_ctor_set(v___x_1483_, 1, v_k_1366_);
lean_ctor_set(v___x_1483_, 0, v___x_1376_);
v___x_1494_ = v___x_1483_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_l_1462_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v_l_1462_);
v___x_1494_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v___x_1494_);
lean_ctor_set(v___x_1371_, 3, v___x_1492_);
lean_ctor_set(v___x_1371_, 2, v_v_1486_);
lean_ctor_set(v___x_1371_, 1, v_k_1485_);
lean_ctor_set(v___x_1371_, 0, v___x_1490_);
v___x_1496_ = v___x_1371_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_k_1485_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_v_1486_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v___x_1494_);
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
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1508_ = lean_unsigned_to_nat(2u);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_r_1479_);
lean_ctor_set(v___x_1371_, 3, v_impl_1375_);
lean_ctor_set(v___x_1371_, 0, v___x_1508_);
v___x_1510_ = v___x_1371_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_impl_1375_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_r_1479_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1513_; 
lean_dec(v_v_1367_);
lean_dec(v_k_1366_);
lean_dec_ref(v_cmp_1361_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 2, v_v_1363_);
lean_ctor_set(v___x_1371_, 1, v_k_1362_);
v___x_1513_ = v___x_1371_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_size_1365_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_k_1362_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1363_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_l_1368_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_r_1369_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
default: 
{
lean_object* v_impl_1515_; lean_object* v___x_1516_; 
lean_dec(v_size_1365_);
v_impl_1515_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1361_, v_k_1362_, v_v_1363_, v_r_1369_);
v___x_1516_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1368_) == 0)
{
lean_object* v_size_1517_; lean_object* v_size_1518_; lean_object* v_k_1519_; lean_object* v_v_1520_; lean_object* v_l_1521_; lean_object* v_r_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v_size_1517_ = lean_ctor_get(v_l_1368_, 0);
v_size_1518_ = lean_ctor_get(v_impl_1515_, 0);
v_k_1519_ = lean_ctor_get(v_impl_1515_, 1);
v_v_1520_ = lean_ctor_get(v_impl_1515_, 2);
v_l_1521_ = lean_ctor_get(v_impl_1515_, 3);
lean_inc(v_l_1521_);
v_r_1522_ = lean_ctor_get(v_impl_1515_, 4);
v___x_1523_ = lean_unsigned_to_nat(3u);
v___x_1524_ = lean_nat_mul(v___x_1523_, v_size_1517_);
v___x_1525_ = lean_nat_dec_lt(v___x_1524_, v_size_1518_);
lean_dec(v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
lean_dec(v_l_1521_);
v___x_1526_ = lean_nat_add(v___x_1516_, v_size_1517_);
v___x_1527_ = lean_nat_add(v___x_1526_, v_size_1518_);
lean_dec(v___x_1526_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_impl_1515_);
lean_ctor_set(v___x_1371_, 0, v___x_1527_);
v___x_1529_ = v___x_1371_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_l_1368_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_impl_1515_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
else
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1594_; 
lean_inc(v_r_1522_);
lean_inc(v_v_1520_);
lean_inc(v_k_1519_);
lean_inc(v_size_1518_);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_impl_1515_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; lean_object* v_unused_1596_; lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; 
v_unused_1595_ = lean_ctor_get(v_impl_1515_, 4);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_impl_1515_, 3);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_impl_1515_, 2);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_impl_1515_, 1);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_impl_1515_, 0);
lean_dec(v_unused_1599_);
v___x_1532_ = v_impl_1515_;
v_isShared_1533_ = v_isSharedCheck_1594_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v_impl_1515_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1594_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v_size_1534_; lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v_l_1537_; lean_object* v_r_1538_; lean_object* v_size_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v_size_1534_ = lean_ctor_get(v_l_1521_, 0);
v_k_1535_ = lean_ctor_get(v_l_1521_, 1);
v_v_1536_ = lean_ctor_get(v_l_1521_, 2);
v_l_1537_ = lean_ctor_get(v_l_1521_, 3);
v_r_1538_ = lean_ctor_get(v_l_1521_, 4);
v_size_1539_ = lean_ctor_get(v_r_1522_, 0);
v___x_1540_ = lean_unsigned_to_nat(2u);
v___x_1541_ = lean_nat_mul(v___x_1540_, v_size_1539_);
v___x_1542_ = lean_nat_dec_lt(v_size_1534_, v___x_1541_);
lean_dec(v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1570_; 
lean_inc(v_r_1538_);
lean_inc(v_l_1537_);
lean_inc(v_v_1536_);
lean_inc(v_k_1535_);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_l_1521_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; lean_object* v_unused_1572_; lean_object* v_unused_1573_; lean_object* v_unused_1574_; lean_object* v_unused_1575_; 
v_unused_1571_ = lean_ctor_get(v_l_1521_, 4);
lean_dec(v_unused_1571_);
v_unused_1572_ = lean_ctor_get(v_l_1521_, 3);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v_l_1521_, 2);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v_l_1521_, 1);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_l_1521_, 0);
lean_dec(v_unused_1575_);
v___x_1544_ = v_l_1521_;
v_isShared_1545_ = v_isSharedCheck_1570_;
goto v_resetjp_1543_;
}
else
{
lean_dec(v_l_1521_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1570_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1560_; 
v___x_1546_ = lean_nat_add(v___x_1516_, v_size_1517_);
v___x_1547_ = lean_nat_add(v___x_1546_, v_size_1518_);
lean_dec(v_size_1518_);
if (lean_obj_tag(v_l_1537_) == 0)
{
lean_object* v_size_1568_; 
v_size_1568_ = lean_ctor_get(v_l_1537_, 0);
lean_inc(v_size_1568_);
v___y_1560_ = v_size_1568_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_unsigned_to_nat(0u);
v___y_1560_ = v___x_1569_;
goto v___jp_1559_;
}
v___jp_1548_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = lean_nat_add(v___y_1549_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec(v___y_1549_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 4, v_r_1522_);
lean_ctor_set(v___x_1544_, 3, v_r_1538_);
lean_ctor_set(v___x_1544_, 2, v_v_1520_);
lean_ctor_set(v___x_1544_, 1, v_k_1519_);
lean_ctor_set(v___x_1544_, 0, v___x_1552_);
v___x_1554_ = v___x_1544_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1519_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1520_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_r_1538_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1522_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 4, v___x_1554_);
lean_ctor_set(v___x_1532_, 3, v___y_1550_);
lean_ctor_set(v___x_1532_, 2, v_v_1536_);
lean_ctor_set(v___x_1532_, 1, v_k_1535_);
lean_ctor_set(v___x_1532_, 0, v___x_1547_);
v___x_1556_ = v___x_1532_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_k_1535_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_v_1536_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v___y_1550_);
lean_ctor_set(v_reuseFailAlloc_1557_, 4, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
v___jp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = lean_nat_add(v___x_1546_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec(v___x_1546_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_l_1537_);
lean_ctor_set(v___x_1371_, 0, v___x_1561_);
v___x_1563_ = v___x_1371_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_l_1368_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_l_1537_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_nat_add(v___x_1516_, v_size_1539_);
if (lean_obj_tag(v_r_1538_) == 0)
{
lean_object* v_size_1565_; 
v_size_1565_ = lean_ctor_get(v_r_1538_, 0);
lean_inc(v_size_1565_);
v___y_1549_ = v___x_1564_;
v___y_1550_ = v___x_1563_;
v___y_1551_ = v_size_1565_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_unsigned_to_nat(0u);
v___y_1549_ = v___x_1564_;
v___y_1550_ = v___x_1563_;
v___y_1551_ = v___x_1566_;
goto v___jp_1548_;
}
}
}
}
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_del_object(v___x_1371_);
v___x_1576_ = lean_nat_add(v___x_1516_, v_size_1517_);
v___x_1577_ = lean_nat_add(v___x_1576_, v_size_1518_);
lean_dec(v_size_1518_);
v___x_1578_ = lean_nat_add(v___x_1576_, v_size_1534_);
lean_dec(v___x_1576_);
lean_inc_ref(v_l_1368_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 4, v_l_1521_);
lean_ctor_set(v___x_1532_, 3, v_l_1368_);
lean_ctor_set(v___x_1532_, 2, v_v_1367_);
lean_ctor_set(v___x_1532_, 1, v_k_1366_);
lean_ctor_set(v___x_1532_, 0, v___x_1578_);
v___x_1580_ = v___x_1532_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_l_1368_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_l_1521_);
v___x_1580_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
v_isSharedCheck_1587_ = !lean_is_exclusive(v_l_1368_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; lean_object* v_unused_1589_; lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; 
v_unused_1588_ = lean_ctor_get(v_l_1368_, 4);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_l_1368_, 3);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_l_1368_, 2);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_l_1368_, 1);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_l_1368_, 0);
lean_dec(v_unused_1592_);
v___x_1582_ = v_l_1368_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v_l_1368_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 4, v_r_1522_);
lean_ctor_set(v___x_1582_, 3, v___x_1580_);
lean_ctor_set(v___x_1582_, 2, v_v_1520_);
lean_ctor_set(v___x_1582_, 1, v_k_1519_);
lean_ctor_set(v___x_1582_, 0, v___x_1577_);
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_k_1519_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_v_1520_);
lean_ctor_set(v_reuseFailAlloc_1586_, 3, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1586_, 4, v_r_1522_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1600_; 
v_l_1600_ = lean_ctor_get(v_impl_1515_, 3);
lean_inc(v_l_1600_);
if (lean_obj_tag(v_l_1600_) == 0)
{
lean_object* v_r_1601_; lean_object* v_k_1602_; lean_object* v_v_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1626_; 
v_r_1601_ = lean_ctor_get(v_impl_1515_, 4);
v_k_1602_ = lean_ctor_get(v_impl_1515_, 1);
v_v_1603_ = lean_ctor_get(v_impl_1515_, 2);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_impl_1515_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; lean_object* v_unused_1628_; 
v_unused_1627_ = lean_ctor_get(v_impl_1515_, 3);
lean_dec(v_unused_1627_);
v_unused_1628_ = lean_ctor_get(v_impl_1515_, 0);
lean_dec(v_unused_1628_);
v___x_1605_ = v_impl_1515_;
v_isShared_1606_ = v_isSharedCheck_1626_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_r_1601_);
lean_inc(v_v_1603_);
lean_inc(v_k_1602_);
lean_dec(v_impl_1515_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1626_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v_k_1607_; lean_object* v_v_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1622_; 
v_k_1607_ = lean_ctor_get(v_l_1600_, 1);
v_v_1608_ = lean_ctor_get(v_l_1600_, 2);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_l_1600_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; lean_object* v_unused_1624_; lean_object* v_unused_1625_; 
v_unused_1623_ = lean_ctor_get(v_l_1600_, 4);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_l_1600_, 3);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_l_1600_, 0);
lean_dec(v_unused_1625_);
v___x_1610_ = v_l_1600_;
v_isShared_1611_ = v_isSharedCheck_1622_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_v_1608_);
lean_inc(v_k_1607_);
lean_dec(v_l_1600_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1622_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1601_, 2);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 4, v_r_1601_);
lean_ctor_set(v___x_1610_, 3, v_r_1601_);
lean_ctor_set(v___x_1610_, 2, v_v_1367_);
lean_ctor_set(v___x_1610_, 1, v_k_1366_);
lean_ctor_set(v___x_1610_, 0, v___x_1516_);
v___x_1614_ = v___x_1610_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1621_, 3, v_r_1601_);
lean_ctor_set(v_reuseFailAlloc_1621_, 4, v_r_1601_);
v___x_1614_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1616_; 
lean_inc(v_r_1601_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 3, v_r_1601_);
lean_ctor_set(v___x_1605_, 0, v___x_1516_);
v___x_1616_ = v___x_1605_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_k_1602_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_v_1603_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v_r_1601_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v_r_1601_);
v___x_1616_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1618_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v___x_1616_);
lean_ctor_set(v___x_1371_, 3, v___x_1614_);
lean_ctor_set(v___x_1371_, 2, v_v_1608_);
lean_ctor_set(v___x_1371_, 1, v_k_1607_);
lean_ctor_set(v___x_1371_, 0, v___x_1612_);
v___x_1618_ = v___x_1371_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_k_1607_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_v_1608_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v___x_1616_);
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
else
{
lean_object* v_r_1629_; 
v_r_1629_ = lean_ctor_get(v_impl_1515_, 4);
lean_inc(v_r_1629_);
if (lean_obj_tag(v_r_1629_) == 0)
{
lean_object* v_k_1630_; lean_object* v_v_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1642_; 
v_k_1630_ = lean_ctor_get(v_impl_1515_, 1);
v_v_1631_ = lean_ctor_get(v_impl_1515_, 2);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_impl_1515_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; lean_object* v_unused_1644_; lean_object* v_unused_1645_; 
v_unused_1643_ = lean_ctor_get(v_impl_1515_, 4);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_impl_1515_, 3);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_impl_1515_, 0);
lean_dec(v_unused_1645_);
v___x_1633_ = v_impl_1515_;
v_isShared_1634_ = v_isSharedCheck_1642_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_v_1631_);
lean_inc(v_k_1630_);
lean_dec(v_impl_1515_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1642_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1635_ = lean_unsigned_to_nat(3u);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 4, v_l_1600_);
lean_ctor_set(v___x_1633_, 2, v_v_1367_);
lean_ctor_set(v___x_1633_, 1, v_k_1366_);
lean_ctor_set(v___x_1633_, 0, v___x_1516_);
v___x_1637_ = v___x_1633_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_l_1600_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_l_1600_);
v___x_1637_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_r_1629_);
lean_ctor_set(v___x_1371_, 3, v___x_1637_);
lean_ctor_set(v___x_1371_, 2, v_v_1631_);
lean_ctor_set(v___x_1371_, 1, v_k_1630_);
lean_ctor_set(v___x_1371_, 0, v___x_1635_);
v___x_1639_ = v___x_1371_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_k_1630_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_v_1631_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_r_1629_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = lean_unsigned_to_nat(2u);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v_impl_1515_);
lean_ctor_set(v___x_1371_, 3, v_r_1629_);
lean_ctor_set(v___x_1371_, 0, v___x_1646_);
v___x_1648_ = v___x_1371_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1649_, 3, v_r_1629_);
lean_ctor_set(v_reuseFailAlloc_1649_, 4, v_impl_1515_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
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
lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec_ref(v_cmp_1361_);
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v_k_1362_);
lean_ctor_set(v___x_1652_, 2, v_v_1363_);
lean_ctor_set(v___x_1652_, 3, v_t_1364_);
lean_ctor_set(v___x_1652_, 4, v_t_1364_);
return v___x_1652_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(lean_object* v_cmp_1653_, lean_object* v_k_1654_, lean_object* v_t_1655_){
_start:
{
if (lean_obj_tag(v_t_1655_) == 0)
{
lean_object* v_k_1656_; lean_object* v_l_1657_; lean_object* v_r_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v_k_1656_ = lean_ctor_get(v_t_1655_, 1);
lean_inc(v_k_1656_);
v_l_1657_ = lean_ctor_get(v_t_1655_, 3);
lean_inc(v_l_1657_);
v_r_1658_ = lean_ctor_get(v_t_1655_, 4);
lean_inc(v_r_1658_);
lean_dec_ref_known(v_t_1655_, 5);
lean_inc_ref(v_cmp_1653_);
lean_inc(v_k_1654_);
v___x_1659_ = lean_apply_2(v_cmp_1653_, v_k_1654_, v_k_1656_);
v___x_1660_ = lean_unbox(v___x_1659_);
switch(v___x_1660_)
{
case 0:
{
lean_dec(v_r_1658_);
v_t_1655_ = v_l_1657_;
goto _start;
}
case 1:
{
uint8_t v___x_1662_; 
lean_dec(v_r_1658_);
lean_dec(v_l_1657_);
lean_dec(v_k_1654_);
lean_dec_ref(v_cmp_1653_);
v___x_1662_ = 1;
return v___x_1662_;
}
default: 
{
lean_dec(v_l_1657_);
v_t_1655_ = v_r_1658_;
goto _start;
}
}
}
else
{
uint8_t v___x_1664_; 
lean_dec(v_k_1654_);
lean_dec_ref(v_cmp_1653_);
v___x_1664_ = 0;
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg___boxed(lean_object* v_cmp_1665_, lean_object* v_k_1666_, lean_object* v_t_1667_){
_start:
{
uint8_t v_res_1668_; lean_object* v_r_1669_; 
v_res_1668_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1665_, v_k_1666_, v_t_1667_);
v_r_1669_ = lean_box(v_res_1668_);
return v_r_1669_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(lean_object* v_cmp_1670_, lean_object* v_as_x27_1671_, lean_object* v_b_1672_){
_start:
{
if (lean_obj_tag(v_as_x27_1671_) == 0)
{
lean_dec_ref(v_cmp_1670_);
return v_b_1672_;
}
else
{
lean_object* v_head_1673_; lean_object* v_tail_1674_; uint8_t v___x_1675_; 
v_head_1673_ = lean_ctor_get(v_as_x27_1671_, 0);
v_tail_1674_ = lean_ctor_get(v_as_x27_1671_, 1);
lean_inc(v_b_1672_);
lean_inc(v_head_1673_);
lean_inc_ref(v_cmp_1670_);
v___x_1675_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1670_, v_head_1673_, v_b_1672_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_box(0);
lean_inc(v_head_1673_);
lean_inc_ref(v_cmp_1670_);
v___x_1677_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1670_, v_head_1673_, v___x_1676_, v_b_1672_);
v_as_x27_1671_ = v_tail_1674_;
v_b_1672_ = v___x_1677_;
goto _start;
}
else
{
v_as_x27_1671_ = v_tail_1674_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg___boxed(lean_object* v_cmp_1680_, lean_object* v_as_x27_1681_, lean_object* v_b_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1680_, v_as_x27_1681_, v_b_1682_);
lean_dec(v_as_x27_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___redArg(lean_object* v_l_1684_, lean_object* v_cmp_1685_){
_start:
{
lean_object* v_r_1686_; lean_object* v___x_1687_; 
v_r_1686_ = lean_box(1);
v___x_1687_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1685_, v_l_1684_, v_r_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___redArg___boxed(lean_object* v_l_1688_, lean_object* v_cmp_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_TreeSet_ofList___redArg(v_l_1688_, v_cmp_1689_);
lean_dec(v_l_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList(lean_object* v_00_u03b1_1691_, lean_object* v_l_1692_, lean_object* v_cmp_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Std_TreeSet_ofList___redArg(v_l_1692_, v_cmp_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofList___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_l_1696_, lean_object* v_cmp_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Std_TreeSet_ofList(v_00_u03b1_1695_, v_l_1696_, v_cmp_1697_);
lean_dec(v_l_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(lean_object* v_00_u03b1_1699_, lean_object* v_cmp_1700_, lean_object* v_00_u03b2_1701_, lean_object* v_k_1702_, lean_object* v_t_1703_){
_start:
{
uint8_t v___x_1704_; 
v___x_1704_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1700_, v_k_1702_, v_t_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___boxed(lean_object* v_00_u03b1_1705_, lean_object* v_cmp_1706_, lean_object* v_00_u03b2_1707_, lean_object* v_k_1708_, lean_object* v_t_1709_){
_start:
{
uint8_t v_res_1710_; lean_object* v_r_1711_; 
v_res_1710_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(v_00_u03b1_1705_, v_cmp_1706_, v_00_u03b2_1707_, v_k_1708_, v_t_1709_);
v_r_1711_ = lean_box(v_res_1710_);
return v_r_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1(lean_object* v_00_u03b1_1712_, lean_object* v_cmp_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_k_1715_, lean_object* v_v_1716_, lean_object* v_t_1717_, lean_object* v_hl_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1713_, v_k_1715_, v_v_1716_, v_t_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(lean_object* v_00_u03b1_1720_, lean_object* v_cmp_1721_, lean_object* v_as_1722_, lean_object* v_as_x27_1723_, lean_object* v_b_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(v_cmp_1721_, v_as_x27_1723_, v_b_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___boxed(lean_object* v_00_u03b1_1727_, lean_object* v_cmp_1728_, lean_object* v_as_1729_, lean_object* v_as_x27_1730_, lean_object* v_b_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(v_00_u03b1_1727_, v_cmp_1728_, v_as_1729_, v_as_x27_1730_, v_b_1731_, v_a_1732_);
lean_dec(v_as_x27_1730_);
lean_dec(v_as_1729_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg___lam__0(lean_object* v_l_1734_, lean_object* v_k_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_array_push(v_l_1734_, v_k_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___redArg(lean_object* v_t_1739_){
_start:
{
lean_object* v___f_1740_; lean_object* v___y_1742_; 
v___f_1740_ = ((lean_object*)(l_Std_TreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1739_) == 0)
{
lean_object* v_size_1745_; 
v_size_1745_ = lean_ctor_get(v_t_1739_, 0);
lean_inc(v_size_1745_);
v___y_1742_ = v_size_1745_;
goto v___jp_1741_;
}
else
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_unsigned_to_nat(0u);
v___y_1742_ = v___x_1746_;
goto v___jp_1741_;
}
v___jp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_mk_empty_array_with_capacity(v___y_1742_);
lean_dec(v___y_1742_);
v___x_1744_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1740_, v___x_1743_, v_t_1739_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray(lean_object* v_00_u03b1_1747_, lean_object* v_cmp_1748_, lean_object* v_t_1749_){
_start:
{
lean_object* v___f_1750_; lean_object* v___y_1752_; 
v___f_1750_ = ((lean_object*)(l_Std_TreeSet_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1749_) == 0)
{
lean_object* v_size_1755_; 
v_size_1755_ = lean_ctor_get(v_t_1749_, 0);
lean_inc(v_size_1755_);
v___y_1752_ = v_size_1755_;
goto v___jp_1751_;
}
else
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_unsigned_to_nat(0u);
v___y_1752_ = v___x_1756_;
goto v___jp_1751_;
}
v___jp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_mk_empty_array_with_capacity(v___y_1752_);
lean_dec(v___y_1752_);
v___x_1754_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1750_, v___x_1753_, v_t_1749_);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_toArray___boxed(lean_object* v_00_u03b1_1757_, lean_object* v_cmp_1758_, lean_object* v_t_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Std_TreeSet_toArray(v_00_u03b1_1757_, v_cmp_1758_, v_t_1759_);
lean_dec_ref(v_cmp_1758_);
return v_res_1760_;
}
}
static lean_object* _init_l_Std_TreeSet_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_obj_once(&l_Std_TreeSet___auto__1___closed__25, &l_Std_TreeSet___auto__1___closed__25_once, _init_l_Std_TreeSet___auto__1___closed__25);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(lean_object* v_cmp_1762_, lean_object* v_as_1763_, size_t v_sz_1764_, size_t v_i_1765_, lean_object* v_b_1766_){
_start:
{
lean_object* v___y_1768_; uint8_t v___x_1772_; 
v___x_1772_ = lean_usize_dec_lt(v_i_1765_, v_sz_1764_);
if (v___x_1772_ == 0)
{
lean_dec_ref(v_cmp_1762_);
return v_b_1766_;
}
else
{
lean_object* v_a_1773_; uint8_t v___x_1774_; 
v_a_1773_ = lean_array_uget_borrowed(v_as_1763_, v_i_1765_);
lean_inc(v_b_1766_);
lean_inc(v_a_1773_);
lean_inc_ref(v_cmp_1762_);
v___x_1774_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_1762_, v_a_1773_, v_b_1766_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = lean_box(0);
lean_inc(v_a_1773_);
lean_inc_ref(v_cmp_1762_);
v___x_1776_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_1762_, v_a_1773_, v___x_1775_, v_b_1766_);
v___y_1768_ = v___x_1776_;
goto v___jp_1767_;
}
else
{
v___y_1768_ = v_b_1766_;
goto v___jp_1767_;
}
}
v___jp_1767_:
{
size_t v___x_1769_; size_t v___x_1770_; 
v___x_1769_ = ((size_t)1ULL);
v___x_1770_ = lean_usize_add(v_i_1765_, v___x_1769_);
v_i_1765_ = v___x_1770_;
v_b_1766_ = v___y_1768_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg___boxed(lean_object* v_cmp_1777_, lean_object* v_as_1778_, lean_object* v_sz_1779_, lean_object* v_i_1780_, lean_object* v_b_1781_){
_start:
{
size_t v_sz_boxed_1782_; size_t v_i_boxed_1783_; lean_object* v_res_1784_; 
v_sz_boxed_1782_ = lean_unbox_usize(v_sz_1779_);
lean_dec(v_sz_1779_);
v_i_boxed_1783_ = lean_unbox_usize(v_i_1780_);
lean_dec(v_i_1780_);
v_res_1784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1777_, v_as_1778_, v_sz_boxed_1782_, v_i_boxed_1783_, v_b_1781_);
lean_dec_ref(v_as_1778_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg(lean_object* v_a_1785_, lean_object* v_cmp_1786_){
_start:
{
lean_object* v_r_1787_; size_t v_sz_1788_; size_t v___x_1789_; lean_object* v___x_1790_; 
v_r_1787_ = lean_box(1);
v_sz_1788_ = lean_array_size(v_a_1785_);
v___x_1789_ = ((size_t)0ULL);
v___x_1790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1786_, v_a_1785_, v_sz_1788_, v___x_1789_, v_r_1787_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___redArg___boxed(lean_object* v_a_1791_, lean_object* v_cmp_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Std_TreeSet_ofArray___redArg(v_a_1791_, v_cmp_1792_);
lean_dec_ref(v_a_1791_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray(lean_object* v_00_u03b1_1794_, lean_object* v_a_1795_, lean_object* v_cmp_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Std_TreeSet_ofArray___redArg(v_a_1795_, v_cmp_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_ofArray___boxed(lean_object* v_00_u03b1_1798_, lean_object* v_a_1799_, lean_object* v_cmp_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Std_TreeSet_ofArray(v_00_u03b1_1798_, v_a_1799_, v_cmp_1800_);
lean_dec_ref(v_a_1799_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(lean_object* v_00_u03b1_1802_, lean_object* v_cmp_1803_, lean_object* v_as_1804_, size_t v_sz_1805_, size_t v_i_1806_, lean_object* v_b_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_1803_, v_as_1804_, v_sz_1805_, v_i_1806_, v_b_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___boxed(lean_object* v_00_u03b1_1809_, lean_object* v_cmp_1810_, lean_object* v_as_1811_, lean_object* v_sz_1812_, lean_object* v_i_1813_, lean_object* v_b_1814_){
_start:
{
size_t v_sz_boxed_1815_; size_t v_i_boxed_1816_; lean_object* v_res_1817_; 
v_sz_boxed_1815_ = lean_unbox_usize(v_sz_1812_);
lean_dec(v_sz_1812_);
v_i_boxed_1816_ = lean_unbox_usize(v_i_1813_);
lean_dec(v_i_1813_);
v_res_1817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(v_00_u03b1_1809_, v_cmp_1810_, v_as_1811_, v_sz_boxed_1815_, v_i_boxed_1816_, v_b_1814_);
lean_dec_ref(v_as_1811_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0(lean_object* v_b_u2082_1820_, lean_object* v_x_1821_){
_start:
{
if (lean_obj_tag(v_x_1821_) == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_b_u2082_1820_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; 
v___x_1823_ = ((lean_object*)(l_Std_TreeSet_merge___redArg___lam__0___closed__0));
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1824_, lean_object* v_x_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Std_TreeSet_merge___redArg___lam__0(v_b_u2082_1824_, v_x_1825_);
lean_dec(v_x_1825_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg___lam__1(lean_object* v_cmp_1827_, lean_object* v_t_1828_, lean_object* v_a_1829_, lean_object* v_b_u2082_1830_){
_start:
{
lean_object* v___f_1831_; lean_object* v___x_1832_; 
v___f_1831_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1831_, 0, v_b_u2082_1830_);
v___x_1832_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_1827_, v_a_1829_, v___f_1831_, v_t_1828_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge___redArg(lean_object* v_cmp_1833_, lean_object* v_t_u2081_1834_, lean_object* v_t_u2082_1835_){
_start:
{
lean_object* v___f_1836_; lean_object* v___x_1837_; 
v___f_1836_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1836_, 0, v_cmp_1833_);
v___x_1837_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1836_, v_t_u2081_1834_, v_t_u2082_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_merge(lean_object* v_00_u03b1_1838_, lean_object* v_cmp_1839_, lean_object* v_t_u2081_1840_, lean_object* v_t_u2082_1841_){
_start:
{
lean_object* v___f_1842_; lean_object* v___x_1843_; 
v___f_1842_ = lean_alloc_closure((void*)(l_Std_TreeSet_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1842_, 0, v_cmp_1839_);
v___x_1843_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1842_, v_t_u2081_1840_, v_t_u2082_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg___lam__0(lean_object* v_cmp_1844_, lean_object* v_a_1845_, lean_object* v_____s_1846_){
_start:
{
uint8_t v___x_1847_; 
lean_inc(v_____s_1846_);
lean_inc(v_a_1845_);
lean_inc_ref(v_cmp_1844_);
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1844_, v_a_1845_, v_____s_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_box(0);
v___x_1849_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1844_, v_a_1845_, v___x_1848_, v_____s_1846_);
v___x_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; 
lean_dec(v_a_1845_);
lean_dec_ref(v_cmp_1844_);
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_____s_1846_);
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany___redArg(lean_object* v_cmp_1852_, lean_object* v_inst_1853_, lean_object* v_t_1854_, lean_object* v_l_1855_){
_start:
{
lean_object* v___f_1856_; lean_object* v___x_1857_; 
v___f_1856_ = lean_alloc_closure((void*)(l_Std_TreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1856_, 0, v_cmp_1852_);
v___x_1857_ = lean_apply_4(v_inst_1853_, lean_box(0), v_l_1855_, v_t_1854_, v___f_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_insertMany(lean_object* v_00_u03b1_1858_, lean_object* v_cmp_1859_, lean_object* v_00_u03c1_1860_, lean_object* v_inst_1861_, lean_object* v_t_1862_, lean_object* v_l_1863_){
_start:
{
lean_object* v___f_1864_; lean_object* v___x_1865_; 
v___f_1864_ = lean_alloc_closure((void*)(l_Std_TreeSet_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1864_, 0, v_cmp_1859_);
v___x_1865_ = lean_apply_4(v_inst_1861_, lean_box(0), v_l_1863_, v_t_1862_, v___f_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_union___redArg(lean_object* v_cmp_1866_, lean_object* v_t_u2081_1867_, lean_object* v_t_u2082_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1866_, v_t_u2081_1867_, v_t_u2082_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_union(lean_object* v_00_u03b1_1870_, lean_object* v_cmp_1871_, lean_object* v_t_u2081_1872_, lean_object* v_t_u2082_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_1871_, v_t_u2081_1872_, v_t_u2082_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion___redArg(lean_object* v_cmp_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_alloc_closure((void*)(l_Std_TreeSet_union), 4, 2);
lean_closure_set(v___x_1876_, 0, lean_box(0));
lean_closure_set(v___x_1876_, 1, v_cmp_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instUnion(lean_object* v_00_u03b1_1877_, lean_object* v_cmp_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_closure((void*)(l_Std_TreeSet_union), 4, 2);
lean_closure_set(v___x_1879_, 0, lean_box(0));
lean_closure_set(v___x_1879_, 1, v_cmp_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_inter___redArg(lean_object* v_cmp_1880_, lean_object* v_t_u2081_1881_, lean_object* v_t_u2082_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1880_, v_t_u2081_1881_, v_t_u2082_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_inter(lean_object* v_00_u03b1_1884_, lean_object* v_cmp_1885_, lean_object* v_t_u2081_1886_, lean_object* v_t_u2082_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_1885_, v_t_u2081_1886_, v_t_u2082_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter___redArg(lean_object* v_cmp_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_closure((void*)(l_Std_TreeSet_inter), 4, 2);
lean_closure_set(v___x_1890_, 0, lean_box(0));
lean_closure_set(v___x_1890_, 1, v_cmp_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instInter(lean_object* v_00_u03b1_1891_, lean_object* v_cmp_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_alloc_closure((void*)(l_Std_TreeSet_inter), 4, 2);
lean_closure_set(v___x_1893_, 0, lean_box(0));
lean_closure_set(v___x_1893_, 1, v_cmp_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_cmp_1894_, lean_object* v_t_1895_, lean_object* v_k_1896_){
_start:
{
if (lean_obj_tag(v_t_1895_) == 0)
{
lean_object* v_k_1897_; lean_object* v_v_1898_; lean_object* v_l_1899_; lean_object* v_r_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v_k_1897_ = lean_ctor_get(v_t_1895_, 1);
lean_inc(v_k_1897_);
v_v_1898_ = lean_ctor_get(v_t_1895_, 2);
lean_inc(v_v_1898_);
v_l_1899_ = lean_ctor_get(v_t_1895_, 3);
lean_inc(v_l_1899_);
v_r_1900_ = lean_ctor_get(v_t_1895_, 4);
lean_inc(v_r_1900_);
lean_dec_ref_known(v_t_1895_, 5);
lean_inc_ref(v_cmp_1894_);
lean_inc(v_k_1896_);
v___x_1901_ = lean_apply_2(v_cmp_1894_, v_k_1896_, v_k_1897_);
v___x_1902_ = lean_unbox(v___x_1901_);
switch(v___x_1902_)
{
case 0:
{
lean_dec(v_r_1900_);
lean_dec(v_v_1898_);
v_t_1895_ = v_l_1899_;
goto _start;
}
case 1:
{
lean_object* v___x_1904_; 
lean_dec(v_r_1900_);
lean_dec(v_l_1899_);
lean_dec(v_k_1896_);
lean_dec_ref(v_cmp_1894_);
v___x_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_v_1898_);
return v___x_1904_;
}
default: 
{
lean_dec(v_l_1899_);
lean_dec(v_v_1898_);
v_t_1895_ = v_r_1900_;
goto _start;
}
}
}
else
{
lean_object* v___x_1906_; 
lean_dec(v_k_1896_);
lean_dec_ref(v_cmp_1894_);
v___x_1906_ = lean_box(0);
return v___x_1906_;
}
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
if (lean_obj_tag(v_x_1907_) == 0)
{
if (lean_obj_tag(v_x_1908_) == 0)
{
uint8_t v___x_1909_; 
v___x_1909_ = 1;
return v___x_1909_;
}
else
{
uint8_t v___x_1910_; 
v___x_1910_ = 0;
return v___x_1910_;
}
}
else
{
if (lean_obj_tag(v_x_1908_) == 0)
{
uint8_t v___x_1911_; 
v___x_1911_ = 0;
return v___x_1911_;
}
else
{
uint8_t v___x_1912_; 
v___x_1912_ = 1;
return v___x_1912_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1913_, lean_object* v_x_1914_){
_start:
{
uint8_t v_res_1915_; lean_object* v_r_1916_; 
v_res_1915_ = l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v_x_1913_, v_x_1914_);
lean_dec(v_x_1914_);
lean_dec(v_x_1913_);
v_r_1916_ = lean_box(v_res_1915_);
return v_r_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v_cmp_1919_, lean_object* v_t_u2082_1920_, lean_object* v_init_1921_, lean_object* v_x_1922_){
_start:
{
lean_object* v___x_1923_; uint8_t v___y_1925_; lean_object* v___x_1930_; uint8_t v___y_1932_; uint8_t v___x_1950_; 
v___x_1923_ = lean_box(0);
v___x_1930_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___x_1950_ = lean_nat_dec_eq(v___y_1917_, v___y_1918_);
if (v___x_1950_ == 0)
{
uint8_t v___x_1951_; 
v___x_1951_ = 1;
v___y_1932_ = v___x_1951_;
goto v___jp_1931_;
}
else
{
uint8_t v___x_1952_; 
v___x_1952_ = 0;
v___y_1932_ = v___x_1952_;
goto v___jp_1931_;
}
v___jp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1926_ = lean_box(v___y_1925_);
v___x_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set(v___x_1928_, 1, v___x_1923_);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
v___jp_1931_:
{
if (lean_obj_tag(v_x_1922_) == 0)
{
lean_object* v_k_1933_; lean_object* v_v_1934_; lean_object* v_l_1935_; lean_object* v_r_1936_; lean_object* v___x_1937_; 
v_k_1933_ = lean_ctor_get(v_x_1922_, 1);
lean_inc(v_k_1933_);
v_v_1934_ = lean_ctor_get(v_x_1922_, 2);
lean_inc(v_v_1934_);
v_l_1935_ = lean_ctor_get(v_x_1922_, 3);
lean_inc(v_l_1935_);
v_r_1936_ = lean_ctor_get(v_x_1922_, 4);
lean_inc(v_r_1936_);
lean_dec_ref_known(v_x_1922_, 5);
lean_inc(v_t_u2082_1920_);
lean_inc_ref(v_cmp_1919_);
v___x_1937_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1917_, v___y_1918_, v_cmp_1919_, v_t_u2082_1920_, v_init_1921_, v_l_1935_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_dec(v_r_1936_);
lean_dec(v_v_1934_);
lean_dec(v_k_1933_);
lean_dec(v_t_u2082_1920_);
lean_dec_ref(v_cmp_1919_);
return v___x_1937_;
}
else
{
lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1947_; 
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v___x_1937_, 0);
lean_dec(v_unused_1948_);
v___x_1939_ = v___x_1937_;
v_isShared_1940_ = v_isSharedCheck_1947_;
goto v_resetjp_1938_;
}
else
{
lean_dec(v___x_1937_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1947_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
lean_inc(v_t_u2082_1920_);
lean_inc_ref(v_cmp_1919_);
v___x_1941_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1919_, v_t_u2082_1920_, v_k_1933_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v_v_1934_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_v_1934_);
v___x_1943_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
uint8_t v___x_1944_; 
v___x_1944_ = l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v___x_1941_, v___x_1943_);
lean_dec_ref(v___x_1943_);
lean_dec(v___x_1941_);
if (v___x_1944_ == 0)
{
lean_dec(v_r_1936_);
lean_dec(v_t_u2082_1920_);
lean_dec_ref(v_cmp_1919_);
v___y_1925_ = v___y_1932_;
goto v___jp_1924_;
}
else
{
if (v___y_1932_ == 0)
{
v_init_1921_ = v___x_1930_;
v_x_1922_ = v_r_1936_;
goto _start;
}
else
{
lean_dec(v_r_1936_);
lean_dec(v_t_u2082_1920_);
lean_dec_ref(v_cmp_1919_);
v___y_1925_ = v___y_1932_;
goto v___jp_1924_;
}
}
}
}
}
}
else
{
lean_object* v___x_1949_; 
lean_dec(v_t_u2082_1920_);
lean_dec_ref(v_cmp_1919_);
v___x_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1949_, 0, v_init_1921_);
return v___x_1949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v_cmp_1955_, lean_object* v_t_u2082_1956_, lean_object* v_init_1957_, lean_object* v_x_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1953_, v___y_1954_, v_cmp_1955_, v_t_u2082_1956_, v_init_1957_, v_x_1958_);
lean_dec(v___y_1954_);
lean_dec(v___y_1953_);
return v_res_1959_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_1960_, lean_object* v_t_u2081_1961_, lean_object* v_t_u2082_1962_){
_start:
{
lean_object* v___y_1964_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1977_; 
if (lean_obj_tag(v_t_u2081_1961_) == 0)
{
lean_object* v_size_1980_; 
v_size_1980_ = lean_ctor_get(v_t_u2081_1961_, 0);
lean_inc(v_size_1980_);
v___y_1977_ = v_size_1980_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___y_1977_ = v___x_1981_;
goto v___jp_1976_;
}
v___jp_1963_:
{
lean_object* v_fst_1965_; 
v_fst_1965_ = lean_ctor_get(v___y_1964_, 0);
lean_inc(v_fst_1965_);
lean_dec_ref(v___y_1964_);
if (lean_obj_tag(v_fst_1965_) == 0)
{
uint8_t v___x_1966_; 
v___x_1966_ = 1;
return v___x_1966_;
}
else
{
lean_object* v_val_1967_; uint8_t v___x_1968_; 
v_val_1967_ = lean_ctor_get(v_fst_1965_, 0);
lean_inc(v_val_1967_);
lean_dec_ref_known(v_fst_1965_, 1);
v___x_1968_ = lean_unbox(v_val_1967_);
lean_dec(v_val_1967_);
return v___x_1968_;
}
}
v___jp_1969_:
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_nat_dec_eq(v___y_1970_, v___y_1971_);
if (v___x_1972_ == 0)
{
lean_dec(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec(v_t_u2082_1962_);
lean_dec(v_t_u2081_1961_);
lean_dec_ref(v_cmp_1960_);
return v___x_1972_;
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v_a_1975_; 
v___x_1973_ = ((lean_object*)(l_Std_TreeSet_any___redArg___closed__0));
v___x_1974_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1970_, v___y_1971_, v_cmp_1960_, v_t_u2082_1962_, v___x_1973_, v_t_u2081_1961_);
lean_dec(v___y_1971_);
lean_dec(v___y_1970_);
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref(v___x_1974_);
v___y_1964_ = v_a_1975_;
goto v___jp_1963_;
}
}
v___jp_1976_:
{
if (lean_obj_tag(v_t_u2082_1962_) == 0)
{
lean_object* v_size_1978_; 
v_size_1978_ = lean_ctor_get(v_t_u2082_1962_, 0);
lean_inc(v_size_1978_);
v___y_1970_ = v___y_1977_;
v___y_1971_ = v_size_1978_;
goto v___jp_1969_;
}
else
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_unsigned_to_nat(0u);
v___y_1970_ = v___y_1977_;
v___y_1971_ = v___x_1979_;
goto v___jp_1969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_1982_, lean_object* v_t_u2081_1983_, lean_object* v_t_u2082_1984_){
_start:
{
uint8_t v_res_1985_; lean_object* v_r_1986_; 
v_res_1985_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1982_, v_t_u2081_1983_, v_t_u2082_1984_);
v_r_1986_ = lean_box(v_res_1985_);
return v_r_1986_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_beq___redArg(lean_object* v_cmp_1987_, lean_object* v_t_u2081_1988_, lean_object* v_t_u2082_1989_){
_start:
{
uint8_t v___x_1990_; 
v___x_1990_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1987_, v_t_u2081_1988_, v_t_u2082_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___redArg___boxed(lean_object* v_cmp_1991_, lean_object* v_t_u2081_1992_, lean_object* v_t_u2082_1993_){
_start:
{
uint8_t v_res_1994_; lean_object* v_r_1995_; 
v_res_1994_ = l_Std_TreeSet_beq___redArg(v_cmp_1991_, v_t_u2081_1992_, v_t_u2082_1993_);
v_r_1995_ = lean_box(v_res_1994_);
return v_r_1995_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_beq(lean_object* v_00_u03b1_1996_, lean_object* v_cmp_1997_, lean_object* v_t_u2081_1998_, lean_object* v_t_u2082_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1997_, v_t_u2081_1998_, v_t_u2082_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_beq___boxed(lean_object* v_00_u03b1_2001_, lean_object* v_cmp_2002_, lean_object* v_t_u2081_2003_, lean_object* v_t_u2082_2004_){
_start:
{
uint8_t v_res_2005_; lean_object* v_r_2006_; 
v_res_2005_ = l_Std_TreeSet_beq(v_00_u03b1_2001_, v_cmp_2002_, v_t_u2081_2003_, v_t_u2082_2004_);
v_r_2006_ = lean_box(v_res_2005_);
return v_r_2006_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(lean_object* v_cmp_2007_, lean_object* v_t_u2081_2008_, lean_object* v_t_u2082_2009_){
_start:
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2007_, v_t_u2081_2008_, v_t_u2082_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg___boxed(lean_object* v_cmp_2011_, lean_object* v_t_u2081_2012_, lean_object* v_t_u2082_2013_){
_start:
{
uint8_t v_res_2014_; lean_object* v_r_2015_; 
v_res_2014_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(v_cmp_2011_, v_t_u2081_2012_, v_t_u2082_2013_);
v_r_2015_ = lean_box(v_res_2014_);
return v_r_2015_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(lean_object* v_00_u03b1_2016_, lean_object* v_cmp_2017_, lean_object* v_t_u2081_2018_, lean_object* v_t_u2082_2019_){
_start:
{
uint8_t v___x_2020_; 
v___x_2020_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2017_, v_t_u2081_2018_, v_t_u2082_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___boxed(lean_object* v_00_u03b1_2021_, lean_object* v_cmp_2022_, lean_object* v_t_u2081_2023_, lean_object* v_t_u2082_2024_){
_start:
{
uint8_t v_res_2025_; lean_object* v_r_2026_; 
v_res_2025_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(v_00_u03b1_2021_, v_cmp_2022_, v_t_u2081_2023_, v_t_u2082_2024_);
v_r_2026_ = lean_box(v_res_2025_);
return v_r_2026_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(lean_object* v_cmp_2027_, lean_object* v_t_u2081_2028_, lean_object* v_t_u2082_2029_){
_start:
{
uint8_t v___x_2030_; 
v___x_2030_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2027_, v_t_u2081_2028_, v_t_u2082_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_2031_, lean_object* v_t_u2081_2032_, lean_object* v_t_u2082_2033_){
_start:
{
uint8_t v_res_2034_; lean_object* v_r_2035_; 
v_res_2034_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(v_cmp_2031_, v_t_u2081_2032_, v_t_u2082_2033_);
v_r_2035_ = lean_box(v_res_2034_);
return v_r_2035_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(lean_object* v_00_u03b1_2036_, lean_object* v_cmp_2037_, lean_object* v_t_u2081_2038_, lean_object* v_t_u2082_2039_){
_start:
{
uint8_t v___x_2040_; 
v___x_2040_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2037_, v_t_u2081_2038_, v_t_u2082_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2041_, lean_object* v_cmp_2042_, lean_object* v_t_u2081_2043_, lean_object* v_t_u2082_2044_){
_start:
{
uint8_t v_res_2045_; lean_object* v_r_2046_; 
v_res_2045_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(v_00_u03b1_2041_, v_cmp_2042_, v_t_u2081_2043_, v_t_u2082_2044_);
v_r_2046_ = lean_box(v_res_2045_);
return v_r_2046_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2047_, lean_object* v_cmp_2048_, lean_object* v_t_u2081_2049_, lean_object* v_t_u2082_2050_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_2048_, v_t_u2081_2049_, v_t_u2082_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2052_, lean_object* v_cmp_2053_, lean_object* v_t_u2081_2054_, lean_object* v_t_u2082_2055_){
_start:
{
uint8_t v_res_2056_; lean_object* v_r_2057_; 
v_res_2056_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(v_00_u03b1_2052_, v_cmp_2053_, v_t_u2081_2054_, v_t_u2082_2055_);
v_r_2057_ = lean_box(v_res_2056_);
return v_r_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2058_, lean_object* v_cmp_2059_, lean_object* v_00_u03b4_2060_, lean_object* v_t_2061_, lean_object* v_k_2062_){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_2059_, v_t_2061_, v_k_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v_cmp_2067_, lean_object* v_t_u2082_2068_, lean_object* v_init_2069_, lean_object* v_x_2070_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_2065_, v___y_2066_, v_cmp_2067_, v_t_u2082_2068_, v_init_2069_, v_x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v_cmp_2075_, lean_object* v_t_u2082_2076_, lean_object* v_init_2077_, lean_object* v_x_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2072_, v___y_2073_, v___y_2074_, v_cmp_2075_, v_t_u2082_2076_, v_init_2077_, v_x_2078_);
lean_dec(v___y_2074_);
lean_dec(v___y_2073_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq___redArg(lean_object* v_cmp_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_alloc_closure((void*)(l_Std_TreeSet_beq___boxed), 4, 2);
lean_closure_set(v___x_2081_, 0, lean_box(0));
lean_closure_set(v___x_2081_, 1, v_cmp_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instBEq(lean_object* v_00_u03b1_2082_, lean_object* v_cmp_2083_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_closure((void*)(l_Std_TreeSet_beq___boxed), 4, 2);
lean_closure_set(v___x_2084_, 0, lean_box(0));
lean_closure_set(v___x_2084_, 1, v_cmp_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_diff___redArg(lean_object* v_cmp_2085_, lean_object* v_t_u2081_2086_, lean_object* v_t_u2082_2087_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2085_, v_t_u2081_2086_, v_t_u2082_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_diff(lean_object* v_00_u03b1_2089_, lean_object* v_cmp_2090_, lean_object* v_t_u2081_2091_, lean_object* v_t_u2082_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2090_, v_t_u2081_2091_, v_t_u2082_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff___redArg(lean_object* v_cmp_2094_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_alloc_closure((void*)(l_Std_TreeSet_diff), 4, 2);
lean_closure_set(v___x_2095_, 0, lean_box(0));
lean_closure_set(v___x_2095_, 1, v_cmp_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instSDiff(lean_object* v_00_u03b1_2096_, lean_object* v_cmp_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_alloc_closure((void*)(l_Std_TreeSet_diff), 4, 2);
lean_closure_set(v___x_2098_, 0, lean_box(0));
lean_closure_set(v___x_2098_, 1, v_cmp_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg___lam__0(lean_object* v_cmp_2099_, lean_object* v_a_2100_, lean_object* v_____s_2101_){
_start:
{
lean_object* v_r_2102_; lean_object* v___x_2103_; 
v_r_2102_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2099_, v_a_2100_, v_____s_2101_);
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v_r_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany___redArg(lean_object* v_cmp_2104_, lean_object* v_inst_2105_, lean_object* v_t_2106_, lean_object* v_l_2107_){
_start:
{
lean_object* v___f_2108_; lean_object* v___x_2109_; 
v___f_2108_ = lean_alloc_closure((void*)(l_Std_TreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2108_, 0, v_cmp_2104_);
v___x_2109_ = lean_apply_4(v_inst_2105_, lean_box(0), v_l_2107_, v_t_2106_, v___f_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_eraseMany(lean_object* v_00_u03b1_2110_, lean_object* v_cmp_2111_, lean_object* v_00_u03c1_2112_, lean_object* v_inst_2113_, lean_object* v_t_2114_, lean_object* v_l_2115_){
_start:
{
lean_object* v___f_2116_; lean_object* v___x_2117_; 
v___f_2116_ = lean_alloc_closure((void*)(l_Std_TreeSet_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2116_, 0, v_cmp_2111_);
v___x_2117_ = lean_apply_4(v_inst_2113_, lean_box(0), v_l_2115_, v_t_2114_, v___f_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1(lean_object* v___f_2121_, lean_object* v_inst_2122_, lean_object* v_m_2123_, lean_object* v_prec_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2125_ = ((lean_object*)(l_Std_TreeSet_instRepr___redArg___lam__1___closed__1));
v___x_2126_ = lean_box(0);
v___x_2127_ = ((lean_object*)(l_Std_TreeSet_foldr___redArg___closed__9));
v___x_2128_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2127_, v___f_2121_, v___x_2126_, v_m_2123_);
v___x_2129_ = l_List_repr___redArg(v_inst_2122_, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2125_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Repr_addAppParen(v___x_2130_, v_prec_2124_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg___lam__1___boxed(lean_object* v___f_2132_, lean_object* v_inst_2133_, lean_object* v_m_2134_, lean_object* v_prec_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Std_TreeSet_instRepr___redArg___lam__1(v___f_2132_, v_inst_2133_, v_m_2134_, v_prec_2135_);
lean_dec(v_prec_2135_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___redArg(lean_object* v_inst_2137_){
_start:
{
lean_object* v___f_2138_; lean_object* v___f_2139_; 
v___f_2138_ = ((lean_object*)(l_Std_TreeSet_toList___redArg___closed__0));
v___f_2139_ = lean_alloc_closure((void*)(l_Std_TreeSet_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2139_, 0, v___f_2138_);
lean_closure_set(v___f_2139_, 1, v_inst_2137_);
return v___f_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr(lean_object* v_00_u03b1_2140_, lean_object* v_cmp_2141_, lean_object* v_inst_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Std_TreeSet_instRepr___redArg(v_inst_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instRepr___boxed(lean_object* v_00_u03b1_2144_, lean_object* v_cmp_2145_, lean_object* v_inst_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Std_TreeSet_instRepr(v_00_u03b1_2144_, v_cmp_2145_, v_inst_2146_);
lean_dec_ref(v_cmp_2145_);
return v_res_2147_;
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
