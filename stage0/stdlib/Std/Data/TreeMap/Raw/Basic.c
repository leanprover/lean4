// Lean compiler output
// Module: Std.Data.TreeMap.Raw.Basic
// Imports: public import Std.Data.DTreeMap.Raw.Basic
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeMap_Raw___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__0_value;
static const lean_string_object l_Std_TreeMap_Raw___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__1 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__1_value;
static const lean_string_object l_Std_TreeMap_Raw___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__2 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__2_value;
static const lean_string_object l_Std_TreeMap_Raw___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__3 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__3_value;
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__4 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__4_value;
static const lean_array_object l_Std_TreeMap_Raw___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__5 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__5_value;
static const lean_string_object l_Std_TreeMap_Raw___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__6 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__6_value;
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__7 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__7_value;
static const lean_string_object l_Std_TreeMap_Raw___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__8 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__8_value;
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__9 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__9_value;
static const lean_string_object l_Std_TreeMap_Raw___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__10 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__10_value;
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__11 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__11_value;
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__12;
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__13;
static const lean_string_object l_Std_TreeMap_Raw___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__14 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__14_value;
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__15 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__15_value;
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__16 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__16_value;
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__15_value),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeMap_Raw___auto__1___closed__17 = (const lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__17_value;
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__18;
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__19;
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__20;
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__21;
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__22;
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__23;
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__24;
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__25;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeMap_Raw_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_TreeMap_Raw_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TreeMap"};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__1 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_TreeMap_Raw_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Raw"};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__2 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__2_value;
static const lean_string_object l_Std_TreeMap_Raw_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__3 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__3_value;
static const lean_ctor_object l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_0),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(198, 52, 198, 157, 19, 230, 196, 235)}};
static const lean_ctor_object l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_1),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(253, 144, 163, 182, 151, 123, 142, 126)}};
static const lean_ctor_object l_Std_TreeMap_Raw_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_2),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 99, 107, 130, 189, 13, 49, 97)}};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__4 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__4_value;
static const lean_string_object l_Std_TreeMap_Raw_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__5 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__5_value;
static const lean_ctor_object l_Std_TreeMap_Raw_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__6 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__6_value;
static const lean_string_object l_Std_TreeMap_Raw_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__7 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__7_value;
static const lean_ctor_object l_Std_TreeMap_Raw_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__7_value)}};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__8 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__8_value;
static const lean_string_object l_Std_TreeMap_Raw_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__9 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_TreeMap_Raw_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__10 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_TreeMap_Raw_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__10_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__11 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_TreeMap_Raw_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__6_value),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__8_value),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__12 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__12_value;
static const lean_ctor_object l_Std_TreeMap_Raw_term___x7em___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__4_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__12_value)}};
static const lean_object* l_Std_TreeMap_Raw_term___x7em___00__closed__13 = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__13_value;
LEAN_EXPORT const lean_object* l_Std_TreeMap_Raw_term___x7em__ = (const lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__13_value;
static const lean_string_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__1 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__1_value;
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_0),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_1),((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_2),((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3_value;
static lean_once_cell_t l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4;
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__5 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__5_value;
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_0),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(198, 52, 198, 157, 19, 230, 196, 235)}};
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_1),((lean_object*)&l_Std_TreeMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(253, 144, 163, 182, 151, 123, 142, 126)}};
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_2),((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(190, 41, 117, 30, 103, 140, 131, 94)}};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value;
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__7 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value)}};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__8 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__9 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__7_value),((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__9_value)}};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__10 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__10_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__1 = (const lean_object*)&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__0_value;
static const lean_string_object l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__1 = (const lean_object*)&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__1_value;
static const lean_string_object l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__2 = (const lean_object*)&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_foldr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_foldr___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__0_value;
static const lean_closure_object l_Std_TreeMap_Raw_foldr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_foldr___redArg___closed__1 = (const lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__1_value;
static const lean_closure_object l_Std_TreeMap_Raw_foldr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_foldr___redArg___closed__2 = (const lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__2_value;
static const lean_closure_object l_Std_TreeMap_Raw_foldr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_foldr___redArg___closed__3 = (const lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__3_value;
static const lean_closure_object l_Std_TreeMap_Raw_foldr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_foldr___redArg___closed__4 = (const lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__4_value;
static const lean_closure_object l_Std_TreeMap_Raw_foldr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_foldr___redArg___closed__5 = (const lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__5_value;
static const lean_closure_object l_Std_TreeMap_Raw_foldr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_foldr___redArg___closed__6 = (const lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__6_value;
static const lean_ctor_object l_Std_TreeMap_Raw_foldr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__0_value),((lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__1_value)}};
static const lean_object* l_Std_TreeMap_Raw_foldr___redArg___closed__7 = (const lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__7_value;
static const lean_ctor_object l_Std_TreeMap_Raw_foldr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__7_value),((lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__2_value),((lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__3_value),((lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__4_value),((lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__5_value)}};
static const lean_object* l_Std_TreeMap_Raw_foldr___redArg___closed__8 = (const lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__8_value;
static const lean_ctor_object l_Std_TreeMap_Raw_foldr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__8_value),((lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__6_value)}};
static const lean_object* l_Std_TreeMap_Raw_foldr___redArg___closed__9 = (const lean_object*)&l_Std_TreeMap_Raw_foldr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_TreeMap_Raw_partition___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_TreeMap_Raw_partition___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_partition___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_TreeMap_Raw_any___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeMap_Raw_any___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_any___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_keys___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_keys___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_keysArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_values___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_values___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_valuesArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_toList___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_toArray___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofArray___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfArray___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instUnion___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instUnion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_inter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instBEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instBEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSDiff___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSDiff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.TreeMap.Raw.ofList "};
static const lean_object* l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__12, &l_Std_TreeMap_Raw___auto__1___closed__12_once, _init_l_Std_TreeMap_Raw___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__17));
v___x_45_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__13, &l_Std_TreeMap_Raw___auto__1___closed__13_once, _init_l_Std_TreeMap_Raw___auto__1___closed__13);
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__18, &l_Std_TreeMap_Raw___auto__1___closed__18_once, _init_l_Std_TreeMap_Raw___auto__1___closed__18);
v___x_48_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__11));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__19, &l_Std_TreeMap_Raw___auto__1___closed__19_once, _init_l_Std_TreeMap_Raw___auto__1___closed__19);
v___x_52_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__20, &l_Std_TreeMap_Raw___auto__1___closed__20_once, _init_l_Std_TreeMap_Raw___auto__1___closed__20);
v___x_55_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__9));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__22(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__21, &l_Std_TreeMap_Raw___auto__1___closed__21_once, _init_l_Std_TreeMap_Raw___auto__1___closed__21);
v___x_59_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__23(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__22, &l_Std_TreeMap_Raw___auto__1___closed__22_once, _init_l_Std_TreeMap_Raw___auto__1___closed__22);
v___x_62_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__7));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__24(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__23, &l_Std_TreeMap_Raw___auto__1___closed__23_once, _init_l_Std_TreeMap_Raw___auto__1___closed__23);
v___x_66_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__25(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__24, &l_Std_TreeMap_Raw___auto__1___closed__24_once, _init_l_Std_TreeMap_Raw___auto__1___closed__24);
v___x_69_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__4));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__25, &l_Std_TreeMap_Raw___auto__1___closed__25_once, _init_l_Std_TreeMap_Raw___auto__1___closed__25);
return v___x_72_;
}
}
lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_instCoeWFWFInner___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_75_;
v_res_75_ = l_Std_TreeMap_Raw_instCoeWFWFInner___redArg();
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner___redArg___boxed(lean_object* v___dummy_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_TreeMap_Raw_instCoeWFWFInner___redArg();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner(lean_object* v_00_u03b1_78_, lean_object* v_00_u03b2_79_, lean_object* v_cmp_80_, lean_object* v_t_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner___boxed(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_cmp_85_, lean_object* v_t_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_TreeMap_Raw_instCoeWFWFInner(v_00_u03b1_83_, v_00_u03b2_84_, v_cmp_85_, v_t_86_);
lean_dec(v_t_86_);
lean_dec_ref(v_cmp_85_);
return v_res_87_;
}
}
lean_object* l_Std_TreeMap_Raw_empty___redArg(){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(1);
return v___x_89_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_90_;
v_res_90_ = l_Std_TreeMap_Raw_empty___redArg();
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty___redArg___boxed(lean_object* v___dummy_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_TreeMap_Raw_empty___redArg();
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_cmp_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty___boxed(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_cmp_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_TreeMap_Raw_empty(v_00_u03b1_97_, v_00_u03b2_98_, v_cmp_99_);
lean_dec_ref(v_cmp_99_);
return v_res_100_;
}
}
lean_object* l_Std_TreeMap_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(1);
return v___x_102_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_103_;
v_res_103_ = l_Std_TreeMap_Raw_instEmptyCollection___redArg();
stack->m_obj
 = v_res_103_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_TreeMap_Raw_instEmptyCollection___redArg();
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_106_, lean_object* v_00_u03b2_107_, lean_object* v_cmp_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(1);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection___boxed(lean_object* v_00_u03b1_110_, lean_object* v_00_u03b2_111_, lean_object* v_cmp_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_TreeMap_Raw_instEmptyCollection(v_00_u03b1_110_, v_00_u03b2_111_, v_cmp_112_);
lean_dec_ref(v_cmp_112_);
return v_res_113_;
}
}
lean_object* l_Std_TreeMap_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(1);
return v___x_115_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_116_;
v_res_116_ = l_Std_TreeMap_Raw_instInhabited___redArg();
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_TreeMap_Raw_instInhabited___redArg();
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_cmp_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(1);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited___boxed(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_cmp_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_TreeMap_Raw_instInhabited(v_00_u03b1_123_, v_00_u03b2_124_, v_cmp_125_);
lean_dec_ref(v_cmp_125_);
return v_res_126_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3));
v___x_167_ = l_String_toRawSubstring_x27(v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1(lean_object* v_x_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l_Std_TreeMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_186_);
v___x_190_ = l_Lean_Syntax_isOfKind(v_x_186_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_x_186_);
v___x_191_ = lean_box(1);
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_a_188_);
return v___x_192_;
}
else
{
lean_object* v_quotContext_193_; lean_object* v_currMacroScope_194_; lean_object* v_ref_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_quotContext_193_ = lean_ctor_get(v_a_187_, 1);
v_currMacroScope_194_ = lean_ctor_get(v_a_187_, 2);
v_ref_195_ = lean_ctor_get(v_a_187_, 5);
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = l_Lean_Syntax_getArg(v_x_186_, v___x_196_);
v___x_198_ = lean_unsigned_to_nat(2u);
v___x_199_ = l_Lean_Syntax_getArg(v_x_186_, v___x_198_);
lean_dec(v_x_186_);
v___x_200_ = 0;
v___x_201_ = l_Lean_SourceInfo_fromRef(v_ref_195_, v___x_200_);
v___x_202_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2));
v___x_203_ = lean_obj_once(&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4, &l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4_once, _init_l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4);
v___x_204_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_194_);
lean_inc(v_quotContext_193_);
v___x_205_ = l_Lean_addMacroScope(v_quotContext_193_, v___x_204_, v_currMacroScope_194_);
v___x_206_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__10));
lean_inc_n(v___x_201_, 2);
v___x_207_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_207_, 0, v___x_201_);
lean_ctor_set(v___x_207_, 1, v___x_203_);
lean_ctor_set(v___x_207_, 2, v___x_205_);
lean_ctor_set(v___x_207_, 3, v___x_206_);
v___x_208_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__9));
v___x_209_ = l_Lean_Syntax_node2(v___x_201_, v___x_208_, v___x_197_, v___x_199_);
v___x_210_ = l_Lean_Syntax_node2(v___x_201_, v___x_202_, v___x_207_, v___x_209_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v_a_188_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___boxed(lean_object* v_x_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1(v_x_212_, v_a_213_, v_a_214_);
lean_dec_ref(v_a_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1(lean_object* v_x_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2));
lean_inc(v_x_219_);
v___x_223_ = l_Lean_Syntax_isOfKind(v_x_219_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec(v_x_219_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v_a_221_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = l_Lean_Syntax_getArg(v_x_219_, v___x_226_);
v___x_228_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_227_);
v___x_229_ = l_Lean_Syntax_isOfKind(v___x_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec(v___x_227_);
lean_dec(v_x_219_);
v___x_230_ = lean_box(0);
v___x_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_a_221_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = l_Lean_Syntax_getArg(v_x_219_, v___x_232_);
lean_dec(v_x_219_);
v___x_234_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_233_);
v___x_235_ = l_Lean_Syntax_matchesNull(v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v___x_233_);
lean_dec(v___x_227_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v_a_221_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v_ref_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_238_ = l_Lean_Syntax_getArg(v___x_233_, v___x_226_);
v___x_239_ = l_Lean_Syntax_getArg(v___x_233_, v___x_232_);
lean_dec(v___x_233_);
v_ref_240_ = l_Lean_replaceRef(v___x_227_, v_a_220_);
lean_dec(v___x_227_);
v___x_241_ = 0;
v___x_242_ = l_Lean_SourceInfo_fromRef(v_ref_240_, v___x_241_);
lean_dec(v_ref_240_);
v___x_243_ = ((lean_object*)(l_Std_TreeMap_Raw_term___x7em___00__closed__4));
v___x_244_ = ((lean_object*)(l_Std_TreeMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_242_);
v___x_245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_242_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = l_Lean_Syntax_node3(v___x_242_, v___x_243_, v___x_238_, v___x_245_, v___x_239_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_a_221_);
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___boxed(lean_object* v_x_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1(v_x_248_, v_a_249_, v_a_250_);
lean_dec(v_a_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insert___redArg(lean_object* v_cmp_252_, lean_object* v_l_253_, lean_object* v_a_254_, lean_object* v_b_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_252_, v_a_254_, v_b_255_, v_l_253_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insert(lean_object* v_00_u03b1_257_, lean_object* v_00_u03b2_258_, lean_object* v_cmp_259_, lean_object* v_l_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_259_, v_a_261_, v_b_262_, v_l_260_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0(lean_object* v_cmp_264_, lean_object* v_e_265_){
_start:
{
lean_object* v_fst_266_; lean_object* v_snd_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_fst_266_ = lean_ctor_get(v_e_265_, 0);
lean_inc(v_fst_266_);
v_snd_267_ = lean_ctor_get(v_e_265_, 1);
lean_inc(v_snd_267_);
lean_dec_ref(v_e_265_);
v___x_268_ = lean_box(1);
v___x_269_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_264_, v_fst_266_, v_snd_267_, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd___redArg(lean_object* v_cmp_270_){
_start:
{
lean_object* v___f_271_; 
v___f_271_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0), 2, 1);
lean_closure_set(v___f_271_, 0, v_cmp_270_);
return v___f_271_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd(lean_object* v_00_u03b1_272_, lean_object* v_00_u03b2_273_, lean_object* v_cmp_274_){
_start:
{
lean_object* v___f_275_; 
v___f_275_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0), 2, 1);
lean_closure_set(v___f_275_, 0, v_cmp_274_);
return v___f_275_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0(lean_object* v_cmp_276_, lean_object* v_e_277_, lean_object* v_s_278_){
_start:
{
lean_object* v_fst_279_; lean_object* v_snd_280_; lean_object* v___x_281_; 
v_fst_279_ = lean_ctor_get(v_e_277_, 0);
lean_inc(v_fst_279_);
v_snd_280_ = lean_ctor_get(v_e_277_, 1);
lean_inc(v_snd_280_);
lean_dec_ref(v_e_277_);
v___x_281_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_276_, v_fst_279_, v_snd_280_, v_s_278_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd___redArg(lean_object* v_cmp_282_){
_start:
{
lean_object* v___f_283_; 
v___f_283_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_283_, 0, v_cmp_282_);
return v___f_283_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd(lean_object* v_00_u03b1_284_, lean_object* v_00_u03b2_285_, lean_object* v_cmp_286_){
_start:
{
lean_object* v___f_287_; 
v___f_287_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_287_, 0, v_cmp_286_);
return v___f_287_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertIfNew___redArg(lean_object* v_cmp_288_, lean_object* v_t_289_, lean_object* v_a_290_, lean_object* v_b_291_){
_start:
{
uint8_t v___x_292_; 
lean_inc(v_t_289_);
lean_inc(v_a_290_);
lean_inc_ref(v_cmp_288_);
v___x_292_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_288_, v_a_290_, v_t_289_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
v___x_293_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_288_, v_a_290_, v_b_291_, v_t_289_);
return v___x_293_;
}
else
{
lean_dec(v_b_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_cmp_288_);
return v_t_289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertIfNew(lean_object* v_00_u03b1_294_, lean_object* v_00_u03b2_295_, lean_object* v_cmp_296_, lean_object* v_t_297_, lean_object* v_a_298_, lean_object* v_b_299_){
_start:
{
uint8_t v___x_300_; 
lean_inc(v_t_297_);
lean_inc(v_a_298_);
lean_inc_ref(v_cmp_296_);
v___x_300_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_296_, v_a_298_, v_t_297_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_296_, v_a_298_, v_b_299_, v_t_297_);
return v___x_301_;
}
else
{
lean_dec(v_b_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_cmp_296_);
return v_t_297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsert___redArg(lean_object* v_cmp_302_, lean_object* v_t_303_, lean_object* v_a_304_, lean_object* v_b_305_){
_start:
{
lean_object* v_sz_306_; lean_object* v_m_307_; lean_object* v___y_309_; 
v_sz_306_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_303_);
v_m_307_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_302_, v_a_304_, v_b_305_, v_t_303_);
if (lean_obj_tag(v_m_307_) == 0)
{
lean_object* v_size_313_; 
v_size_313_ = lean_ctor_get(v_m_307_, 0);
lean_inc(v_size_313_);
v___y_309_ = v_size_313_;
goto v___jp_308_;
}
else
{
lean_object* v___x_314_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___y_309_ = v___x_314_;
goto v___jp_308_;
}
v___jp_308_:
{
uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_nat_dec_eq(v_sz_306_, v___y_309_);
lean_dec(v___y_309_);
lean_dec(v_sz_306_);
v___x_311_ = lean_box(v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v_m_307_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsert(lean_object* v_00_u03b1_315_, lean_object* v_00_u03b2_316_, lean_object* v_cmp_317_, lean_object* v_t_318_, lean_object* v_a_319_, lean_object* v_b_320_){
_start:
{
lean_object* v_sz_321_; lean_object* v_m_322_; lean_object* v___y_324_; 
v_sz_321_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_318_);
v_m_322_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_317_, v_a_319_, v_b_320_, v_t_318_);
if (lean_obj_tag(v_m_322_) == 0)
{
lean_object* v_size_328_; 
v_size_328_ = lean_ctor_get(v_m_322_, 0);
lean_inc(v_size_328_);
v___y_324_ = v_size_328_;
goto v___jp_323_;
}
else
{
lean_object* v___x_329_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___y_324_ = v___x_329_;
goto v___jp_323_;
}
v___jp_323_:
{
uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_nat_dec_eq(v_sz_321_, v___y_324_);
lean_dec(v___y_324_);
lean_dec(v_sz_321_);
v___x_326_ = lean_box(v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v_m_322_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_cmp_330_, lean_object* v_t_331_, lean_object* v_a_332_, lean_object* v_b_333_){
_start:
{
uint8_t v___x_334_; 
lean_inc(v_t_331_);
lean_inc(v_a_332_);
lean_inc_ref(v_cmp_330_);
v___x_334_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_330_, v_a_332_, v_t_331_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_330_, v_a_332_, v_b_333_, v_t_331_);
v___x_336_ = lean_box(v___x_334_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
return v___x_337_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_b_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_cmp_330_);
v___x_338_ = lean_box(v___x_334_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v_t_331_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_340_, lean_object* v_00_u03b2_341_, lean_object* v_cmp_342_, lean_object* v_t_343_, lean_object* v_a_344_, lean_object* v_b_345_){
_start:
{
uint8_t v___x_346_; 
lean_inc(v_t_343_);
lean_inc(v_a_344_);
lean_inc_ref(v_cmp_342_);
v___x_346_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_342_, v_a_344_, v_t_343_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_342_, v_a_344_, v_b_345_, v_t_343_);
v___x_348_ = lean_box(v___x_346_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_b_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_cmp_342_);
v___x_350_ = lean_box(v___x_346_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_t_343_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_352_, lean_object* v_t_353_, lean_object* v_a_354_, lean_object* v_b_355_){
_start:
{
lean_object* v___x_356_; 
lean_inc(v_a_354_);
lean_inc(v_t_353_);
lean_inc_ref(v_cmp_352_);
v___x_356_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_352_, v_t_353_, v_a_354_);
if (lean_obj_tag(v___x_356_) == 0)
{
uint8_t v___x_357_; 
lean_inc(v_t_353_);
lean_inc(v_a_354_);
lean_inc_ref(v_cmp_352_);
v___x_357_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_352_, v_a_354_, v_t_353_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_352_, v_a_354_, v_b_355_, v_t_353_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_356_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; 
lean_dec(v_b_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_cmp_352_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_356_);
lean_ctor_set(v___x_360_, 1, v_t_353_);
return v___x_360_;
}
}
else
{
lean_object* v___x_361_; 
lean_dec(v_b_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_cmp_352_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_356_);
lean_ctor_set(v___x_361_, 1, v_t_353_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_362_, lean_object* v_00_u03b2_363_, lean_object* v_cmp_364_, lean_object* v_t_365_, lean_object* v_a_366_, lean_object* v_b_367_){
_start:
{
lean_object* v___x_368_; 
lean_inc(v_a_366_);
lean_inc(v_t_365_);
lean_inc_ref(v_cmp_364_);
v___x_368_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_364_, v_t_365_, v_a_366_);
if (lean_obj_tag(v___x_368_) == 0)
{
uint8_t v___x_369_; 
lean_inc(v_t_365_);
lean_inc(v_a_366_);
lean_inc_ref(v_cmp_364_);
v___x_369_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_364_, v_a_366_, v_t_365_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_364_, v_a_366_, v_b_367_, v_t_365_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_368_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; 
lean_dec(v_b_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_cmp_364_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_368_);
lean_ctor_set(v___x_372_, 1, v_t_365_);
return v___x_372_;
}
}
else
{
lean_object* v___x_373_; 
lean_dec(v_b_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_cmp_364_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_368_);
lean_ctor_set(v___x_373_, 1, v_t_365_);
return v___x_373_;
}
}
}
uint8_t l_Std_TreeMap_Raw_contains___redArg(lean_object* v_cmp_374_, lean_object* v_l_375_, lean_object* v_a_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_374_, v_a_376_, v_l_375_);
return v___x_377_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_374_ = stack[0].m_obj;
lean_object* v_l_375_ = stack[1].m_obj;
lean_object* v_a_376_ = stack[2].m_obj;
uint8_t v_res_378_;
v_res_378_ = l_Std_TreeMap_Raw_contains___redArg(v_cmp_374_, v_l_375_, v_a_376_);
stack->m_num = v_res_378_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_contains___redArg___boxed(lean_object* v_cmp_379_, lean_object* v_l_380_, lean_object* v_a_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Std_TreeMap_Raw_contains___redArg(v_cmp_379_, v_l_380_, v_a_381_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
uint8_t l_Std_TreeMap_Raw_contains(lean_object* v_00_u03b1_384_, lean_object* v_00_u03b2_385_, lean_object* v_cmp_386_, lean_object* v_l_387_, lean_object* v_a_388_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_386_, v_a_388_, v_l_387_);
return v___x_389_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_386_ = stack[2].m_obj;
lean_object* v_l_387_ = stack[3].m_obj;
lean_object* v_a_388_ = stack[4].m_obj;
uint8_t v_res_390_;
v_res_390_ = l_Std_TreeMap_Raw_contains(lean_box(0), lean_box(0), v_cmp_386_, v_l_387_, v_a_388_);
stack->m_num = v_res_390_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_contains___boxed(lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_cmp_393_, lean_object* v_l_394_, lean_object* v_a_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Std_TreeMap_Raw_contains(v_00_u03b1_391_, v_00_u03b2_392_, v_cmp_393_, v_l_394_, v_a_395_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
lean_object* l_Std_TreeMap_Raw_instMembership___redArg(){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
return v___x_399_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_400_;
v_res_400_ = l_Std_TreeMap_Raw_instMembership___redArg();
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership___redArg___boxed(lean_object* v___dummy_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_TreeMap_Raw_instMembership___redArg();
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_cmp_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_box(0);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership___boxed(lean_object* v_00_u03b1_407_, lean_object* v_00_u03b2_408_, lean_object* v_cmp_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_TreeMap_Raw_instMembership(v_00_u03b1_407_, v_00_u03b2_408_, v_cmp_409_);
lean_dec_ref(v_cmp_409_);
return v_res_410_;
}
}
uint8_t l_Std_TreeMap_Raw_instDecidableMem___redArg(lean_object* v_cmp_411_, lean_object* v_t_412_, lean_object* v_a_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_411_, v_a_413_, v_t_412_);
return v___x_414_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_411_ = stack[0].m_obj;
lean_object* v_t_412_ = stack[1].m_obj;
lean_object* v_a_413_ = stack[2].m_obj;
uint8_t v_res_415_;
v_res_415_ = l_Std_TreeMap_Raw_instDecidableMem___redArg(v_cmp_411_, v_t_412_, v_a_413_);
stack->m_num = v_res_415_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_416_, lean_object* v_t_417_, lean_object* v_a_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Std_TreeMap_Raw_instDecidableMem___redArg(v_cmp_416_, v_t_417_, v_a_418_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
uint8_t l_Std_TreeMap_Raw_instDecidableMem(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_cmp_423_, lean_object* v_t_424_, lean_object* v_a_425_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_423_, v_a_425_, v_t_424_);
return v___x_426_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_423_ = stack[2].m_obj;
lean_object* v_t_424_ = stack[3].m_obj;
lean_object* v_a_425_ = stack[4].m_obj;
uint8_t v_res_427_;
v_res_427_ = l_Std_TreeMap_Raw_instDecidableMem(lean_box(0), lean_box(0), v_cmp_423_, v_t_424_, v_a_425_);
stack->m_num = v_res_427_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_428_, lean_object* v_00_u03b2_429_, lean_object* v_cmp_430_, lean_object* v_t_431_, lean_object* v_a_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Std_TreeMap_Raw_instDecidableMem(v_00_u03b1_428_, v_00_u03b2_429_, v_cmp_430_, v_t_431_, v_a_432_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___redArg(lean_object* v_t_435_){
_start:
{
if (lean_obj_tag(v_t_435_) == 0)
{
lean_object* v_size_436_; 
v_size_436_ = lean_ctor_get(v_t_435_, 0);
lean_inc(v_size_436_);
return v_size_436_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = lean_unsigned_to_nat(0u);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___redArg___boxed(lean_object* v_t_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_TreeMap_Raw_size___redArg(v_t_438_);
lean_dec(v_t_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b2_441_, lean_object* v_cmp_442_, lean_object* v_t_443_){
_start:
{
if (lean_obj_tag(v_t_443_) == 0)
{
lean_object* v_size_444_; 
v_size_444_ = lean_ctor_get(v_t_443_, 0);
lean_inc(v_size_444_);
return v_size_444_;
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_unsigned_to_nat(0u);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___boxed(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_cmp_448_, lean_object* v_t_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_TreeMap_Raw_size(v_00_u03b1_446_, v_00_u03b2_447_, v_cmp_448_, v_t_449_);
lean_dec(v_t_449_);
lean_dec_ref(v_cmp_448_);
return v_res_450_;
}
}
uint8_t l_Std_TreeMap_Raw_isEmpty___redArg(lean_object* v_t_451_){
_start:
{
if (lean_obj_tag(v_t_451_) == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
v___x_453_ = 1;
return v___x_453_;
}
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_451_ = stack[0].m_obj;
uint8_t v_res_454_;
v_res_454_ = l_Std_TreeMap_Raw_isEmpty___redArg(v_t_451_);
stack->m_num = v_res_454_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_isEmpty___redArg___boxed(lean_object* v_t_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_Std_TreeMap_Raw_isEmpty___redArg(v_t_455_);
lean_dec(v_t_455_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
uint8_t l_Std_TreeMap_Raw_isEmpty(lean_object* v_00_u03b1_458_, lean_object* v_00_u03b2_459_, lean_object* v_cmp_460_, lean_object* v_t_461_){
_start:
{
if (lean_obj_tag(v_t_461_) == 0)
{
uint8_t v___x_462_; 
v___x_462_ = 0;
return v___x_462_;
}
else
{
uint8_t v___x_463_; 
v___x_463_ = 1;
return v___x_463_;
}
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_460_ = stack[2].m_obj;
lean_object* v_t_461_ = stack[3].m_obj;
uint8_t v_res_464_;
v_res_464_ = l_Std_TreeMap_Raw_isEmpty(lean_box(0), lean_box(0), v_cmp_460_, v_t_461_);
stack->m_num = v_res_464_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_465_, lean_object* v_00_u03b2_466_, lean_object* v_cmp_467_, lean_object* v_t_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_Std_TreeMap_Raw_isEmpty(v_00_u03b1_465_, v_00_u03b2_466_, v_cmp_467_, v_t_468_);
lean_dec(v_t_468_);
lean_dec_ref(v_cmp_467_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_erase___redArg(lean_object* v_cmp_471_, lean_object* v_t_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_471_, v_a_473_, v_t_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_erase(lean_object* v_00_u03b1_475_, lean_object* v_00_u03b2_476_, lean_object* v_cmp_477_, lean_object* v_t_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_477_, v_a_479_, v_t_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x3f___redArg(lean_object* v_cmp_481_, lean_object* v_t_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_481_, v_t_482_, v_a_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x3f(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_cmp_487_, lean_object* v_t_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_487_, v_t_488_, v_a_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get___redArg(lean_object* v_cmp_491_, lean_object* v_t_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_491_, v_t_492_, v_a_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get(lean_object* v_00_u03b1_495_, lean_object* v_00_u03b2_496_, lean_object* v_cmp_497_, lean_object* v_t_498_, lean_object* v_a_499_, lean_object* v_h_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_497_, v_t_498_, v_a_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21___redArg(lean_object* v_cmp_502_, lean_object* v_inst_503_, lean_object* v_t_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_502_, v_inst_503_, v_t_504_, v_a_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21___redArg___boxed(lean_object* v_cmp_507_, lean_object* v_inst_508_, lean_object* v_t_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_TreeMap_Raw_get_x21___redArg(v_cmp_507_, v_inst_508_, v_t_509_, v_a_510_);
lean_dec(v_inst_508_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21(lean_object* v_00_u03b1_512_, lean_object* v_00_u03b2_513_, lean_object* v_cmp_514_, lean_object* v_inst_515_, lean_object* v_t_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_514_, v_inst_515_, v_t_516_, v_a_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_cmp_521_, lean_object* v_inst_522_, lean_object* v_t_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_TreeMap_Raw_get_x21(v_00_u03b1_519_, v_00_u03b2_520_, v_cmp_521_, v_inst_522_, v_t_523_, v_a_524_);
lean_dec(v_inst_522_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___redArg(lean_object* v_cmp_526_, lean_object* v_t_527_, lean_object* v_a_528_, lean_object* v_fallback_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_526_, v_t_527_, v_a_528_, v_fallback_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___redArg___boxed(lean_object* v_cmp_531_, lean_object* v_t_532_, lean_object* v_a_533_, lean_object* v_fallback_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_TreeMap_Raw_getD___redArg(v_cmp_531_, v_t_532_, v_a_533_, v_fallback_534_);
lean_dec(v_fallback_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_cmp_538_, lean_object* v_t_539_, lean_object* v_a_540_, lean_object* v_fallback_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_538_, v_t_539_, v_a_540_, v_fallback_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___boxed(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, lean_object* v_cmp_545_, lean_object* v_t_546_, lean_object* v_a_547_, lean_object* v_fallback_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_TreeMap_Raw_getD(v_00_u03b1_543_, v_00_u03b2_544_, v_cmp_545_, v_t_546_, v_a_547_, v_fallback_548_);
lean_dec(v_fallback_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object* v_cmp_550_, lean_object* v_m_551_, lean_object* v_a_552_, lean_object* v_h_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_550_, v_m_551_, v_a_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object* v_cmp_555_, lean_object* v_m_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_555_, v_m_556_, v_a_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object* v_cmp_559_, lean_object* v_inst_560_, lean_object* v_m_561_, lean_object* v_a_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_559_, v_inst_560_, v_m_561_, v_a_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_cmp_564_, lean_object* v_inst_565_, lean_object* v_m_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2(v_cmp_564_, v_inst_565_, v_m_566_, v_a_567_);
lean_dec(v_inst_565_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg(lean_object* v_cmp_569_){
_start:
{
lean_object* v___f_570_; lean_object* v___f_571_; lean_object* v___f_572_; lean_object* v___x_573_; 
lean_inc_ref_n(v_cmp_569_, 2);
v___f_570_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__0), 4, 1);
lean_closure_set(v___f_570_, 0, v_cmp_569_);
v___f_571_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__1), 3, 1);
lean_closure_set(v___f_571_, 0, v_cmp_569_);
v___f_572_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_572_, 0, v_cmp_569_);
v___x_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_573_, 0, v___f_570_);
lean_ctor_set(v___x_573_, 1, v___f_571_);
lean_ctor_set(v___x_573_, 2, v___f_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem(lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_cmp_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg(v_cmp_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x3f___redArg(lean_object* v_cmp_578_, lean_object* v_t_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_578_, v_t_579_, v_a_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x3f(lean_object* v_00_u03b1_582_, lean_object* v_00_u03b2_583_, lean_object* v_cmp_584_, lean_object* v_t_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_584_, v_t_585_, v_a_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey___redArg(lean_object* v_cmp_588_, lean_object* v_t_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_588_, v_t_589_, v_a_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey(lean_object* v_00_u03b1_592_, lean_object* v_00_u03b2_593_, lean_object* v_cmp_594_, lean_object* v_t_595_, lean_object* v_a_596_, lean_object* v_h_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_594_, v_t_595_, v_a_596_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21___redArg(lean_object* v_cmp_599_, lean_object* v_inst_600_, lean_object* v_t_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_599_, v_t_601_, v_a_602_, v_inst_600_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21___redArg___boxed(lean_object* v_cmp_604_, lean_object* v_inst_605_, lean_object* v_t_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_TreeMap_Raw_getKey_x21___redArg(v_cmp_604_, v_inst_605_, v_t_606_, v_a_607_);
lean_dec(v_inst_605_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21(lean_object* v_00_u03b1_609_, lean_object* v_00_u03b2_610_, lean_object* v_cmp_611_, lean_object* v_inst_612_, lean_object* v_t_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_611_, v_t_613_, v_a_614_, v_inst_612_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_616_, lean_object* v_00_u03b2_617_, lean_object* v_cmp_618_, lean_object* v_inst_619_, lean_object* v_t_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Std_TreeMap_Raw_getKey_x21(v_00_u03b1_616_, v_00_u03b2_617_, v_cmp_618_, v_inst_619_, v_t_620_, v_a_621_);
lean_dec(v_inst_619_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___redArg(lean_object* v_cmp_623_, lean_object* v_t_624_, lean_object* v_a_625_, lean_object* v_fallback_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_623_, v_t_624_, v_a_625_, v_fallback_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___redArg___boxed(lean_object* v_cmp_628_, lean_object* v_t_629_, lean_object* v_a_630_, lean_object* v_fallback_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_TreeMap_Raw_getKeyD___redArg(v_cmp_628_, v_t_629_, v_a_630_, v_fallback_631_);
lean_dec(v_fallback_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD(lean_object* v_00_u03b1_633_, lean_object* v_00_u03b2_634_, lean_object* v_cmp_635_, lean_object* v_t_636_, lean_object* v_a_637_, lean_object* v_fallback_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_635_, v_t_636_, v_a_637_, v_fallback_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_640_, lean_object* v_00_u03b2_641_, lean_object* v_cmp_642_, lean_object* v_t_643_, lean_object* v_a_644_, lean_object* v_fallback_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_TreeMap_Raw_getKeyD(v_00_u03b1_640_, v_00_u03b2_641_, v_cmp_642_, v_t_643_, v_a_644_, v_fallback_645_);
lean_dec(v_fallback_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___redArg(lean_object* v_t_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___redArg___boxed(lean_object* v_t_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_TreeMap_Raw_minEntry_x3f___redArg(v_t_649_);
lean_dec(v_t_649_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b2_652_, lean_object* v_cmp_653_, lean_object* v_t_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___boxed(lean_object* v_00_u03b1_656_, lean_object* v_00_u03b2_657_, lean_object* v_cmp_658_, lean_object* v_t_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_TreeMap_Raw_minEntry_x3f(v_00_u03b1_656_, v_00_u03b2_657_, v_cmp_658_, v_t_659_);
lean_dec(v_t_659_);
lean_dec_ref(v_cmp_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___redArg(lean_object* v_inst_661_, lean_object* v_t_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_661_, v_t_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___redArg___boxed(lean_object* v_inst_664_, lean_object* v_t_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_TreeMap_Raw_minEntry_x21___redArg(v_inst_664_, v_t_665_);
lean_dec(v_t_665_);
lean_dec_ref(v_inst_664_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21(lean_object* v_00_u03b1_667_, lean_object* v_00_u03b2_668_, lean_object* v_cmp_669_, lean_object* v_inst_670_, lean_object* v_t_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_670_, v_t_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___boxed(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_cmp_675_, lean_object* v_inst_676_, lean_object* v_t_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_TreeMap_Raw_minEntry_x21(v_00_u03b1_673_, v_00_u03b2_674_, v_cmp_675_, v_inst_676_, v_t_677_);
lean_dec(v_t_677_);
lean_dec_ref(v_inst_676_);
lean_dec_ref(v_cmp_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___redArg(lean_object* v_t_679_, lean_object* v_fallback_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_679_, v_fallback_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___redArg___boxed(lean_object* v_t_682_, lean_object* v_fallback_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_TreeMap_Raw_minEntryD___redArg(v_t_682_, v_fallback_683_);
lean_dec_ref(v_fallback_683_);
lean_dec(v_t_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD(lean_object* v_00_u03b1_685_, lean_object* v_00_u03b2_686_, lean_object* v_cmp_687_, lean_object* v_t_688_, lean_object* v_fallback_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_688_, v_fallback_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___boxed(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_cmp_693_, lean_object* v_t_694_, lean_object* v_fallback_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Std_TreeMap_Raw_minEntryD(v_00_u03b1_691_, v_00_u03b2_692_, v_cmp_693_, v_t_694_, v_fallback_695_);
lean_dec_ref(v_fallback_695_);
lean_dec(v_t_694_);
lean_dec_ref(v_cmp_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___redArg(lean_object* v_t_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___redArg___boxed(lean_object* v_t_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Std_TreeMap_Raw_maxEntry_x3f___redArg(v_t_699_);
lean_dec(v_t_699_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f(lean_object* v_00_u03b1_701_, lean_object* v_00_u03b2_702_, lean_object* v_cmp_703_, lean_object* v_t_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___boxed(lean_object* v_00_u03b1_706_, lean_object* v_00_u03b2_707_, lean_object* v_cmp_708_, lean_object* v_t_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_TreeMap_Raw_maxEntry_x3f(v_00_u03b1_706_, v_00_u03b2_707_, v_cmp_708_, v_t_709_);
lean_dec(v_t_709_);
lean_dec_ref(v_cmp_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___redArg(lean_object* v_inst_711_, lean_object* v_t_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_711_, v_t_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___redArg___boxed(lean_object* v_inst_714_, lean_object* v_t_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_TreeMap_Raw_maxEntry_x21___redArg(v_inst_714_, v_t_715_);
lean_dec(v_t_715_);
lean_dec_ref(v_inst_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21(lean_object* v_00_u03b1_717_, lean_object* v_00_u03b2_718_, lean_object* v_cmp_719_, lean_object* v_inst_720_, lean_object* v_t_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_720_, v_t_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___boxed(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_cmp_725_, lean_object* v_inst_726_, lean_object* v_t_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_TreeMap_Raw_maxEntry_x21(v_00_u03b1_723_, v_00_u03b2_724_, v_cmp_725_, v_inst_726_, v_t_727_);
lean_dec(v_t_727_);
lean_dec_ref(v_inst_726_);
lean_dec_ref(v_cmp_725_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___redArg(lean_object* v_t_729_, lean_object* v_fallback_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_729_, v_fallback_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___redArg___boxed(lean_object* v_t_732_, lean_object* v_fallback_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_TreeMap_Raw_maxEntryD___redArg(v_t_732_, v_fallback_733_);
lean_dec_ref(v_fallback_733_);
lean_dec(v_t_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD(lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_cmp_737_, lean_object* v_t_738_, lean_object* v_fallback_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_738_, v_fallback_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___boxed(lean_object* v_00_u03b1_741_, lean_object* v_00_u03b2_742_, lean_object* v_cmp_743_, lean_object* v_t_744_, lean_object* v_fallback_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Std_TreeMap_Raw_maxEntryD(v_00_u03b1_741_, v_00_u03b2_742_, v_cmp_743_, v_t_744_, v_fallback_745_);
lean_dec_ref(v_fallback_745_);
lean_dec(v_t_744_);
lean_dec_ref(v_cmp_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___redArg(lean_object* v_t_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___redArg___boxed(lean_object* v_t_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_TreeMap_Raw_minKey_x3f___redArg(v_t_749_);
lean_dec(v_t_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f(lean_object* v_00_u03b1_751_, lean_object* v_00_u03b2_752_, lean_object* v_cmp_753_, lean_object* v_t_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___boxed(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_cmp_758_, lean_object* v_t_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_TreeMap_Raw_minKey_x3f(v_00_u03b1_756_, v_00_u03b2_757_, v_cmp_758_, v_t_759_);
lean_dec(v_t_759_);
lean_dec_ref(v_cmp_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___redArg(lean_object* v_inst_761_, lean_object* v_t_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_761_, v_t_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___redArg___boxed(lean_object* v_inst_764_, lean_object* v_t_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_TreeMap_Raw_minKey_x21___redArg(v_inst_764_, v_t_765_);
lean_dec(v_t_765_);
lean_dec(v_inst_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21(lean_object* v_00_u03b1_767_, lean_object* v_00_u03b2_768_, lean_object* v_cmp_769_, lean_object* v_inst_770_, lean_object* v_t_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_770_, v_t_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___boxed(lean_object* v_00_u03b1_773_, lean_object* v_00_u03b2_774_, lean_object* v_cmp_775_, lean_object* v_inst_776_, lean_object* v_t_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_TreeMap_Raw_minKey_x21(v_00_u03b1_773_, v_00_u03b2_774_, v_cmp_775_, v_inst_776_, v_t_777_);
lean_dec(v_t_777_);
lean_dec(v_inst_776_);
lean_dec_ref(v_cmp_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___redArg(lean_object* v_t_779_, lean_object* v_fallback_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_779_, v_fallback_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___redArg___boxed(lean_object* v_t_782_, lean_object* v_fallback_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_TreeMap_Raw_minKeyD___redArg(v_t_782_, v_fallback_783_);
lean_dec(v_fallback_783_);
lean_dec(v_t_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD(lean_object* v_00_u03b1_785_, lean_object* v_00_u03b2_786_, lean_object* v_cmp_787_, lean_object* v_t_788_, lean_object* v_fallback_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_788_, v_fallback_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___boxed(lean_object* v_00_u03b1_791_, lean_object* v_00_u03b2_792_, lean_object* v_cmp_793_, lean_object* v_t_794_, lean_object* v_fallback_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Std_TreeMap_Raw_minKeyD(v_00_u03b1_791_, v_00_u03b2_792_, v_cmp_793_, v_t_794_, v_fallback_795_);
lean_dec(v_fallback_795_);
lean_dec(v_t_794_);
lean_dec_ref(v_cmp_793_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___redArg(lean_object* v_t_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___redArg___boxed(lean_object* v_t_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_TreeMap_Raw_maxKey_x3f___redArg(v_t_799_);
lean_dec(v_t_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_cmp_803_, lean_object* v_t_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___boxed(lean_object* v_00_u03b1_806_, lean_object* v_00_u03b2_807_, lean_object* v_cmp_808_, lean_object* v_t_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_TreeMap_Raw_maxKey_x3f(v_00_u03b1_806_, v_00_u03b2_807_, v_cmp_808_, v_t_809_);
lean_dec(v_t_809_);
lean_dec_ref(v_cmp_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___redArg(lean_object* v_inst_811_, lean_object* v_t_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_811_, v_t_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___redArg___boxed(lean_object* v_inst_814_, lean_object* v_t_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_TreeMap_Raw_maxKey_x21___redArg(v_inst_814_, v_t_815_);
lean_dec(v_t_815_);
lean_dec(v_inst_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21(lean_object* v_00_u03b1_817_, lean_object* v_00_u03b2_818_, lean_object* v_cmp_819_, lean_object* v_inst_820_, lean_object* v_t_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_820_, v_t_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___boxed(lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_cmp_825_, lean_object* v_inst_826_, lean_object* v_t_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_TreeMap_Raw_maxKey_x21(v_00_u03b1_823_, v_00_u03b2_824_, v_cmp_825_, v_inst_826_, v_t_827_);
lean_dec(v_t_827_);
lean_dec(v_inst_826_);
lean_dec_ref(v_cmp_825_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___redArg(lean_object* v_t_829_, lean_object* v_fallback_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_829_, v_fallback_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___redArg___boxed(lean_object* v_t_832_, lean_object* v_fallback_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_TreeMap_Raw_maxKeyD___redArg(v_t_832_, v_fallback_833_);
lean_dec(v_fallback_833_);
lean_dec(v_t_832_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD(lean_object* v_00_u03b1_835_, lean_object* v_00_u03b2_836_, lean_object* v_cmp_837_, lean_object* v_t_838_, lean_object* v_fallback_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_838_, v_fallback_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___boxed(lean_object* v_00_u03b1_841_, lean_object* v_00_u03b2_842_, lean_object* v_cmp_843_, lean_object* v_t_844_, lean_object* v_fallback_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_TreeMap_Raw_maxKeyD(v_00_u03b1_841_, v_00_u03b2_842_, v_cmp_843_, v_t_844_, v_fallback_845_);
lean_dec(v_fallback_845_);
lean_dec(v_t_844_);
lean_dec_ref(v_cmp_843_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg(lean_object* v_t_847_, lean_object* v_n_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_847_, v_n_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_850_, lean_object* v_n_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg(v_t_850_, v_n_851_);
lean_dec(v_t_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f(lean_object* v_00_u03b1_853_, lean_object* v_00_u03b2_854_, lean_object* v_cmp_855_, lean_object* v_t_856_, lean_object* v_n_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_856_, v_n_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_859_, lean_object* v_00_u03b2_860_, lean_object* v_cmp_861_, lean_object* v_t_862_, lean_object* v_n_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_TreeMap_Raw_entryAtIdx_x3f(v_00_u03b1_859_, v_00_u03b2_860_, v_cmp_861_, v_t_862_, v_n_863_);
lean_dec(v_t_862_);
lean_dec_ref(v_cmp_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___redArg(lean_object* v_inst_865_, lean_object* v_t_866_, lean_object* v_n_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_865_, v_t_866_, v_n_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_869_, lean_object* v_t_870_, lean_object* v_n_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_TreeMap_Raw_entryAtIdx_x21___redArg(v_inst_869_, v_t_870_, v_n_871_);
lean_dec(v_t_870_);
lean_dec_ref(v_inst_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21(lean_object* v_00_u03b1_873_, lean_object* v_00_u03b2_874_, lean_object* v_cmp_875_, lean_object* v_inst_876_, lean_object* v_t_877_, lean_object* v_n_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_876_, v_t_877_, v_n_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_880_, lean_object* v_00_u03b2_881_, lean_object* v_cmp_882_, lean_object* v_inst_883_, lean_object* v_t_884_, lean_object* v_n_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_TreeMap_Raw_entryAtIdx_x21(v_00_u03b1_880_, v_00_u03b2_881_, v_cmp_882_, v_inst_883_, v_t_884_, v_n_885_);
lean_dec(v_t_884_);
lean_dec_ref(v_inst_883_);
lean_dec_ref(v_cmp_882_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___redArg(lean_object* v_t_887_, lean_object* v_n_888_, lean_object* v_fallback_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_887_, v_n_888_, v_fallback_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___redArg___boxed(lean_object* v_t_891_, lean_object* v_n_892_, lean_object* v_fallback_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Std_TreeMap_Raw_entryAtIdxD___redArg(v_t_891_, v_n_892_, v_fallback_893_);
lean_dec_ref(v_fallback_893_);
lean_dec(v_t_891_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_cmp_897_, lean_object* v_t_898_, lean_object* v_n_899_, lean_object* v_fallback_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_898_, v_n_899_, v_fallback_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___boxed(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_cmp_904_, lean_object* v_t_905_, lean_object* v_n_906_, lean_object* v_fallback_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_TreeMap_Raw_entryAtIdxD(v_00_u03b1_902_, v_00_u03b2_903_, v_cmp_904_, v_t_905_, v_n_906_, v_fallback_907_);
lean_dec_ref(v_fallback_907_);
lean_dec(v_t_905_);
lean_dec_ref(v_cmp_904_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg(lean_object* v_t_909_, lean_object* v_n_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_909_, v_n_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_912_, lean_object* v_n_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg(v_t_912_, v_n_913_);
lean_dec(v_t_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f(lean_object* v_00_u03b1_915_, lean_object* v_00_u03b2_916_, lean_object* v_cmp_917_, lean_object* v_t_918_, lean_object* v_n_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_918_, v_n_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_921_, lean_object* v_00_u03b2_922_, lean_object* v_cmp_923_, lean_object* v_t_924_, lean_object* v_n_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Std_TreeMap_Raw_keyAtIdx_x3f(v_00_u03b1_921_, v_00_u03b2_922_, v_cmp_923_, v_t_924_, v_n_925_);
lean_dec(v_t_924_);
lean_dec_ref(v_cmp_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___redArg(lean_object* v_inst_927_, lean_object* v_t_928_, lean_object* v_n_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_927_, v_t_928_, v_n_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_931_, lean_object* v_t_932_, lean_object* v_n_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_TreeMap_Raw_keyAtIdx_x21___redArg(v_inst_931_, v_t_932_, v_n_933_);
lean_dec(v_t_932_);
lean_dec(v_inst_931_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_cmp_937_, lean_object* v_inst_938_, lean_object* v_t_939_, lean_object* v_n_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_938_, v_t_939_, v_n_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_942_, lean_object* v_00_u03b2_943_, lean_object* v_cmp_944_, lean_object* v_inst_945_, lean_object* v_t_946_, lean_object* v_n_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Std_TreeMap_Raw_keyAtIdx_x21(v_00_u03b1_942_, v_00_u03b2_943_, v_cmp_944_, v_inst_945_, v_t_946_, v_n_947_);
lean_dec(v_t_946_);
lean_dec(v_inst_945_);
lean_dec_ref(v_cmp_944_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___redArg(lean_object* v_t_949_, lean_object* v_n_950_, lean_object* v_fallback_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_949_, v_n_950_, v_fallback_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___redArg___boxed(lean_object* v_t_953_, lean_object* v_n_954_, lean_object* v_fallback_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_TreeMap_Raw_keyAtIdxD___redArg(v_t_953_, v_n_954_, v_fallback_955_);
lean_dec(v_fallback_955_);
lean_dec(v_t_953_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD(lean_object* v_00_u03b1_957_, lean_object* v_00_u03b2_958_, lean_object* v_cmp_959_, lean_object* v_t_960_, lean_object* v_n_961_, lean_object* v_fallback_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_960_, v_n_961_, v_fallback_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___boxed(lean_object* v_00_u03b1_964_, lean_object* v_00_u03b2_965_, lean_object* v_cmp_966_, lean_object* v_t_967_, lean_object* v_n_968_, lean_object* v_fallback_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_TreeMap_Raw_keyAtIdxD(v_00_u03b1_964_, v_00_u03b2_965_, v_cmp_966_, v_t_967_, v_n_968_, v_fallback_969_);
lean_dec(v_fallback_969_);
lean_dec(v_t_967_);
lean_dec_ref(v_cmp_966_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x3f___redArg(lean_object* v_cmp_971_, lean_object* v_t_972_, lean_object* v_k_973_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_box(0);
v___x_975_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_971_, v_k_973_, v___x_974_, v_t_972_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x3f(lean_object* v_00_u03b1_976_, lean_object* v_00_u03b2_977_, lean_object* v_cmp_978_, lean_object* v_t_979_, lean_object* v_k_980_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_box(0);
v___x_982_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_978_, v_k_980_, v___x_981_, v_t_979_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x3f___redArg(lean_object* v_cmp_983_, lean_object* v_t_984_, lean_object* v_k_985_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_box(0);
v___x_987_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_983_, v_k_985_, v___x_986_, v_t_984_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x3f(lean_object* v_00_u03b1_988_, lean_object* v_00_u03b2_989_, lean_object* v_cmp_990_, lean_object* v_t_991_, lean_object* v_k_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_box(0);
v___x_994_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_990_, v_k_992_, v___x_993_, v_t_991_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x3f___redArg(lean_object* v_cmp_995_, lean_object* v_t_996_, lean_object* v_k_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_box(0);
v___x_999_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_995_, v_k_997_, v___x_998_, v_t_996_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x3f(lean_object* v_00_u03b1_1000_, lean_object* v_00_u03b2_1001_, lean_object* v_cmp_1002_, lean_object* v_t_1003_, lean_object* v_k_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_box(0);
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1002_, v_k_1004_, v___x_1005_, v_t_1003_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x3f___redArg(lean_object* v_cmp_1007_, lean_object* v_t_1008_, lean_object* v_k_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1007_, v_k_1009_, v___x_1010_, v_t_1008_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x3f(lean_object* v_00_u03b1_1012_, lean_object* v_00_u03b2_1013_, lean_object* v_cmp_1014_, lean_object* v_t_1015_, lean_object* v_k_1016_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_box(0);
v___x_1018_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1014_, v_k_1016_, v___x_1017_, v_t_1015_);
return v___x_1018_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1022_ = ((lean_object*)(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__2));
v___x_1023_ = lean_unsigned_to_nat(14u);
v___x_1024_ = lean_unsigned_to_nat(22u);
v___x_1025_ = ((lean_object*)(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__1));
v___x_1026_ = ((lean_object*)(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__0));
v___x_1027_ = l_mkPanicMessageWithDecl(v___x_1026_, v___x_1025_, v___x_1024_, v___x_1023_, v___x_1022_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___redArg(lean_object* v_cmp_1028_, lean_object* v_inst_1029_, lean_object* v_t_1030_, lean_object* v_k_1031_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1028_, v_k_1031_, v___x_1032_, v_t_1030_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1035_ = l_panic___redArg(v_inst_1029_, v___x_1034_);
return v___x_1035_;
}
else
{
lean_object* v_val_1036_; 
v_val_1036_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_val_1036_);
lean_dec_ref_known(v___x_1033_, 1);
return v_val_1036_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1037_, lean_object* v_inst_1038_, lean_object* v_t_1039_, lean_object* v_k_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_TreeMap_Raw_getEntryGE_x21___redArg(v_cmp_1037_, v_inst_1038_, v_t_1039_, v_k_1040_);
lean_dec_ref(v_inst_1038_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_cmp_1044_, lean_object* v_inst_1045_, lean_object* v_t_1046_, lean_object* v_k_1047_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_box(0);
v___x_1049_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1044_, v_k_1047_, v___x_1048_, v_t_1046_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1051_ = l_panic___redArg(v_inst_1045_, v___x_1050_);
return v___x_1051_;
}
else
{
lean_object* v_val_1052_; 
v_val_1052_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_val_1052_);
lean_dec_ref_known(v___x_1049_, 1);
return v_val_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1053_, lean_object* v_00_u03b2_1054_, lean_object* v_cmp_1055_, lean_object* v_inst_1056_, lean_object* v_t_1057_, lean_object* v_k_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_TreeMap_Raw_getEntryGE_x21(v_00_u03b1_1053_, v_00_u03b2_1054_, v_cmp_1055_, v_inst_1056_, v_t_1057_, v_k_1058_);
lean_dec_ref(v_inst_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21___redArg(lean_object* v_cmp_1060_, lean_object* v_inst_1061_, lean_object* v_t_1062_, lean_object* v_k_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1060_, v_k_1063_, v___x_1064_, v_t_1062_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1067_ = l_panic___redArg(v_inst_1061_, v___x_1066_);
return v___x_1067_;
}
else
{
lean_object* v_val_1068_; 
v_val_1068_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_val_1068_);
lean_dec_ref_known(v___x_1065_, 1);
return v_val_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1069_, lean_object* v_inst_1070_, lean_object* v_t_1071_, lean_object* v_k_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_TreeMap_Raw_getEntryGT_x21___redArg(v_cmp_1069_, v_inst_1070_, v_t_1071_, v_k_1072_);
lean_dec_ref(v_inst_1070_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21(lean_object* v_00_u03b1_1074_, lean_object* v_00_u03b2_1075_, lean_object* v_cmp_1076_, lean_object* v_inst_1077_, lean_object* v_t_1078_, lean_object* v_k_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1076_, v_k_1079_, v___x_1080_, v_t_1078_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1083_ = l_panic___redArg(v_inst_1077_, v___x_1082_);
return v___x_1083_;
}
else
{
lean_object* v_val_1084_; 
v_val_1084_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v___x_1081_, 1);
return v_val_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1085_, lean_object* v_00_u03b2_1086_, lean_object* v_cmp_1087_, lean_object* v_inst_1088_, lean_object* v_t_1089_, lean_object* v_k_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Std_TreeMap_Raw_getEntryGT_x21(v_00_u03b1_1085_, v_00_u03b2_1086_, v_cmp_1087_, v_inst_1088_, v_t_1089_, v_k_1090_);
lean_dec_ref(v_inst_1088_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21___redArg(lean_object* v_cmp_1092_, lean_object* v_inst_1093_, lean_object* v_t_1094_, lean_object* v_k_1095_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1092_, v_k_1095_, v___x_1096_, v_t_1094_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1099_ = l_panic___redArg(v_inst_1093_, v___x_1098_);
return v___x_1099_;
}
else
{
lean_object* v_val_1100_; 
v_val_1100_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_val_1100_);
lean_dec_ref_known(v___x_1097_, 1);
return v_val_1100_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1101_, lean_object* v_inst_1102_, lean_object* v_t_1103_, lean_object* v_k_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_TreeMap_Raw_getEntryLE_x21___redArg(v_cmp_1101_, v_inst_1102_, v_t_1103_, v_k_1104_);
lean_dec_ref(v_inst_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_cmp_1108_, lean_object* v_inst_1109_, lean_object* v_t_1110_, lean_object* v_k_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_box(0);
v___x_1113_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1108_, v_k_1111_, v___x_1112_, v_t_1110_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1115_ = l_panic___redArg(v_inst_1109_, v___x_1114_);
return v___x_1115_;
}
else
{
lean_object* v_val_1116_; 
v_val_1116_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_val_1116_);
lean_dec_ref_known(v___x_1113_, 1);
return v_val_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_00_u03b2_1118_, lean_object* v_cmp_1119_, lean_object* v_inst_1120_, lean_object* v_t_1121_, lean_object* v_k_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_TreeMap_Raw_getEntryLE_x21(v_00_u03b1_1117_, v_00_u03b2_1118_, v_cmp_1119_, v_inst_1120_, v_t_1121_, v_k_1122_);
lean_dec_ref(v_inst_1120_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21___redArg(lean_object* v_cmp_1124_, lean_object* v_inst_1125_, lean_object* v_t_1126_, lean_object* v_k_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1124_, v_k_1127_, v___x_1128_, v_t_1126_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1131_ = l_panic___redArg(v_inst_1125_, v___x_1130_);
return v___x_1131_;
}
else
{
lean_object* v_val_1132_; 
v_val_1132_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_val_1132_);
lean_dec_ref_known(v___x_1129_, 1);
return v_val_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1133_, lean_object* v_inst_1134_, lean_object* v_t_1135_, lean_object* v_k_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_TreeMap_Raw_getEntryLT_x21___redArg(v_cmp_1133_, v_inst_1134_, v_t_1135_, v_k_1136_);
lean_dec_ref(v_inst_1134_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21(lean_object* v_00_u03b1_1138_, lean_object* v_00_u03b2_1139_, lean_object* v_cmp_1140_, lean_object* v_inst_1141_, lean_object* v_t_1142_, lean_object* v_k_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_box(0);
v___x_1145_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1140_, v_k_1143_, v___x_1144_, v_t_1142_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1147_ = l_panic___redArg(v_inst_1141_, v___x_1146_);
return v___x_1147_;
}
else
{
lean_object* v_val_1148_; 
v_val_1148_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_val_1148_);
lean_dec_ref_known(v___x_1145_, 1);
return v_val_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1149_, lean_object* v_00_u03b2_1150_, lean_object* v_cmp_1151_, lean_object* v_inst_1152_, lean_object* v_t_1153_, lean_object* v_k_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_TreeMap_Raw_getEntryLT_x21(v_00_u03b1_1149_, v_00_u03b2_1150_, v_cmp_1151_, v_inst_1152_, v_t_1153_, v_k_1154_);
lean_dec_ref(v_inst_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___redArg(lean_object* v_cmp_1156_, lean_object* v_t_1157_, lean_object* v_k_1158_, lean_object* v_fallback_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_box(0);
v___x_1161_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1156_, v_k_1158_, v___x_1160_, v_t_1157_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_inc_ref(v_fallback_1159_);
return v_fallback_1159_;
}
else
{
lean_object* v_val_1162_; 
v_val_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_val_1162_);
lean_dec_ref_known(v___x_1161_, 1);
return v_val_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___redArg___boxed(lean_object* v_cmp_1163_, lean_object* v_t_1164_, lean_object* v_k_1165_, lean_object* v_fallback_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Std_TreeMap_Raw_getEntryGED___redArg(v_cmp_1163_, v_t_1164_, v_k_1165_, v_fallback_1166_);
lean_dec_ref(v_fallback_1166_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED(lean_object* v_00_u03b1_1168_, lean_object* v_00_u03b2_1169_, lean_object* v_cmp_1170_, lean_object* v_t_1171_, lean_object* v_k_1172_, lean_object* v_fallback_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_box(0);
v___x_1175_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1170_, v_k_1172_, v___x_1174_, v_t_1171_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_inc_ref(v_fallback_1173_);
return v_fallback_1173_;
}
else
{
lean_object* v_val_1176_; 
v_val_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_val_1176_);
lean_dec_ref_known(v___x_1175_, 1);
return v_val_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___boxed(lean_object* v_00_u03b1_1177_, lean_object* v_00_u03b2_1178_, lean_object* v_cmp_1179_, lean_object* v_t_1180_, lean_object* v_k_1181_, lean_object* v_fallback_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Std_TreeMap_Raw_getEntryGED(v_00_u03b1_1177_, v_00_u03b2_1178_, v_cmp_1179_, v_t_1180_, v_k_1181_, v_fallback_1182_);
lean_dec_ref(v_fallback_1182_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___redArg(lean_object* v_cmp_1184_, lean_object* v_t_1185_, lean_object* v_k_1186_, lean_object* v_fallback_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_box(0);
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1184_, v_k_1186_, v___x_1188_, v_t_1185_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_inc_ref(v_fallback_1187_);
return v_fallback_1187_;
}
else
{
lean_object* v_val_1190_; 
v_val_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_val_1190_);
lean_dec_ref_known(v___x_1189_, 1);
return v_val_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___redArg___boxed(lean_object* v_cmp_1191_, lean_object* v_t_1192_, lean_object* v_k_1193_, lean_object* v_fallback_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Std_TreeMap_Raw_getEntryGTD___redArg(v_cmp_1191_, v_t_1192_, v_k_1193_, v_fallback_1194_);
lean_dec_ref(v_fallback_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD(lean_object* v_00_u03b1_1196_, lean_object* v_00_u03b2_1197_, lean_object* v_cmp_1198_, lean_object* v_t_1199_, lean_object* v_k_1200_, lean_object* v_fallback_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_box(0);
v___x_1203_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1198_, v_k_1200_, v___x_1202_, v_t_1199_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_inc_ref(v_fallback_1201_);
return v_fallback_1201_;
}
else
{
lean_object* v_val_1204_; 
v_val_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v___x_1203_, 1);
return v_val_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___boxed(lean_object* v_00_u03b1_1205_, lean_object* v_00_u03b2_1206_, lean_object* v_cmp_1207_, lean_object* v_t_1208_, lean_object* v_k_1209_, lean_object* v_fallback_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_TreeMap_Raw_getEntryGTD(v_00_u03b1_1205_, v_00_u03b2_1206_, v_cmp_1207_, v_t_1208_, v_k_1209_, v_fallback_1210_);
lean_dec_ref(v_fallback_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___redArg(lean_object* v_cmp_1212_, lean_object* v_t_1213_, lean_object* v_k_1214_, lean_object* v_fallback_1215_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1212_, v_k_1214_, v___x_1216_, v_t_1213_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_inc_ref(v_fallback_1215_);
return v_fallback_1215_;
}
else
{
lean_object* v_val_1218_; 
v_val_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_val_1218_);
lean_dec_ref_known(v___x_1217_, 1);
return v_val_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___redArg___boxed(lean_object* v_cmp_1219_, lean_object* v_t_1220_, lean_object* v_k_1221_, lean_object* v_fallback_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Std_TreeMap_Raw_getEntryLED___redArg(v_cmp_1219_, v_t_1220_, v_k_1221_, v_fallback_1222_);
lean_dec_ref(v_fallback_1222_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED(lean_object* v_00_u03b1_1224_, lean_object* v_00_u03b2_1225_, lean_object* v_cmp_1226_, lean_object* v_t_1227_, lean_object* v_k_1228_, lean_object* v_fallback_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_box(0);
v___x_1231_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1226_, v_k_1228_, v___x_1230_, v_t_1227_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_inc_ref(v_fallback_1229_);
return v_fallback_1229_;
}
else
{
lean_object* v_val_1232_; 
v_val_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_val_1232_);
lean_dec_ref_known(v___x_1231_, 1);
return v_val_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_00_u03b2_1234_, lean_object* v_cmp_1235_, lean_object* v_t_1236_, lean_object* v_k_1237_, lean_object* v_fallback_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Std_TreeMap_Raw_getEntryLED(v_00_u03b1_1233_, v_00_u03b2_1234_, v_cmp_1235_, v_t_1236_, v_k_1237_, v_fallback_1238_);
lean_dec_ref(v_fallback_1238_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___redArg(lean_object* v_cmp_1240_, lean_object* v_t_1241_, lean_object* v_k_1242_, lean_object* v_fallback_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_box(0);
v___x_1245_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1240_, v_k_1242_, v___x_1244_, v_t_1241_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_inc_ref(v_fallback_1243_);
return v_fallback_1243_;
}
else
{
lean_object* v_val_1246_; 
v_val_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v___x_1245_, 1);
return v_val_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___redArg___boxed(lean_object* v_cmp_1247_, lean_object* v_t_1248_, lean_object* v_k_1249_, lean_object* v_fallback_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_TreeMap_Raw_getEntryLTD___redArg(v_cmp_1247_, v_t_1248_, v_k_1249_, v_fallback_1250_);
lean_dec_ref(v_fallback_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD(lean_object* v_00_u03b1_1252_, lean_object* v_00_u03b2_1253_, lean_object* v_cmp_1254_, lean_object* v_t_1255_, lean_object* v_k_1256_, lean_object* v_fallback_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_box(0);
v___x_1259_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1254_, v_k_1256_, v___x_1258_, v_t_1255_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_inc_ref(v_fallback_1257_);
return v_fallback_1257_;
}
else
{
lean_object* v_val_1260_; 
v_val_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_val_1260_);
lean_dec_ref_known(v___x_1259_, 1);
return v_val_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___boxed(lean_object* v_00_u03b1_1261_, lean_object* v_00_u03b2_1262_, lean_object* v_cmp_1263_, lean_object* v_t_1264_, lean_object* v_k_1265_, lean_object* v_fallback_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_TreeMap_Raw_getEntryLTD(v_00_u03b1_1261_, v_00_u03b2_1262_, v_cmp_1263_, v_t_1264_, v_k_1265_, v_fallback_1266_);
lean_dec_ref(v_fallback_1266_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x3f___redArg(lean_object* v_cmp_1268_, lean_object* v_t_1269_, lean_object* v_k_1270_){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_box(0);
v___x_1272_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1268_, v_k_1270_, v___x_1271_, v_t_1269_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x3f(lean_object* v_00_u03b1_1273_, lean_object* v_00_u03b2_1274_, lean_object* v_cmp_1275_, lean_object* v_t_1276_, lean_object* v_k_1277_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_box(0);
v___x_1279_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1275_, v_k_1277_, v___x_1278_, v_t_1276_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x3f___redArg(lean_object* v_cmp_1280_, lean_object* v_t_1281_, lean_object* v_k_1282_){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_box(0);
v___x_1284_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1280_, v_k_1282_, v___x_1283_, v_t_1281_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x3f(lean_object* v_00_u03b1_1285_, lean_object* v_00_u03b2_1286_, lean_object* v_cmp_1287_, lean_object* v_t_1288_, lean_object* v_k_1289_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1287_, v_k_1289_, v___x_1290_, v_t_1288_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x3f___redArg(lean_object* v_cmp_1292_, lean_object* v_t_1293_, lean_object* v_k_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_box(0);
v___x_1296_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1292_, v_k_1294_, v___x_1295_, v_t_1293_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x3f(lean_object* v_00_u03b1_1297_, lean_object* v_00_u03b2_1298_, lean_object* v_cmp_1299_, lean_object* v_t_1300_, lean_object* v_k_1301_){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_box(0);
v___x_1303_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1299_, v_k_1301_, v___x_1302_, v_t_1300_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x3f___redArg(lean_object* v_cmp_1304_, lean_object* v_t_1305_, lean_object* v_k_1306_){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_box(0);
v___x_1308_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1304_, v_k_1306_, v___x_1307_, v_t_1305_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x3f(lean_object* v_00_u03b1_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_cmp_1311_, lean_object* v_t_1312_, lean_object* v_k_1313_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_box(0);
v___x_1315_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1311_, v_k_1313_, v___x_1314_, v_t_1312_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21___redArg(lean_object* v_cmp_1316_, lean_object* v_inst_1317_, lean_object* v_t_1318_, lean_object* v_k_1319_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_box(0);
v___x_1321_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1316_, v_k_1319_, v___x_1320_, v_t_1318_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1323_ = l_panic___redArg(v_inst_1317_, v___x_1322_);
return v___x_1323_;
}
else
{
lean_object* v_val_1324_; 
v_val_1324_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_val_1324_);
lean_dec_ref_known(v___x_1321_, 1);
return v_val_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1325_, lean_object* v_inst_1326_, lean_object* v_t_1327_, lean_object* v_k_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_TreeMap_Raw_getKeyGE_x21___redArg(v_cmp_1325_, v_inst_1326_, v_t_1327_, v_k_1328_);
lean_dec(v_inst_1326_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21(lean_object* v_00_u03b1_1330_, lean_object* v_00_u03b2_1331_, lean_object* v_cmp_1332_, lean_object* v_inst_1333_, lean_object* v_t_1334_, lean_object* v_k_1335_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1332_, v_k_1335_, v___x_1336_, v_t_1334_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1339_ = l_panic___redArg(v_inst_1333_, v___x_1338_);
return v___x_1339_;
}
else
{
lean_object* v_val_1340_; 
v_val_1340_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_val_1340_);
lean_dec_ref_known(v___x_1337_, 1);
return v_val_1340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_cmp_1343_, lean_object* v_inst_1344_, lean_object* v_t_1345_, lean_object* v_k_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_TreeMap_Raw_getKeyGE_x21(v_00_u03b1_1341_, v_00_u03b2_1342_, v_cmp_1343_, v_inst_1344_, v_t_1345_, v_k_1346_);
lean_dec(v_inst_1344_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21___redArg(lean_object* v_cmp_1348_, lean_object* v_inst_1349_, lean_object* v_t_1350_, lean_object* v_k_1351_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_box(0);
v___x_1353_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1348_, v_k_1351_, v___x_1352_, v_t_1350_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1355_ = l_panic___redArg(v_inst_1349_, v___x_1354_);
return v___x_1355_;
}
else
{
lean_object* v_val_1356_; 
v_val_1356_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1353_, 1);
return v_val_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1357_, lean_object* v_inst_1358_, lean_object* v_t_1359_, lean_object* v_k_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_TreeMap_Raw_getKeyGT_x21___redArg(v_cmp_1357_, v_inst_1358_, v_t_1359_, v_k_1360_);
lean_dec(v_inst_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21(lean_object* v_00_u03b1_1362_, lean_object* v_00_u03b2_1363_, lean_object* v_cmp_1364_, lean_object* v_inst_1365_, lean_object* v_t_1366_, lean_object* v_k_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1364_, v_k_1367_, v___x_1368_, v_t_1366_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1371_ = l_panic___redArg(v_inst_1365_, v___x_1370_);
return v___x_1371_;
}
else
{
lean_object* v_val_1372_; 
v_val_1372_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1372_);
lean_dec_ref_known(v___x_1369_, 1);
return v_val_1372_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1373_, lean_object* v_00_u03b2_1374_, lean_object* v_cmp_1375_, lean_object* v_inst_1376_, lean_object* v_t_1377_, lean_object* v_k_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_TreeMap_Raw_getKeyGT_x21(v_00_u03b1_1373_, v_00_u03b2_1374_, v_cmp_1375_, v_inst_1376_, v_t_1377_, v_k_1378_);
lean_dec(v_inst_1376_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21___redArg(lean_object* v_cmp_1380_, lean_object* v_inst_1381_, lean_object* v_t_1382_, lean_object* v_k_1383_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_box(0);
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1380_, v_k_1383_, v___x_1384_, v_t_1382_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1387_ = l_panic___redArg(v_inst_1381_, v___x_1386_);
return v___x_1387_;
}
else
{
lean_object* v_val_1388_; 
v_val_1388_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_val_1388_);
lean_dec_ref_known(v___x_1385_, 1);
return v_val_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1389_, lean_object* v_inst_1390_, lean_object* v_t_1391_, lean_object* v_k_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Std_TreeMap_Raw_getKeyLE_x21___redArg(v_cmp_1389_, v_inst_1390_, v_t_1391_, v_k_1392_);
lean_dec(v_inst_1390_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21(lean_object* v_00_u03b1_1394_, lean_object* v_00_u03b2_1395_, lean_object* v_cmp_1396_, lean_object* v_inst_1397_, lean_object* v_t_1398_, lean_object* v_k_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_box(0);
v___x_1401_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1396_, v_k_1399_, v___x_1400_, v_t_1398_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1403_ = l_panic___redArg(v_inst_1397_, v___x_1402_);
return v___x_1403_;
}
else
{
lean_object* v_val_1404_; 
v_val_1404_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v___x_1401_, 1);
return v_val_1404_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1405_, lean_object* v_00_u03b2_1406_, lean_object* v_cmp_1407_, lean_object* v_inst_1408_, lean_object* v_t_1409_, lean_object* v_k_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Std_TreeMap_Raw_getKeyLE_x21(v_00_u03b1_1405_, v_00_u03b2_1406_, v_cmp_1407_, v_inst_1408_, v_t_1409_, v_k_1410_);
lean_dec(v_inst_1408_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21___redArg(lean_object* v_cmp_1412_, lean_object* v_inst_1413_, lean_object* v_t_1414_, lean_object* v_k_1415_){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_box(0);
v___x_1417_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1412_, v_k_1415_, v___x_1416_, v_t_1414_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1419_ = l_panic___redArg(v_inst_1413_, v___x_1418_);
return v___x_1419_;
}
else
{
lean_object* v_val_1420_; 
v_val_1420_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_val_1420_);
lean_dec_ref_known(v___x_1417_, 1);
return v_val_1420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1421_, lean_object* v_inst_1422_, lean_object* v_t_1423_, lean_object* v_k_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Std_TreeMap_Raw_getKeyLT_x21___redArg(v_cmp_1421_, v_inst_1422_, v_t_1423_, v_k_1424_);
lean_dec(v_inst_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21(lean_object* v_00_u03b1_1426_, lean_object* v_00_u03b2_1427_, lean_object* v_cmp_1428_, lean_object* v_inst_1429_, lean_object* v_t_1430_, lean_object* v_k_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_box(0);
v___x_1433_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1428_, v_k_1431_, v___x_1432_, v_t_1430_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1435_ = l_panic___redArg(v_inst_1429_, v___x_1434_);
return v___x_1435_;
}
else
{
lean_object* v_val_1436_; 
v_val_1436_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_val_1436_);
lean_dec_ref_known(v___x_1433_, 1);
return v_val_1436_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_00_u03b2_1438_, lean_object* v_cmp_1439_, lean_object* v_inst_1440_, lean_object* v_t_1441_, lean_object* v_k_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Std_TreeMap_Raw_getKeyLT_x21(v_00_u03b1_1437_, v_00_u03b2_1438_, v_cmp_1439_, v_inst_1440_, v_t_1441_, v_k_1442_);
lean_dec(v_inst_1440_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___redArg(lean_object* v_cmp_1444_, lean_object* v_t_1445_, lean_object* v_k_1446_, lean_object* v_fallback_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1444_, v_k_1446_, v___x_1448_, v_t_1445_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_inc(v_fallback_1447_);
return v_fallback_1447_;
}
else
{
lean_object* v_val_1450_; 
v_val_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_val_1450_);
lean_dec_ref_known(v___x_1449_, 1);
return v_val_1450_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___redArg___boxed(lean_object* v_cmp_1451_, lean_object* v_t_1452_, lean_object* v_k_1453_, lean_object* v_fallback_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Std_TreeMap_Raw_getKeyGED___redArg(v_cmp_1451_, v_t_1452_, v_k_1453_, v_fallback_1454_);
lean_dec(v_fallback_1454_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED(lean_object* v_00_u03b1_1456_, lean_object* v_00_u03b2_1457_, lean_object* v_cmp_1458_, lean_object* v_t_1459_, lean_object* v_k_1460_, lean_object* v_fallback_1461_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_box(0);
v___x_1463_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1458_, v_k_1460_, v___x_1462_, v_t_1459_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_inc(v_fallback_1461_);
return v_fallback_1461_;
}
else
{
lean_object* v_val_1464_; 
v_val_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_val_1464_);
lean_dec_ref_known(v___x_1463_, 1);
return v_val_1464_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___boxed(lean_object* v_00_u03b1_1465_, lean_object* v_00_u03b2_1466_, lean_object* v_cmp_1467_, lean_object* v_t_1468_, lean_object* v_k_1469_, lean_object* v_fallback_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Std_TreeMap_Raw_getKeyGED(v_00_u03b1_1465_, v_00_u03b2_1466_, v_cmp_1467_, v_t_1468_, v_k_1469_, v_fallback_1470_);
lean_dec(v_fallback_1470_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___redArg(lean_object* v_cmp_1472_, lean_object* v_t_1473_, lean_object* v_k_1474_, lean_object* v_fallback_1475_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_box(0);
v___x_1477_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1472_, v_k_1474_, v___x_1476_, v_t_1473_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_inc(v_fallback_1475_);
return v_fallback_1475_;
}
else
{
lean_object* v_val_1478_; 
v_val_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_val_1478_);
lean_dec_ref_known(v___x_1477_, 1);
return v_val_1478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___redArg___boxed(lean_object* v_cmp_1479_, lean_object* v_t_1480_, lean_object* v_k_1481_, lean_object* v_fallback_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Std_TreeMap_Raw_getKeyGTD___redArg(v_cmp_1479_, v_t_1480_, v_k_1481_, v_fallback_1482_);
lean_dec(v_fallback_1482_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD(lean_object* v_00_u03b1_1484_, lean_object* v_00_u03b2_1485_, lean_object* v_cmp_1486_, lean_object* v_t_1487_, lean_object* v_k_1488_, lean_object* v_fallback_1489_){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_box(0);
v___x_1491_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1486_, v_k_1488_, v___x_1490_, v_t_1487_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_inc(v_fallback_1489_);
return v_fallback_1489_;
}
else
{
lean_object* v_val_1492_; 
v_val_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v___x_1491_, 1);
return v_val_1492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___boxed(lean_object* v_00_u03b1_1493_, lean_object* v_00_u03b2_1494_, lean_object* v_cmp_1495_, lean_object* v_t_1496_, lean_object* v_k_1497_, lean_object* v_fallback_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Std_TreeMap_Raw_getKeyGTD(v_00_u03b1_1493_, v_00_u03b2_1494_, v_cmp_1495_, v_t_1496_, v_k_1497_, v_fallback_1498_);
lean_dec(v_fallback_1498_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___redArg(lean_object* v_cmp_1500_, lean_object* v_t_1501_, lean_object* v_k_1502_, lean_object* v_fallback_1503_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_box(0);
v___x_1505_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1500_, v_k_1502_, v___x_1504_, v_t_1501_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_inc(v_fallback_1503_);
return v_fallback_1503_;
}
else
{
lean_object* v_val_1506_; 
v_val_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_val_1506_);
lean_dec_ref_known(v___x_1505_, 1);
return v_val_1506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___redArg___boxed(lean_object* v_cmp_1507_, lean_object* v_t_1508_, lean_object* v_k_1509_, lean_object* v_fallback_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Std_TreeMap_Raw_getKeyLED___redArg(v_cmp_1507_, v_t_1508_, v_k_1509_, v_fallback_1510_);
lean_dec(v_fallback_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED(lean_object* v_00_u03b1_1512_, lean_object* v_00_u03b2_1513_, lean_object* v_cmp_1514_, lean_object* v_t_1515_, lean_object* v_k_1516_, lean_object* v_fallback_1517_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_box(0);
v___x_1519_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1514_, v_k_1516_, v___x_1518_, v_t_1515_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_inc(v_fallback_1517_);
return v_fallback_1517_;
}
else
{
lean_object* v_val_1520_; 
v_val_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v___x_1519_, 1);
return v_val_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___boxed(lean_object* v_00_u03b1_1521_, lean_object* v_00_u03b2_1522_, lean_object* v_cmp_1523_, lean_object* v_t_1524_, lean_object* v_k_1525_, lean_object* v_fallback_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Std_TreeMap_Raw_getKeyLED(v_00_u03b1_1521_, v_00_u03b2_1522_, v_cmp_1523_, v_t_1524_, v_k_1525_, v_fallback_1526_);
lean_dec(v_fallback_1526_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___redArg(lean_object* v_cmp_1528_, lean_object* v_t_1529_, lean_object* v_k_1530_, lean_object* v_fallback_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1528_, v_k_1530_, v___x_1532_, v_t_1529_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_inc(v_fallback_1531_);
return v_fallback_1531_;
}
else
{
lean_object* v_val_1534_; 
v_val_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1533_, 1);
return v_val_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___redArg___boxed(lean_object* v_cmp_1535_, lean_object* v_t_1536_, lean_object* v_k_1537_, lean_object* v_fallback_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Std_TreeMap_Raw_getKeyLTD___redArg(v_cmp_1535_, v_t_1536_, v_k_1537_, v_fallback_1538_);
lean_dec(v_fallback_1538_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD(lean_object* v_00_u03b1_1540_, lean_object* v_00_u03b2_1541_, lean_object* v_cmp_1542_, lean_object* v_t_1543_, lean_object* v_k_1544_, lean_object* v_fallback_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_box(0);
v___x_1547_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1542_, v_k_1544_, v___x_1546_, v_t_1543_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_inc(v_fallback_1545_);
return v_fallback_1545_;
}
else
{
lean_object* v_val_1548_; 
v_val_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v___x_1547_, 1);
return v_val_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___boxed(lean_object* v_00_u03b1_1549_, lean_object* v_00_u03b2_1550_, lean_object* v_cmp_1551_, lean_object* v_t_1552_, lean_object* v_k_1553_, lean_object* v_fallback_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Std_TreeMap_Raw_getKeyLTD(v_00_u03b1_1549_, v_00_u03b2_1550_, v_cmp_1551_, v_t_1552_, v_k_1553_, v_fallback_1554_);
lean_dec(v_fallback_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter___redArg(lean_object* v_f_1556_, lean_object* v_t_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_1556_, v_t_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter(lean_object* v_00_u03b1_1559_, lean_object* v_00_u03b2_1560_, lean_object* v_cmp_1561_, lean_object* v_f_1562_, lean_object* v_t_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_1562_, v_t_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_00_u03b2_1566_, lean_object* v_cmp_1567_, lean_object* v_f_1568_, lean_object* v_t_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Std_TreeMap_Raw_filter(v_00_u03b1_1565_, v_00_u03b2_1566_, v_cmp_1567_, v_f_1568_, v_t_1569_);
lean_dec_ref(v_cmp_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM___redArg(lean_object* v_inst_1571_, lean_object* v_f_1572_, lean_object* v_init_1573_, lean_object* v_t_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1571_, v_f_1572_, v_init_1573_, v_t_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM(lean_object* v_00_u03b1_1576_, lean_object* v_00_u03b2_1577_, lean_object* v_cmp_1578_, lean_object* v_00_u03b4_1579_, lean_object* v_m_1580_, lean_object* v_inst_1581_, lean_object* v_f_1582_, lean_object* v_init_1583_, lean_object* v_t_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1581_, v_f_1582_, v_init_1583_, v_t_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM___boxed(lean_object* v_00_u03b1_1586_, lean_object* v_00_u03b2_1587_, lean_object* v_cmp_1588_, lean_object* v_00_u03b4_1589_, lean_object* v_m_1590_, lean_object* v_inst_1591_, lean_object* v_f_1592_, lean_object* v_init_1593_, lean_object* v_t_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Std_TreeMap_Raw_foldlM(v_00_u03b1_1586_, v_00_u03b2_1587_, v_cmp_1588_, v_00_u03b4_1589_, v_m_1590_, v_inst_1591_, v_f_1592_, v_init_1593_, v_t_1594_);
lean_dec_ref(v_cmp_1588_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl___redArg(lean_object* v_f_1596_, lean_object* v_init_1597_, lean_object* v_t_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1596_, v_init_1597_, v_t_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl(lean_object* v_00_u03b1_1600_, lean_object* v_00_u03b2_1601_, lean_object* v_cmp_1602_, lean_object* v_00_u03b4_1603_, lean_object* v_f_1604_, lean_object* v_init_1605_, lean_object* v_t_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1604_, v_init_1605_, v_t_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl___boxed(lean_object* v_00_u03b1_1608_, lean_object* v_00_u03b2_1609_, lean_object* v_cmp_1610_, lean_object* v_00_u03b4_1611_, lean_object* v_f_1612_, lean_object* v_init_1613_, lean_object* v_t_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Std_TreeMap_Raw_foldl(v_00_u03b1_1608_, v_00_u03b2_1609_, v_cmp_1610_, v_00_u03b4_1611_, v_f_1612_, v_init_1613_, v_t_1614_);
lean_dec_ref(v_cmp_1610_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM___redArg(lean_object* v_inst_1616_, lean_object* v_f_1617_, lean_object* v_init_1618_, lean_object* v_t_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1616_, v_f_1617_, v_init_1618_, v_t_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM(lean_object* v_00_u03b1_1621_, lean_object* v_00_u03b2_1622_, lean_object* v_cmp_1623_, lean_object* v_00_u03b4_1624_, lean_object* v_m_1625_, lean_object* v_inst_1626_, lean_object* v_f_1627_, lean_object* v_init_1628_, lean_object* v_t_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1626_, v_f_1627_, v_init_1628_, v_t_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM___boxed(lean_object* v_00_u03b1_1631_, lean_object* v_00_u03b2_1632_, lean_object* v_cmp_1633_, lean_object* v_00_u03b4_1634_, lean_object* v_m_1635_, lean_object* v_inst_1636_, lean_object* v_f_1637_, lean_object* v_init_1638_, lean_object* v_t_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Std_TreeMap_Raw_foldrM(v_00_u03b1_1631_, v_00_u03b2_1632_, v_cmp_1633_, v_00_u03b4_1634_, v_m_1635_, v_inst_1636_, v_f_1637_, v_init_1638_, v_t_1639_);
lean_dec_ref(v_cmp_1633_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___redArg___lam__0(lean_object* v_f_1641_, lean_object* v_x1_1642_, lean_object* v_x2_1643_, lean_object* v_x3_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_apply_3(v_f_1641_, v_x1_1642_, v_x2_1643_, v_x3_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___redArg(lean_object* v_f_1665_, lean_object* v_init_1666_, lean_object* v_t_1667_){
_start:
{
lean_object* v___f_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___f_1668_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1668_, 0, v_f_1665_);
v___x_1669_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1670_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1669_, v___f_1668_, v_init_1666_, v_t_1667_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr(lean_object* v_00_u03b1_1671_, lean_object* v_00_u03b2_1672_, lean_object* v_cmp_1673_, lean_object* v_00_u03b4_1674_, lean_object* v_f_1675_, lean_object* v_init_1676_, lean_object* v_t_1677_){
_start:
{
lean_object* v___f_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___f_1678_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1678_, 0, v_f_1675_);
v___x_1679_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1680_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1679_, v___f_1678_, v_init_1676_, v_t_1677_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___boxed(lean_object* v_00_u03b1_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_cmp_1683_, lean_object* v_00_u03b4_1684_, lean_object* v_f_1685_, lean_object* v_init_1686_, lean_object* v_t_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_TreeMap_Raw_foldr(v_00_u03b1_1681_, v_00_u03b2_1682_, v_cmp_1683_, v_00_u03b4_1684_, v_f_1685_, v_init_1686_, v_t_1687_);
lean_dec_ref(v_cmp_1683_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition___redArg___lam__0(lean_object* v_f_1689_, lean_object* v_cmp_1690_, lean_object* v_x_1691_, lean_object* v_a_1692_, lean_object* v_b_1693_){
_start:
{
lean_object* v_fst_1694_; lean_object* v_snd_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1709_; 
v_fst_1694_ = lean_ctor_get(v_x_1691_, 0);
v_snd_1695_ = lean_ctor_get(v_x_1691_, 1);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_x_1691_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1697_ = v_x_1691_;
v_isShared_1698_ = v_isSharedCheck_1709_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_snd_1695_);
lean_inc(v_fst_1694_);
lean_dec(v_x_1691_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1709_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; uint8_t v___x_1700_; 
lean_inc(v_b_1693_);
lean_inc(v_a_1692_);
v___x_1699_ = lean_apply_2(v_f_1689_, v_a_1692_, v_b_1693_);
v___x_1700_ = lean_unbox(v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1701_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1690_, v_a_1692_, v_b_1693_, v_snd_1695_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v___x_1701_);
v___x_1703_ = v___x_1697_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_fst_1694_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1690_, v_a_1692_, v_b_1693_, v_fst_1694_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1705_);
v___x_1707_ = v___x_1697_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_snd_1695_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition___redArg(lean_object* v_cmp_1712_, lean_object* v_f_1713_, lean_object* v_t_1714_){
_start:
{
lean_object* v___f_1715_; lean_object* v___x_1716_; lean_object* v_p_1717_; lean_object* v_fst_1718_; lean_object* v_snd_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
v___f_1715_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1715_, 0, v_f_1713_);
lean_closure_set(v___f_1715_, 1, v_cmp_1712_);
v___x_1716_ = ((lean_object*)(l_Std_TreeMap_Raw_partition___redArg___closed__0));
v_p_1717_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1715_, v___x_1716_, v_t_1714_);
v_fst_1718_ = lean_ctor_get(v_p_1717_, 0);
v_snd_1719_ = lean_ctor_get(v_p_1717_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_p_1717_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v_p_1717_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_snd_1719_);
lean_inc(v_fst_1718_);
lean_dec(v_p_1717_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_fst_1718_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_snd_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition(lean_object* v_00_u03b1_1727_, lean_object* v_00_u03b2_1728_, lean_object* v_cmp_1729_, lean_object* v_f_1730_, lean_object* v_t_1731_){
_start:
{
lean_object* v___f_1732_; lean_object* v___x_1733_; lean_object* v_p_1734_; lean_object* v_fst_1735_; lean_object* v_snd_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
v___f_1732_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1732_, 0, v_f_1730_);
lean_closure_set(v___f_1732_, 1, v_cmp_1729_);
v___x_1733_ = ((lean_object*)(l_Std_TreeMap_Raw_partition___redArg___closed__0));
v_p_1734_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1732_, v___x_1733_, v_t_1731_);
v_fst_1735_ = lean_ctor_get(v_p_1734_, 0);
v_snd_1736_ = lean_ctor_get(v_p_1734_, 1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_p_1734_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v_p_1734_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_snd_1736_);
lean_inc(v_fst_1735_);
lean_dec(v_p_1734_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_fst_1735_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_snd_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___redArg___lam__0(lean_object* v_f_1744_, lean_object* v_x_1745_, lean_object* v_k_1746_, lean_object* v_v_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_apply_2(v_f_1744_, v_k_1746_, v_v_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___redArg(lean_object* v_inst_1749_, lean_object* v_f_1750_, lean_object* v_t_1751_){
_start:
{
lean_object* v___f_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___f_1752_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1752_, 0, v_f_1750_);
v___x_1753_ = lean_box(0);
v___x_1754_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1749_, v___f_1752_, v___x_1753_, v_t_1751_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM(lean_object* v_00_u03b1_1755_, lean_object* v_00_u03b2_1756_, lean_object* v_cmp_1757_, lean_object* v_m_1758_, lean_object* v_inst_1759_, lean_object* v_f_1760_, lean_object* v_t_1761_){
_start:
{
lean_object* v___f_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___f_1762_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1762_, 0, v_f_1760_);
v___x_1763_ = lean_box(0);
v___x_1764_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1759_, v___f_1762_, v___x_1763_, v_t_1761_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___boxed(lean_object* v_00_u03b1_1765_, lean_object* v_00_u03b2_1766_, lean_object* v_cmp_1767_, lean_object* v_m_1768_, lean_object* v_inst_1769_, lean_object* v_f_1770_, lean_object* v_t_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Std_TreeMap_Raw_forM(v_00_u03b1_1765_, v_00_u03b2_1766_, v_cmp_1767_, v_m_1768_, v_inst_1769_, v_f_1770_, v_t_1771_);
lean_dec_ref(v_cmp_1767_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg___lam__0(lean_object* v_f_1773_, lean_object* v_a_1774_, lean_object* v_b_1775_, lean_object* v_c_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_apply_3(v_f_1773_, v_a_1774_, v_b_1775_, v_c_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg___lam__1(lean_object* v_toPure_1778_, lean_object* v_____do__lift_1779_){
_start:
{
lean_object* v_a_1780_; lean_object* v___x_1781_; 
v_a_1780_ = lean_ctor_get(v_____do__lift_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v_____do__lift_1779_);
v___x_1781_ = lean_apply_2(v_toPure_1778_, lean_box(0), v_a_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg(lean_object* v_inst_1782_, lean_object* v_f_1783_, lean_object* v_init_1784_, lean_object* v_t_1785_){
_start:
{
lean_object* v_toApplicative_1786_; lean_object* v_toBind_1787_; lean_object* v_toPure_1788_; lean_object* v___f_1789_; lean_object* v___x_1790_; lean_object* v___f_1791_; lean_object* v___x_1792_; 
v_toApplicative_1786_ = lean_ctor_get(v_inst_1782_, 0);
v_toBind_1787_ = lean_ctor_get(v_inst_1782_, 1);
lean_inc(v_toBind_1787_);
v_toPure_1788_ = lean_ctor_get(v_toApplicative_1786_, 1);
lean_inc(v_toPure_1788_);
v___f_1789_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1789_, 0, v_f_1783_);
v___x_1790_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1782_, v___f_1789_, v_init_1784_, v_t_1785_);
v___f_1791_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1791_, 0, v_toPure_1788_);
v___x_1792_ = lean_apply_4(v_toBind_1787_, lean_box(0), lean_box(0), v___x_1790_, v___f_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn(lean_object* v_00_u03b1_1793_, lean_object* v_00_u03b2_1794_, lean_object* v_cmp_1795_, lean_object* v_00_u03b4_1796_, lean_object* v_m_1797_, lean_object* v_inst_1798_, lean_object* v_f_1799_, lean_object* v_init_1800_, lean_object* v_t_1801_){
_start:
{
lean_object* v_toApplicative_1802_; lean_object* v_toBind_1803_; lean_object* v_toPure_1804_; lean_object* v___f_1805_; lean_object* v___x_1806_; lean_object* v___f_1807_; lean_object* v___x_1808_; 
v_toApplicative_1802_ = lean_ctor_get(v_inst_1798_, 0);
v_toBind_1803_ = lean_ctor_get(v_inst_1798_, 1);
lean_inc(v_toBind_1803_);
v_toPure_1804_ = lean_ctor_get(v_toApplicative_1802_, 1);
lean_inc(v_toPure_1804_);
v___f_1805_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1805_, 0, v_f_1799_);
v___x_1806_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1798_, v___f_1805_, v_init_1800_, v_t_1801_);
v___f_1807_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1807_, 0, v_toPure_1804_);
v___x_1808_ = lean_apply_4(v_toBind_1803_, lean_box(0), lean_box(0), v___x_1806_, v___f_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___boxed(lean_object* v_00_u03b1_1809_, lean_object* v_00_u03b2_1810_, lean_object* v_cmp_1811_, lean_object* v_00_u03b4_1812_, lean_object* v_m_1813_, lean_object* v_inst_1814_, lean_object* v_f_1815_, lean_object* v_init_1816_, lean_object* v_t_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Std_TreeMap_Raw_forIn(v_00_u03b1_1809_, v_00_u03b2_1810_, v_cmp_1811_, v_00_u03b4_1812_, v_m_1813_, v_inst_1814_, v_f_1815_, v_init_1816_, v_t_1817_);
lean_dec_ref(v_cmp_1811_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1819_, lean_object* v_x_1820_, lean_object* v_k_1821_, lean_object* v_v_1822_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v_k_1821_);
lean_ctor_set(v___x_1823_, 1, v_v_1822_);
v___x_1824_ = lean_apply_1(v_f_1819_, v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_1825_, lean_object* v_t_1826_, lean_object* v_f_1827_){
_start:
{
lean_object* v___f_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___f_1828_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1828_, 0, v_f_1827_);
v___x_1829_ = lean_box(0);
v___x_1830_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1825_, v___f_1828_, v___x_1829_, v_t_1826_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg(lean_object* v_inst_1831_){
_start:
{
lean_object* v___f_1832_; 
v___f_1832_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1832_, 0, v_inst_1831_);
return v___f_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad(lean_object* v_00_u03b1_1833_, lean_object* v_00_u03b2_1834_, lean_object* v_cmp_1835_, lean_object* v_m_1836_, lean_object* v_inst_1837_){
_start:
{
lean_object* v___f_1838_; 
v___f_1838_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1838_, 0, v_inst_1837_);
return v___f_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_1839_, lean_object* v_00_u03b2_1840_, lean_object* v_cmp_1841_, lean_object* v_m_1842_, lean_object* v_inst_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Std_TreeMap_Raw_instForMProdOfMonad(v_00_u03b1_1839_, v_00_u03b2_1840_, v_cmp_1841_, v_m_1842_, v_inst_1843_);
lean_dec_ref(v_cmp_1841_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1845_, lean_object* v_a_1846_, lean_object* v_b_1847_, lean_object* v_c_1848_){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v_a_1846_);
lean_ctor_set(v___x_1849_, 1, v_b_1847_);
v___x_1850_ = lean_apply_2(v_f_1845_, v___x_1849_, v_c_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1851_, lean_object* v_00_u03b2_1852_, lean_object* v_t_1853_, lean_object* v_init_1854_, lean_object* v_f_1855_){
_start:
{
lean_object* v_toApplicative_1856_; lean_object* v_toBind_1857_; lean_object* v_toPure_1858_; lean_object* v___f_1859_; lean_object* v___x_1860_; lean_object* v___f_1861_; lean_object* v___x_1862_; 
v_toApplicative_1856_ = lean_ctor_get(v_inst_1851_, 0);
v_toBind_1857_ = lean_ctor_get(v_inst_1851_, 1);
lean_inc(v_toBind_1857_);
v_toPure_1858_ = lean_ctor_get(v_toApplicative_1856_, 1);
lean_inc(v_toPure_1858_);
v___f_1859_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1859_, 0, v_f_1855_);
v___x_1860_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1851_, v___f_1859_, v_init_1854_, v_t_1853_);
v___f_1861_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1861_, 0, v_toPure_1858_);
v___x_1862_ = lean_apply_4(v_toBind_1857_, lean_box(0), lean_box(0), v___x_1860_, v___f_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg(lean_object* v_inst_1863_){
_start:
{
lean_object* v___f_1864_; 
v___f_1864_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1864_, 0, v_inst_1863_);
return v___f_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad(lean_object* v_00_u03b1_1865_, lean_object* v_00_u03b2_1866_, lean_object* v_cmp_1867_, lean_object* v_m_1868_, lean_object* v_inst_1869_){
_start:
{
lean_object* v___f_1870_; 
v___f_1870_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1870_, 0, v_inst_1869_);
return v___f_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_cmp_1873_, lean_object* v_m_1874_, lean_object* v_inst_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Std_TreeMap_Raw_instForInProdOfMonad(v_00_u03b1_1871_, v_00_u03b2_1872_, v_cmp_1873_, v_m_1874_, v_inst_1875_);
lean_dec_ref(v_cmp_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___lam__0(lean_object* v_p_1877_, lean_object* v___x_1878_, lean_object* v___x_1879_, lean_object* v_a_1880_, lean_object* v_b_1881_, lean_object* v_acc_1882_){
_start:
{
lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1883_ = lean_apply_2(v_p_1877_, v_a_1880_, v_b_1881_);
v___x_1884_ = lean_unbox(v___x_1883_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1878_);
return v___x_1885_;
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec_ref(v___x_1878_);
v___x_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1883_);
v___x_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
lean_ctor_set(v___x_1887_, 1, v___x_1879_);
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
return v___x_1888_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1889_, lean_object* v___x_1890_, lean_object* v___x_1891_, lean_object* v_a_1892_, lean_object* v_b_1893_, lean_object* v_acc_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Std_TreeMap_Raw_any___redArg___lam__0(v_p_1889_, v___x_1890_, v___x_1891_, v_a_1892_, v_b_1893_, v_acc_1894_);
lean_dec_ref(v_acc_1894_);
return v_res_1895_;
}
}
uint8_t l_Std_TreeMap_Raw_any___redArg(lean_object* v_t_1899_, lean_object* v_p_1900_){
_start:
{
lean_object* v___y_1902_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___f_1910_; lean_object* v___x_1911_; lean_object* v_a_1912_; 
v___x_1907_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1908_ = lean_box(0);
v___x_1909_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1910_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1910_, 0, v_p_1900_);
lean_closure_set(v___f_1910_, 1, v___x_1909_);
lean_closure_set(v___f_1910_, 2, v___x_1908_);
v___x_1911_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1907_, v___f_1910_, v___x_1909_, v_t_1899_);
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___y_1902_ = v_a_1912_;
goto v___jp_1901_;
v___jp_1901_:
{
lean_object* v_fst_1903_; 
v_fst_1903_ = lean_ctor_get(v___y_1902_, 0);
lean_inc(v_fst_1903_);
lean_dec_ref(v___y_1902_);
if (lean_obj_tag(v_fst_1903_) == 0)
{
uint8_t v___x_1904_; 
v___x_1904_ = 0;
return v___x_1904_;
}
else
{
lean_object* v_val_1905_; uint8_t v___x_1906_; 
v_val_1905_ = lean_ctor_get(v_fst_1903_, 0);
lean_inc(v_val_1905_);
lean_dec_ref_known(v_fst_1903_, 1);
v___x_1906_ = lean_unbox(v_val_1905_);
lean_dec(v_val_1905_);
return v___x_1906_;
}
}
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1899_ = stack[0].m_obj;
lean_object* v_p_1900_ = stack[1].m_obj;
uint8_t v_res_1913_;
v_res_1913_ = l_Std_TreeMap_Raw_any___redArg(v_t_1899_, v_p_1900_);
stack->m_num = v_res_1913_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___boxed(lean_object* v_t_1914_, lean_object* v_p_1915_){
_start:
{
uint8_t v_res_1916_; lean_object* v_r_1917_; 
v_res_1916_ = l_Std_TreeMap_Raw_any___redArg(v_t_1914_, v_p_1915_);
v_r_1917_ = lean_box(v_res_1916_);
return v_r_1917_;
}
}
uint8_t l_Std_TreeMap_Raw_any(lean_object* v_00_u03b1_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_cmp_1920_, lean_object* v_t_1921_, lean_object* v_p_1922_){
_start:
{
lean_object* v___y_1924_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; lean_object* v_a_1934_; 
v___x_1929_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1930_ = lean_box(0);
v___x_1931_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1932_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1932_, 0, v_p_1922_);
lean_closure_set(v___f_1932_, 1, v___x_1931_);
lean_closure_set(v___f_1932_, 2, v___x_1930_);
v___x_1933_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1929_, v___f_1932_, v___x_1931_, v_t_1921_);
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___y_1924_ = v_a_1934_;
goto v___jp_1923_;
v___jp_1923_:
{
lean_object* v_fst_1925_; 
v_fst_1925_ = lean_ctor_get(v___y_1924_, 0);
lean_inc(v_fst_1925_);
lean_dec_ref(v___y_1924_);
if (lean_obj_tag(v_fst_1925_) == 0)
{
uint8_t v___x_1926_; 
v___x_1926_ = 0;
return v___x_1926_;
}
else
{
lean_object* v_val_1927_; uint8_t v___x_1928_; 
v_val_1927_ = lean_ctor_get(v_fst_1925_, 0);
lean_inc(v_val_1927_);
lean_dec_ref_known(v_fst_1925_, 1);
v___x_1928_ = lean_unbox(v_val_1927_);
lean_dec(v_val_1927_);
return v___x_1928_;
}
}
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1920_ = stack[2].m_obj;
lean_object* v_t_1921_ = stack[3].m_obj;
lean_object* v_p_1922_ = stack[4].m_obj;
uint8_t v_res_1935_;
v_res_1935_ = l_Std_TreeMap_Raw_any(lean_box(0), lean_box(0), v_cmp_1920_, v_t_1921_, v_p_1922_);
stack->m_num = v_res_1935_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___boxed(lean_object* v_00_u03b1_1936_, lean_object* v_00_u03b2_1937_, lean_object* v_cmp_1938_, lean_object* v_t_1939_, lean_object* v_p_1940_){
_start:
{
uint8_t v_res_1941_; lean_object* v_r_1942_; 
v_res_1941_ = l_Std_TreeMap_Raw_any(v_00_u03b1_1936_, v_00_u03b2_1937_, v_cmp_1938_, v_t_1939_, v_p_1940_);
lean_dec_ref(v_cmp_1938_);
v_r_1942_ = lean_box(v_res_1941_);
return v_r_1942_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___lam__0(lean_object* v_p_1943_, lean_object* v___x_1944_, lean_object* v___x_1945_, lean_object* v_a_1946_, lean_object* v_b_1947_, lean_object* v_acc_1948_){
_start:
{
lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = lean_apply_2(v_p_1943_, v_a_1946_, v_b_1947_);
v___x_1950_ = lean_unbox(v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec_ref(v___x_1945_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v___x_1944_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
else
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1945_);
return v___x_1954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1955_, lean_object* v___x_1956_, lean_object* v___x_1957_, lean_object* v_a_1958_, lean_object* v_b_1959_, lean_object* v_acc_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Std_TreeMap_Raw_all___redArg___lam__0(v_p_1955_, v___x_1956_, v___x_1957_, v_a_1958_, v_b_1959_, v_acc_1960_);
lean_dec_ref(v_acc_1960_);
return v_res_1961_;
}
}
uint8_t l_Std_TreeMap_Raw_all___redArg(lean_object* v_t_1962_, lean_object* v_p_1963_){
_start:
{
lean_object* v___y_1965_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___f_1973_; lean_object* v___x_1974_; lean_object* v_a_1975_; 
v___x_1970_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1971_ = lean_box(0);
v___x_1972_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1973_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1973_, 0, v_p_1963_);
lean_closure_set(v___f_1973_, 1, v___x_1971_);
lean_closure_set(v___f_1973_, 2, v___x_1972_);
v___x_1974_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1970_, v___f_1973_, v___x_1972_, v_t_1962_);
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___y_1965_ = v_a_1975_;
goto v___jp_1964_;
v___jp_1964_:
{
lean_object* v_fst_1966_; 
v_fst_1966_ = lean_ctor_get(v___y_1965_, 0);
lean_inc(v_fst_1966_);
lean_dec_ref(v___y_1965_);
if (lean_obj_tag(v_fst_1966_) == 0)
{
uint8_t v___x_1967_; 
v___x_1967_ = 1;
return v___x_1967_;
}
else
{
lean_object* v_val_1968_; uint8_t v___x_1969_; 
v_val_1968_ = lean_ctor_get(v_fst_1966_, 0);
lean_inc(v_val_1968_);
lean_dec_ref_known(v_fst_1966_, 1);
v___x_1969_ = lean_unbox(v_val_1968_);
lean_dec(v_val_1968_);
return v___x_1969_;
}
}
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1962_ = stack[0].m_obj;
lean_object* v_p_1963_ = stack[1].m_obj;
uint8_t v_res_1976_;
v_res_1976_ = l_Std_TreeMap_Raw_all___redArg(v_t_1962_, v_p_1963_);
stack->m_num = v_res_1976_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___boxed(lean_object* v_t_1977_, lean_object* v_p_1978_){
_start:
{
uint8_t v_res_1979_; lean_object* v_r_1980_; 
v_res_1979_ = l_Std_TreeMap_Raw_all___redArg(v_t_1977_, v_p_1978_);
v_r_1980_ = lean_box(v_res_1979_);
return v_r_1980_;
}
}
uint8_t l_Std_TreeMap_Raw_all(lean_object* v_00_u03b1_1981_, lean_object* v_00_u03b2_1982_, lean_object* v_cmp_1983_, lean_object* v_t_1984_, lean_object* v_p_1985_){
_start:
{
lean_object* v___y_1987_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___f_1995_; lean_object* v___x_1996_; lean_object* v_a_1997_; 
v___x_1992_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1993_ = lean_box(0);
v___x_1994_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1995_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1995_, 0, v_p_1985_);
lean_closure_set(v___f_1995_, 1, v___x_1993_);
lean_closure_set(v___f_1995_, 2, v___x_1994_);
v___x_1996_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1992_, v___f_1995_, v___x_1994_, v_t_1984_);
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___y_1987_ = v_a_1997_;
goto v___jp_1986_;
v___jp_1986_:
{
lean_object* v_fst_1988_; 
v_fst_1988_ = lean_ctor_get(v___y_1987_, 0);
lean_inc(v_fst_1988_);
lean_dec_ref(v___y_1987_);
if (lean_obj_tag(v_fst_1988_) == 0)
{
uint8_t v___x_1989_; 
v___x_1989_ = 1;
return v___x_1989_;
}
else
{
lean_object* v_val_1990_; uint8_t v___x_1991_; 
v_val_1990_ = lean_ctor_get(v_fst_1988_, 0);
lean_inc(v_val_1990_);
lean_dec_ref_known(v_fst_1988_, 1);
v___x_1991_ = lean_unbox(v_val_1990_);
lean_dec(v_val_1990_);
return v___x_1991_;
}
}
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1983_ = stack[2].m_obj;
lean_object* v_t_1984_ = stack[3].m_obj;
lean_object* v_p_1985_ = stack[4].m_obj;
uint8_t v_res_1998_;
v_res_1998_ = l_Std_TreeMap_Raw_all(lean_box(0), lean_box(0), v_cmp_1983_, v_t_1984_, v_p_1985_);
stack->m_num = v_res_1998_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___boxed(lean_object* v_00_u03b1_1999_, lean_object* v_00_u03b2_2000_, lean_object* v_cmp_2001_, lean_object* v_t_2002_, lean_object* v_p_2003_){
_start:
{
uint8_t v_res_2004_; lean_object* v_r_2005_; 
v_res_2004_ = l_Std_TreeMap_Raw_all(v_00_u03b1_1999_, v_00_u03b2_2000_, v_cmp_2001_, v_t_2002_, v_p_2003_);
lean_dec_ref(v_cmp_2001_);
v_r_2005_ = lean_box(v_res_2004_);
return v_r_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg___lam__0(lean_object* v_x1_2006_, lean_object* v_x2_2007_, lean_object* v_x3_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2009_, 0, v_x1_2006_);
lean_ctor_set(v___x_2009_, 1, v_x3_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_x1_2010_, lean_object* v_x2_2011_, lean_object* v_x3_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Std_TreeMap_Raw_keys___redArg___lam__0(v_x1_2010_, v_x2_2011_, v_x3_2012_);
lean_dec(v_x2_2011_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg(lean_object* v_t_2015_){
_start:
{
lean_object* v___f_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___f_2016_ = ((lean_object*)(l_Std_TreeMap_Raw_keys___redArg___closed__0));
v___x_2017_ = lean_box(0);
v___x_2018_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2019_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2018_, v___f_2016_, v___x_2017_, v_t_2015_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys(lean_object* v_00_u03b1_2020_, lean_object* v_00_u03b2_2021_, lean_object* v_cmp_2022_, lean_object* v_t_2023_){
_start:
{
lean_object* v___f_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___f_2024_ = ((lean_object*)(l_Std_TreeMap_Raw_keys___redArg___closed__0));
v___x_2025_ = lean_box(0);
v___x_2026_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2027_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2026_, v___f_2024_, v___x_2025_, v_t_2023_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___boxed(lean_object* v_00_u03b1_2028_, lean_object* v_00_u03b2_2029_, lean_object* v_cmp_2030_, lean_object* v_t_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Std_TreeMap_Raw_keys(v_00_u03b1_2028_, v_00_u03b2_2029_, v_cmp_2030_, v_t_2031_);
lean_dec_ref(v_cmp_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg___lam__0(lean_object* v_l_2033_, lean_object* v_k_2034_, lean_object* v_x_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_array_push(v_l_2033_, v_k_2034_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_l_2037_, lean_object* v_k_2038_, lean_object* v_x_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Std_TreeMap_Raw_keysArray___redArg___lam__0(v_l_2037_, v_k_2038_, v_x_2039_);
lean_dec(v_x_2039_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg(lean_object* v_t_2042_){
_start:
{
lean_object* v___f_2043_; lean_object* v___y_2045_; 
v___f_2043_ = ((lean_object*)(l_Std_TreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2042_) == 0)
{
lean_object* v_size_2048_; 
v_size_2048_ = lean_ctor_get(v_t_2042_, 0);
lean_inc(v_size_2048_);
v___y_2045_ = v_size_2048_;
goto v___jp_2044_;
}
else
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_unsigned_to_nat(0u);
v___y_2045_ = v___x_2049_;
goto v___jp_2044_;
}
v___jp_2044_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_mk_empty_array_with_capacity(v___y_2045_);
lean_dec(v___y_2045_);
v___x_2047_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2043_, v___x_2046_, v_t_2042_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray(lean_object* v_00_u03b1_2050_, lean_object* v_00_u03b2_2051_, lean_object* v_cmp_2052_, lean_object* v_t_2053_){
_start:
{
lean_object* v___f_2054_; lean_object* v___y_2056_; 
v___f_2054_ = ((lean_object*)(l_Std_TreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2053_) == 0)
{
lean_object* v_size_2059_; 
v_size_2059_ = lean_ctor_get(v_t_2053_, 0);
lean_inc(v_size_2059_);
v___y_2056_ = v_size_2059_;
goto v___jp_2055_;
}
else
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_unsigned_to_nat(0u);
v___y_2056_ = v___x_2060_;
goto v___jp_2055_;
}
v___jp_2055_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_mk_empty_array_with_capacity(v___y_2056_);
lean_dec(v___y_2056_);
v___x_2058_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2054_, v___x_2057_, v_t_2053_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___boxed(lean_object* v_00_u03b1_2061_, lean_object* v_00_u03b2_2062_, lean_object* v_cmp_2063_, lean_object* v_t_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Std_TreeMap_Raw_keysArray(v_00_u03b1_2061_, v_00_u03b2_2062_, v_cmp_2063_, v_t_2064_);
lean_dec_ref(v_cmp_2063_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg___lam__0(lean_object* v_x1_2066_, lean_object* v_x2_2067_, lean_object* v_x3_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_x2_2067_);
lean_ctor_set(v___x_2069_, 1, v_x3_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg___lam__0___boxed(lean_object* v_x1_2070_, lean_object* v_x2_2071_, lean_object* v_x3_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Std_TreeMap_Raw_values___redArg___lam__0(v_x1_2070_, v_x2_2071_, v_x3_2072_);
lean_dec(v_x1_2070_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg(lean_object* v_t_2075_){
_start:
{
lean_object* v___f_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___f_2076_ = ((lean_object*)(l_Std_TreeMap_Raw_values___redArg___closed__0));
v___x_2077_ = lean_box(0);
v___x_2078_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2079_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2078_, v___f_2076_, v___x_2077_, v_t_2075_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values(lean_object* v_00_u03b1_2080_, lean_object* v_00_u03b2_2081_, lean_object* v_cmp_2082_, lean_object* v_t_2083_){
_start:
{
lean_object* v___f_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___f_2084_ = ((lean_object*)(l_Std_TreeMap_Raw_values___redArg___closed__0));
v___x_2085_ = lean_box(0);
v___x_2086_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2087_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2086_, v___f_2084_, v___x_2085_, v_t_2083_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___boxed(lean_object* v_00_u03b1_2088_, lean_object* v_00_u03b2_2089_, lean_object* v_cmp_2090_, lean_object* v_t_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Std_TreeMap_Raw_values(v_00_u03b1_2088_, v_00_u03b2_2089_, v_cmp_2090_, v_t_2091_);
lean_dec_ref(v_cmp_2090_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg___lam__0(lean_object* v_l_2093_, lean_object* v_x_2094_, lean_object* v_v_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = lean_array_push(v_l_2093_, v_v_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2097_, lean_object* v_x_2098_, lean_object* v_v_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Std_TreeMap_Raw_valuesArray___redArg___lam__0(v_l_2097_, v_x_2098_, v_v_2099_);
lean_dec(v_x_2098_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg(lean_object* v_t_2102_){
_start:
{
lean_object* v___f_2103_; lean_object* v___y_2105_; 
v___f_2103_ = ((lean_object*)(l_Std_TreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2102_) == 0)
{
lean_object* v_size_2108_; 
v_size_2108_ = lean_ctor_get(v_t_2102_, 0);
lean_inc(v_size_2108_);
v___y_2105_ = v_size_2108_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_unsigned_to_nat(0u);
v___y_2105_ = v___x_2109_;
goto v___jp_2104_;
}
v___jp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_mk_empty_array_with_capacity(v___y_2105_);
lean_dec(v___y_2105_);
v___x_2107_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2103_, v___x_2106_, v_t_2102_);
return v___x_2107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray(lean_object* v_00_u03b1_2110_, lean_object* v_00_u03b2_2111_, lean_object* v_cmp_2112_, lean_object* v_t_2113_){
_start:
{
lean_object* v___f_2114_; lean_object* v___y_2116_; 
v___f_2114_ = ((lean_object*)(l_Std_TreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2113_) == 0)
{
lean_object* v_size_2119_; 
v_size_2119_ = lean_ctor_get(v_t_2113_, 0);
lean_inc(v_size_2119_);
v___y_2116_ = v_size_2119_;
goto v___jp_2115_;
}
else
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_unsigned_to_nat(0u);
v___y_2116_ = v___x_2120_;
goto v___jp_2115_;
}
v___jp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_mk_empty_array_with_capacity(v___y_2116_);
lean_dec(v___y_2116_);
v___x_2118_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2114_, v___x_2117_, v_t_2113_);
return v___x_2118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___boxed(lean_object* v_00_u03b1_2121_, lean_object* v_00_u03b2_2122_, lean_object* v_cmp_2123_, lean_object* v_t_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Std_TreeMap_Raw_valuesArray(v_00_u03b1_2121_, v_00_u03b2_2122_, v_cmp_2123_, v_t_2124_);
lean_dec_ref(v_cmp_2123_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___redArg___lam__0(lean_object* v_x1_2126_, lean_object* v_x2_2127_, lean_object* v_x3_2128_){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v_x1_2126_);
lean_ctor_set(v___x_2129_, 1, v_x2_2127_);
v___x_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v_x3_2128_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___redArg(lean_object* v_t_2132_){
_start:
{
lean_object* v___f_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___f_2133_ = ((lean_object*)(l_Std_TreeMap_Raw_toList___redArg___closed__0));
v___x_2134_ = lean_box(0);
v___x_2135_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2136_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2135_, v___f_2133_, v___x_2134_, v_t_2132_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList(lean_object* v_00_u03b1_2137_, lean_object* v_00_u03b2_2138_, lean_object* v_cmp_2139_, lean_object* v_t_2140_){
_start:
{
lean_object* v___f_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___f_2141_ = ((lean_object*)(l_Std_TreeMap_Raw_toList___redArg___closed__0));
v___x_2142_ = lean_box(0);
v___x_2143_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2144_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2143_, v___f_2141_, v___x_2142_, v_t_2140_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___boxed(lean_object* v_00_u03b1_2145_, lean_object* v_00_u03b2_2146_, lean_object* v_cmp_2147_, lean_object* v_t_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Std_TreeMap_Raw_toList(v_00_u03b1_2145_, v_00_u03b2_2146_, v_cmp_2147_, v_t_2148_);
lean_dec_ref(v_cmp_2147_);
return v_res_2149_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__25, &l_Std_TreeMap_Raw___auto__1___closed__25_once, _init_l_Std_TreeMap_Raw___auto__1___closed__25);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___redArg___lam__0(lean_object* v_cmp_2151_, lean_object* v_a_2152_, lean_object* v_x_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_fst_2155_; lean_object* v_snd_2156_; lean_object* v_r_2157_; lean_object* v___x_2158_; 
v_fst_2155_ = lean_ctor_get(v_a_2152_, 0);
lean_inc(v_fst_2155_);
v_snd_2156_ = lean_ctor_get(v_a_2152_, 1);
lean_inc(v_snd_2156_);
lean_dec_ref(v_a_2152_);
v_r_2157_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2151_, v_fst_2155_, v_snd_2156_, v___y_2154_);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_r_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___redArg(lean_object* v_l_2159_, lean_object* v_cmp_2160_){
_start:
{
lean_object* v___f_2161_; lean_object* v___x_2162_; lean_object* v_r_2163_; lean_object* v___x_2164_; 
v___f_2161_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2161_, 0, v_cmp_2160_);
v___x_2162_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2163_ = lean_box(1);
v___x_2164_ = l_List_forIn_x27_loop___redArg(v___x_2162_, v___f_2161_, v_l_2159_, v_r_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___redArg___boxed(lean_object* v_l_2165_, lean_object* v_cmp_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Std_TreeMap_Raw_ofList___redArg(v_l_2165_, v_cmp_2166_);
lean_dec(v_l_2165_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList(lean_object* v_00_u03b1_2168_, lean_object* v_00_u03b2_2169_, lean_object* v_l_2170_, lean_object* v_cmp_2171_){
_start:
{
lean_object* v___f_2172_; lean_object* v___x_2173_; lean_object* v_r_2174_; lean_object* v___x_2175_; 
v___f_2172_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2172_, 0, v_cmp_2171_);
v___x_2173_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2174_ = lean_box(1);
v___x_2175_ = l_List_forIn_x27_loop___redArg(v___x_2173_, v___f_2172_, v_l_2170_, v_r_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___boxed(lean_object* v_00_u03b1_2176_, lean_object* v_00_u03b2_2177_, lean_object* v_l_2178_, lean_object* v_cmp_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Std_TreeMap_Raw_ofList(v_00_u03b1_2176_, v_00_u03b2_2177_, v_l_2178_, v_cmp_2179_);
lean_dec(v_l_2178_);
return v_res_2180_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__25, &l_Std_TreeMap_Raw___auto__1___closed__25_once, _init_l_Std_TreeMap_Raw___auto__1___closed__25);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg___lam__0(lean_object* v_cmp_2182_, lean_object* v_a_2183_, lean_object* v_x_2184_, lean_object* v___y_2185_){
_start:
{
uint8_t v___x_2186_; 
lean_inc(v___y_2185_);
lean_inc(v_a_2183_);
lean_inc_ref(v_cmp_2182_);
v___x_2186_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2182_, v_a_2183_, v___y_2185_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = lean_box(0);
v___x_2188_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2182_, v_a_2183_, v___x_2187_, v___y_2185_);
v___x_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
return v___x_2189_;
}
else
{
lean_object* v___x_2190_; 
lean_dec(v_a_2183_);
lean_dec_ref(v_cmp_2182_);
v___x_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___y_2185_);
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg(lean_object* v_l_2191_, lean_object* v_cmp_2192_){
_start:
{
lean_object* v___f_2193_; lean_object* v___x_2194_; lean_object* v_r_2195_; lean_object* v___x_2196_; 
v___f_2193_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2193_, 0, v_cmp_2192_);
v___x_2194_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2195_ = lean_box(1);
v___x_2196_ = l_List_forIn_x27_loop___redArg(v___x_2194_, v___f_2193_, v_l_2191_, v_r_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg___boxed(lean_object* v_l_2197_, lean_object* v_cmp_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Std_TreeMap_Raw_unitOfList___redArg(v_l_2197_, v_cmp_2198_);
lean_dec(v_l_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList(lean_object* v_00_u03b1_2200_, lean_object* v_l_2201_, lean_object* v_cmp_2202_){
_start:
{
lean_object* v___f_2203_; lean_object* v___x_2204_; lean_object* v_r_2205_; lean_object* v___x_2206_; 
v___f_2203_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2203_, 0, v_cmp_2202_);
v___x_2204_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2205_ = lean_box(1);
v___x_2206_ = l_List_forIn_x27_loop___redArg(v___x_2204_, v___f_2203_, v_l_2201_, v_r_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___boxed(lean_object* v_00_u03b1_2207_, lean_object* v_l_2208_, lean_object* v_cmp_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Std_TreeMap_Raw_unitOfList(v_00_u03b1_2207_, v_l_2208_, v_cmp_2209_);
lean_dec(v_l_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___redArg___lam__0(lean_object* v_l_2211_, lean_object* v_k_2212_, lean_object* v_v_2213_){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2214_, 0, v_k_2212_);
lean_ctor_set(v___x_2214_, 1, v_v_2213_);
v___x_2215_ = lean_array_push(v_l_2211_, v___x_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___redArg(lean_object* v_t_2217_){
_start:
{
lean_object* v___f_2218_; lean_object* v___y_2220_; 
v___f_2218_ = ((lean_object*)(l_Std_TreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2217_) == 0)
{
lean_object* v_size_2223_; 
v_size_2223_ = lean_ctor_get(v_t_2217_, 0);
lean_inc(v_size_2223_);
v___y_2220_ = v_size_2223_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_unsigned_to_nat(0u);
v___y_2220_ = v___x_2224_;
goto v___jp_2219_;
}
v___jp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_mk_empty_array_with_capacity(v___y_2220_);
lean_dec(v___y_2220_);
v___x_2222_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2218_, v___x_2221_, v_t_2217_);
return v___x_2222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray(lean_object* v_00_u03b1_2225_, lean_object* v_00_u03b2_2226_, lean_object* v_cmp_2227_, lean_object* v_t_2228_){
_start:
{
lean_object* v___f_2229_; lean_object* v___y_2231_; 
v___f_2229_ = ((lean_object*)(l_Std_TreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2228_) == 0)
{
lean_object* v_size_2234_; 
v_size_2234_ = lean_ctor_get(v_t_2228_, 0);
lean_inc(v_size_2234_);
v___y_2231_ = v_size_2234_;
goto v___jp_2230_;
}
else
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_unsigned_to_nat(0u);
v___y_2231_ = v___x_2235_;
goto v___jp_2230_;
}
v___jp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = lean_mk_empty_array_with_capacity(v___y_2231_);
lean_dec(v___y_2231_);
v___x_2233_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2229_, v___x_2232_, v_t_2228_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___boxed(lean_object* v_00_u03b1_2236_, lean_object* v_00_u03b2_2237_, lean_object* v_cmp_2238_, lean_object* v_t_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Std_TreeMap_Raw_toArray(v_00_u03b1_2236_, v_00_u03b2_2237_, v_cmp_2238_, v_t_2239_);
lean_dec_ref(v_cmp_2238_);
return v_res_2240_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__25, &l_Std_TreeMap_Raw___auto__1___closed__25_once, _init_l_Std_TreeMap_Raw___auto__1___closed__25);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofArray___redArg(lean_object* v_a_2242_, lean_object* v_cmp_2243_){
_start:
{
lean_object* v___f_2244_; lean_object* v___x_2245_; lean_object* v_r_2246_; size_t v_sz_2247_; size_t v___x_2248_; lean_object* v___x_2249_; 
v___f_2244_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2244_, 0, v_cmp_2243_);
v___x_2245_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2246_ = lean_box(1);
v_sz_2247_ = lean_array_size(v_a_2242_);
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2245_, v_a_2242_, v___f_2244_, v_sz_2247_, v___x_2248_, v_r_2246_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofArray(lean_object* v_00_u03b1_2250_, lean_object* v_00_u03b2_2251_, lean_object* v_a_2252_, lean_object* v_cmp_2253_){
_start:
{
lean_object* v___f_2254_; lean_object* v___x_2255_; lean_object* v_r_2256_; size_t v_sz_2257_; size_t v___x_2258_; lean_object* v___x_2259_; 
v___f_2254_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2254_, 0, v_cmp_2253_);
v___x_2255_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2256_ = lean_box(1);
v_sz_2257_ = lean_array_size(v_a_2252_);
v___x_2258_ = ((size_t)0ULL);
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2255_, v_a_2252_, v___f_2254_, v_sz_2257_, v___x_2258_, v_r_2256_);
return v___x_2259_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__25, &l_Std_TreeMap_Raw___auto__1___closed__25_once, _init_l_Std_TreeMap_Raw___auto__1___closed__25);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfArray___redArg(lean_object* v_a_2261_, lean_object* v_cmp_2262_){
_start:
{
lean_object* v___f_2263_; lean_object* v___x_2264_; lean_object* v_r_2265_; size_t v_sz_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v___f_2263_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2263_, 0, v_cmp_2262_);
v___x_2264_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2265_ = lean_box(1);
v_sz_2266_ = lean_array_size(v_a_2261_);
v___x_2267_ = ((size_t)0ULL);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2264_, v_a_2261_, v___f_2263_, v_sz_2266_, v___x_2267_, v_r_2265_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfArray(lean_object* v_00_u03b1_2269_, lean_object* v_a_2270_, lean_object* v_cmp_2271_){
_start:
{
lean_object* v___f_2272_; lean_object* v___x_2273_; lean_object* v_r_2274_; size_t v_sz_2275_; size_t v___x_2276_; lean_object* v___x_2277_; 
v___f_2272_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2272_, 0, v_cmp_2271_);
v___x_2273_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2274_ = lean_box(1);
v_sz_2275_ = lean_array_size(v_a_2270_);
v___x_2276_ = ((size_t)0ULL);
v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2273_, v_a_2270_, v___f_2272_, v_sz_2275_, v___x_2276_, v_r_2274_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_modify___redArg(lean_object* v_cmp_2278_, lean_object* v_t_2279_, lean_object* v_a_2280_, lean_object* v_f_2281_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2278_, v_a_2280_, v_f_2281_, v_t_2279_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_modify(lean_object* v_00_u03b1_2283_, lean_object* v_00_u03b2_2284_, lean_object* v_cmp_2285_, lean_object* v_t_2286_, lean_object* v_a_2287_, lean_object* v_f_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2285_, v_a_2287_, v_f_2288_, v_t_2286_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_alter___redArg(lean_object* v_cmp_2290_, lean_object* v_t_2291_, lean_object* v_a_2292_, lean_object* v_f_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2290_, v_a_2292_, v_f_2293_, v_t_2291_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_alter(lean_object* v_00_u03b1_2295_, lean_object* v_00_u03b2_2296_, lean_object* v_cmp_2297_, lean_object* v_t_2298_, lean_object* v_a_2299_, lean_object* v_f_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2297_, v_a_2299_, v_f_2300_, v_t_2298_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2302_, lean_object* v_mergeFn_2303_, lean_object* v_a_2304_, lean_object* v_x_2305_){
_start:
{
if (lean_obj_tag(v_x_2305_) == 0)
{
lean_object* v___x_2306_; 
lean_dec(v_a_2304_);
lean_dec(v_mergeFn_2303_);
v___x_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2306_, 0, v_b_u2082_2302_);
return v___x_2306_;
}
else
{
lean_object* v_val_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2315_; 
v_val_2307_ = lean_ctor_get(v_x_2305_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_x_2305_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2309_ = v_x_2305_;
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_val_2307_);
lean_dec(v_x_2305_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_apply_3(v_mergeFn_2303_, v_a_2304_, v_val_2307_, v_b_u2082_2302_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2311_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2316_, lean_object* v_cmp_2317_, lean_object* v_t_2318_, lean_object* v_a_2319_, lean_object* v_b_u2082_2320_){
_start:
{
lean_object* v___f_2321_; lean_object* v___x_2322_; 
lean_inc(v_a_2319_);
v___f_2321_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2321_, 0, v_b_u2082_2320_);
lean_closure_set(v___f_2321_, 1, v_mergeFn_2316_);
lean_closure_set(v___f_2321_, 2, v_a_2319_);
v___x_2322_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2317_, v_a_2319_, v___f_2321_, v_t_2318_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg(lean_object* v_cmp_2323_, lean_object* v_mergeFn_2324_, lean_object* v_t_u2081_2325_, lean_object* v_t_u2082_2326_){
_start:
{
lean_object* v___f_2327_; lean_object* v___x_2328_; 
v___f_2327_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2327_, 0, v_mergeFn_2324_);
lean_closure_set(v___f_2327_, 1, v_cmp_2323_);
v___x_2328_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2327_, v_t_u2081_2325_, v_t_u2082_2326_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith(lean_object* v_00_u03b1_2329_, lean_object* v_00_u03b2_2330_, lean_object* v_cmp_2331_, lean_object* v_mergeFn_2332_, lean_object* v_t_u2081_2333_, lean_object* v_t_u2082_2334_){
_start:
{
lean_object* v___f_2335_; lean_object* v___x_2336_; 
v___f_2335_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2335_, 0, v_mergeFn_2332_);
lean_closure_set(v___f_2335_, 1, v_cmp_2331_);
v___x_2336_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2335_, v_t_u2081_2333_, v_t_u2082_2334_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_2337_, lean_object* v_x_2338_, lean_object* v_____s_2339_){
_start:
{
lean_object* v_fst_2340_; lean_object* v_snd_2341_; lean_object* v_r_2342_; lean_object* v___x_2343_; 
v_fst_2340_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_fst_2340_);
v_snd_2341_ = lean_ctor_get(v_x_2338_, 1);
lean_inc(v_snd_2341_);
lean_dec_ref(v_x_2338_);
v_r_2342_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2337_, v_fst_2340_, v_snd_2341_, v_____s_2339_);
v___x_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2343_, 0, v_r_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany___redArg(lean_object* v_cmp_2344_, lean_object* v_inst_2345_, lean_object* v_t_2346_, lean_object* v_l_2347_){
_start:
{
lean_object* v___f_2348_; lean_object* v___x_2349_; 
v___f_2348_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2348_, 0, v_cmp_2344_);
v___x_2349_ = lean_apply_4(v_inst_2345_, lean_box(0), v_l_2347_, v_t_2346_, v___f_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany(lean_object* v_00_u03b1_2350_, lean_object* v_00_u03b2_2351_, lean_object* v_cmp_2352_, lean_object* v_00_u03c1_2353_, lean_object* v_inst_2354_, lean_object* v_t_2355_, lean_object* v_l_2356_){
_start:
{
lean_object* v___f_2357_; lean_object* v___x_2358_; 
v___f_2357_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2357_, 0, v_cmp_2352_);
v___x_2358_ = lean_apply_4(v_inst_2354_, lean_box(0), v_l_2356_, v_t_2355_, v___f_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_union___redArg(lean_object* v_cmp_2359_, lean_object* v_t_u2081_2360_, lean_object* v_t_u2082_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_2359_, v_t_u2081_2360_, v_t_u2082_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_union(lean_object* v_00_u03b1_2363_, lean_object* v_00_u03b2_2364_, lean_object* v_cmp_2365_, lean_object* v_t_u2081_2366_, lean_object* v_t_u2082_2367_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_2365_, v_t_u2081_2366_, v_t_u2082_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instUnion___redArg(lean_object* v_cmp_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_2370_, 0, lean_box(0));
lean_closure_set(v___x_2370_, 1, lean_box(0));
lean_closure_set(v___x_2370_, 2, v_cmp_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instUnion(lean_object* v_00_u03b1_2371_, lean_object* v_00_u03b2_2372_, lean_object* v_cmp_2373_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_2374_, 0, lean_box(0));
lean_closure_set(v___x_2374_, 1, lean_box(0));
lean_closure_set(v___x_2374_, 2, v_cmp_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_inter___redArg(lean_object* v_cmp_2375_, lean_object* v_t_u2081_2376_, lean_object* v_t_u2082_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_2375_, v_t_u2081_2376_, v_t_u2082_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_inter(lean_object* v_00_u03b1_2379_, lean_object* v_00_u03b2_2380_, lean_object* v_cmp_2381_, lean_object* v_t_u2081_2382_, lean_object* v_t_u2082_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_2381_, v_t_u2081_2382_, v_t_u2082_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInter___redArg(lean_object* v_cmp_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_2386_, 0, lean_box(0));
lean_closure_set(v___x_2386_, 1, lean_box(0));
lean_closure_set(v___x_2386_, 2, v_cmp_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInter(lean_object* v_00_u03b1_2387_, lean_object* v_00_u03b2_2388_, lean_object* v_cmp_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_2390_, 0, lean_box(0));
lean_closure_set(v___x_2390_, 1, lean_box(0));
lean_closure_set(v___x_2390_, 2, v_cmp_2389_);
return v___x_2390_;
}
}
uint8_t l_Std_TreeMap_Raw_beq___redArg(lean_object* v_cmp_2391_, lean_object* v_inst_2392_, lean_object* v_t_u2081_2393_, lean_object* v_t_u2082_2394_){
_start:
{
uint8_t v___x_2395_; 
v___x_2395_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2391_, v_inst_2392_, v_t_u2081_2393_, v_t_u2082_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2391_ = stack[0].m_obj;
lean_object* v_inst_2392_ = stack[1].m_obj;
lean_object* v_t_u2081_2393_ = stack[2].m_obj;
lean_object* v_t_u2082_2394_ = stack[3].m_obj;
uint8_t v_res_2396_;
v_res_2396_ = l_Std_TreeMap_Raw_beq___redArg(v_cmp_2391_, v_inst_2392_, v_t_u2081_2393_, v_t_u2082_2394_);
stack->m_num = v_res_2396_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___redArg___boxed(lean_object* v_cmp_2397_, lean_object* v_inst_2398_, lean_object* v_t_u2081_2399_, lean_object* v_t_u2082_2400_){
_start:
{
uint8_t v_res_2401_; lean_object* v_r_2402_; 
v_res_2401_ = l_Std_TreeMap_Raw_beq___redArg(v_cmp_2397_, v_inst_2398_, v_t_u2081_2399_, v_t_u2082_2400_);
v_r_2402_ = lean_box(v_res_2401_);
return v_r_2402_;
}
}
uint8_t l_Std_TreeMap_Raw_beq(lean_object* v_00_u03b1_2403_, lean_object* v_00_u03b2_2404_, lean_object* v_cmp_2405_, lean_object* v_inst_2406_, lean_object* v_t_u2081_2407_, lean_object* v_t_u2082_2408_){
_start:
{
uint8_t v___x_2409_; 
v___x_2409_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2405_, v_inst_2406_, v_t_u2081_2407_, v_t_u2082_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2405_ = stack[2].m_obj;
lean_object* v_inst_2406_ = stack[3].m_obj;
lean_object* v_t_u2081_2407_ = stack[4].m_obj;
lean_object* v_t_u2082_2408_ = stack[5].m_obj;
uint8_t v_res_2410_;
v_res_2410_ = l_Std_TreeMap_Raw_beq(lean_box(0), lean_box(0), v_cmp_2405_, v_inst_2406_, v_t_u2081_2407_, v_t_u2082_2408_);
stack->m_num = v_res_2410_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___boxed(lean_object* v_00_u03b1_2411_, lean_object* v_00_u03b2_2412_, lean_object* v_cmp_2413_, lean_object* v_inst_2414_, lean_object* v_t_u2081_2415_, lean_object* v_t_u2082_2416_){
_start:
{
uint8_t v_res_2417_; lean_object* v_r_2418_; 
v_res_2417_ = l_Std_TreeMap_Raw_beq(v_00_u03b1_2411_, v_00_u03b2_2412_, v_cmp_2413_, v_inst_2414_, v_t_u2081_2415_, v_t_u2082_2416_);
v_r_2418_ = lean_box(v_res_2417_);
return v_r_2418_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instBEq___redArg(lean_object* v_cmp_2419_, lean_object* v_inst_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_beq___boxed), 6, 4);
lean_closure_set(v___x_2421_, 0, lean_box(0));
lean_closure_set(v___x_2421_, 1, lean_box(0));
lean_closure_set(v___x_2421_, 2, v_cmp_2419_);
lean_closure_set(v___x_2421_, 3, v_inst_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instBEq(lean_object* v_00_u03b1_2422_, lean_object* v_00_u03b2_2423_, lean_object* v_cmp_2424_, lean_object* v_inst_2425_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_beq___boxed), 6, 4);
lean_closure_set(v___x_2426_, 0, lean_box(0));
lean_closure_set(v___x_2426_, 1, lean_box(0));
lean_closure_set(v___x_2426_, 2, v_cmp_2424_);
lean_closure_set(v___x_2426_, 3, v_inst_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_diff___redArg(lean_object* v_cmp_2427_, lean_object* v_t_u2081_2428_, lean_object* v_t_u2082_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_2427_, v_t_u2081_2428_, v_t_u2082_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_diff(lean_object* v_00_u03b1_2431_, lean_object* v_00_u03b2_2432_, lean_object* v_cmp_2433_, lean_object* v_t_u2081_2434_, lean_object* v_t_u2082_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_2433_, v_t_u2081_2434_, v_t_u2082_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSDiff___redArg(lean_object* v_cmp_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_2438_, 0, lean_box(0));
lean_closure_set(v___x_2438_, 1, lean_box(0));
lean_closure_set(v___x_2438_, 2, v_cmp_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSDiff(lean_object* v_00_u03b1_2439_, lean_object* v_00_u03b2_2440_, lean_object* v_cmp_2441_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_2442_, 0, lean_box(0));
lean_closure_set(v___x_2442_, 1, lean_box(0));
lean_closure_set(v___x_2442_, 2, v_cmp_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_2443_, lean_object* v_a_2444_, lean_object* v_____s_2445_){
_start:
{
uint8_t v___x_2446_; 
lean_inc(v_____s_2445_);
lean_inc(v_a_2444_);
lean_inc_ref(v_cmp_2443_);
v___x_2446_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2443_, v_a_2444_, v_____s_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = lean_box(0);
v___x_2448_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2443_, v_a_2444_, v___x_2447_, v_____s_2445_);
v___x_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
return v___x_2449_;
}
else
{
lean_object* v___x_2450_; 
lean_dec(v_a_2444_);
lean_dec_ref(v_cmp_2443_);
v___x_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2450_, 0, v_____s_2445_);
return v___x_2450_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg(lean_object* v_cmp_2451_, lean_object* v_inst_2452_, lean_object* v_t_2453_, lean_object* v_l_2454_){
_start:
{
lean_object* v___f_2455_; lean_object* v___x_2456_; 
v___f_2455_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2455_, 0, v_cmp_2451_);
v___x_2456_ = lean_apply_4(v_inst_2452_, lean_box(0), v_l_2454_, v_t_2453_, v___f_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit(lean_object* v_00_u03b1_2457_, lean_object* v_cmp_2458_, lean_object* v_00_u03c1_2459_, lean_object* v_inst_2460_, lean_object* v_t_2461_, lean_object* v_l_2462_){
_start:
{
lean_object* v___f_2463_; lean_object* v___x_2464_; 
v___f_2463_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2463_, 0, v_cmp_2458_);
v___x_2464_ = lean_apply_4(v_inst_2460_, lean_box(0), v_l_2462_, v_t_2461_, v___f_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_2465_, lean_object* v_a_2466_, lean_object* v_____s_2467_){
_start:
{
lean_object* v_r_2468_; lean_object* v___x_2469_; 
v_r_2468_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_2465_, v_a_2466_, v_____s_2467_);
v___x_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_r_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany___redArg(lean_object* v_cmp_2470_, lean_object* v_inst_2471_, lean_object* v_t_2472_, lean_object* v_l_2473_){
_start:
{
lean_object* v___f_2474_; lean_object* v___x_2475_; 
v___f_2474_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2474_, 0, v_cmp_2470_);
v___x_2475_ = lean_apply_4(v_inst_2471_, lean_box(0), v_l_2473_, v_t_2472_, v___f_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany(lean_object* v_00_u03b1_2476_, lean_object* v_00_u03b2_2477_, lean_object* v_cmp_2478_, lean_object* v_00_u03c1_2479_, lean_object* v_inst_2480_, lean_object* v_t_2481_, lean_object* v_l_2482_){
_start:
{
lean_object* v___f_2483_; lean_object* v___x_2484_; 
v___f_2483_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2483_, 0, v_cmp_2478_);
v___x_2484_ = lean_apply_4(v_inst_2480_, lean_box(0), v_l_2482_, v_t_2481_, v___f_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg___lam__1(lean_object* v___f_2488_, lean_object* v___x_2489_, lean_object* v_m_2490_, lean_object* v_prec_2491_){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2492_ = ((lean_object*)(l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__1));
v___x_2493_ = lean_box(0);
v___x_2494_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2495_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2494_, v___f_2488_, v___x_2493_, v_m_2490_);
v___x_2496_ = l_List_repr___redArg(v___x_2489_, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2492_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l_Repr_addAppParen(v___x_2497_, v_prec_2491_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_2499_, lean_object* v___x_2500_, lean_object* v_m_2501_, lean_object* v_prec_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Std_TreeMap_Raw_instRepr___redArg___lam__1(v___f_2499_, v___x_2500_, v_m_2501_, v_prec_2502_);
lean_dec(v_prec_2502_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg(lean_object* v_inst_2504_, lean_object* v_inst_2505_){
_start:
{
lean_object* v___f_2506_; lean_object* v___f_2507_; lean_object* v___x_2508_; lean_object* v___f_2509_; 
v___f_2506_ = ((lean_object*)(l_Std_TreeMap_Raw_toList___redArg___closed__0));
v___f_2507_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2507_, 0, v_inst_2505_);
v___x_2508_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2508_, 0, lean_box(0));
lean_closure_set(v___x_2508_, 1, lean_box(0));
lean_closure_set(v___x_2508_, 2, v_inst_2504_);
lean_closure_set(v___x_2508_, 3, v___f_2507_);
v___f_2509_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2509_, 0, v___f_2506_);
lean_closure_set(v___f_2509_, 1, v___x_2508_);
return v___f_2509_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr(lean_object* v_00_u03b1_2510_, lean_object* v_00_u03b2_2511_, lean_object* v_cmp_2512_, lean_object* v_inst_2513_, lean_object* v_inst_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Std_TreeMap_Raw_instRepr___redArg(v_inst_2513_, v_inst_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___boxed(lean_object* v_00_u03b1_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_cmp_2518_, lean_object* v_inst_2519_, lean_object* v_inst_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Std_TreeMap_Raw_instRepr(v_00_u03b1_2516_, v_00_u03b2_2517_, v_cmp_2518_, v_inst_2519_, v_inst_2520_);
lean_dec_ref(v_cmp_2518_);
return v_res_2521_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_TreeMap_Raw___auto__1 = _init_l_Std_TreeMap_Raw___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw___auto__1);
l_Std_TreeMap_Raw_ofList___auto__1 = _init_l_Std_TreeMap_Raw_ofList___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_ofList___auto__1);
l_Std_TreeMap_Raw_unitOfList___auto__1 = _init_l_Std_TreeMap_Raw_unitOfList___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_unitOfList___auto__1);
l_Std_TreeMap_Raw_ofArray___auto__1 = _init_l_Std_TreeMap_Raw_ofArray___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_ofArray___auto__1);
l_Std_TreeMap_Raw_unitOfArray___auto__1 = _init_l_Std_TreeMap_Raw_unitOfArray___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_unitOfArray___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeMap_Raw_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
