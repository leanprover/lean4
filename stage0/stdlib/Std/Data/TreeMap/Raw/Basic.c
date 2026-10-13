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
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner___redArg___boxed(lean_object* v___dummy_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_TreeMap_Raw_instCoeWFWFInner___redArg();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_cmp_79_, lean_object* v_t_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(0);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner___boxed(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_cmp_84_, lean_object* v_t_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_TreeMap_Raw_instCoeWFWFInner(v_00_u03b1_82_, v_00_u03b2_83_, v_cmp_84_, v_t_85_);
lean_dec(v_t_85_);
lean_dec_ref(v_cmp_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty___redArg(){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(1);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty___redArg___boxed(lean_object* v___dummy_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_TreeMap_Raw_empty___redArg();
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_cmp_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(1);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty___boxed(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_cmp_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_TreeMap_Raw_empty(v_00_u03b1_95_, v_00_u03b2_96_, v_cmp_97_);
lean_dec_ref(v_cmp_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(1);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_TreeMap_Raw_instEmptyCollection___redArg();
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_103_, lean_object* v_00_u03b2_104_, lean_object* v_cmp_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(1);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection___boxed(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_cmp_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_TreeMap_Raw_instEmptyCollection(v_00_u03b1_107_, v_00_u03b2_108_, v_cmp_109_);
lean_dec_ref(v_cmp_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(1);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_TreeMap_Raw_instInhabited___redArg();
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_cmp_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_box(1);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited___boxed(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_cmp_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_TreeMap_Raw_instInhabited(v_00_u03b1_119_, v_00_u03b2_120_, v_cmp_121_);
lean_dec_ref(v_cmp_121_);
return v_res_122_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3));
v___x_163_ = l_String_toRawSubstring_x27(v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1(lean_object* v_x_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l_Std_TreeMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_182_);
v___x_186_ = l_Lean_Syntax_isOfKind(v_x_182_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_x_182_);
v___x_187_ = lean_box(1);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v_a_184_);
return v___x_188_;
}
else
{
lean_object* v_quotContext_189_; lean_object* v_currMacroScope_190_; lean_object* v_ref_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_quotContext_189_ = lean_ctor_get(v_a_183_, 1);
v_currMacroScope_190_ = lean_ctor_get(v_a_183_, 2);
v_ref_191_ = lean_ctor_get(v_a_183_, 5);
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = l_Lean_Syntax_getArg(v_x_182_, v___x_192_);
v___x_194_ = lean_unsigned_to_nat(2u);
v___x_195_ = l_Lean_Syntax_getArg(v_x_182_, v___x_194_);
lean_dec(v_x_182_);
v___x_196_ = 0;
v___x_197_ = l_Lean_SourceInfo_fromRef(v_ref_191_, v___x_196_);
v___x_198_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2));
v___x_199_ = lean_obj_once(&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4, &l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4_once, _init_l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4);
v___x_200_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_190_);
lean_inc(v_quotContext_189_);
v___x_201_ = l_Lean_addMacroScope(v_quotContext_189_, v___x_200_, v_currMacroScope_190_);
v___x_202_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__10));
lean_inc_n(v___x_197_, 2);
v___x_203_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_203_, 0, v___x_197_);
lean_ctor_set(v___x_203_, 1, v___x_199_);
lean_ctor_set(v___x_203_, 2, v___x_201_);
lean_ctor_set(v___x_203_, 3, v___x_202_);
v___x_204_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__9));
v___x_205_ = l_Lean_Syntax_node2(v___x_197_, v___x_204_, v___x_193_, v___x_195_);
v___x_206_ = l_Lean_Syntax_node2(v___x_197_, v___x_198_, v___x_203_, v___x_205_);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v_a_184_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___boxed(lean_object* v_x_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1(v_x_208_, v_a_209_, v_a_210_);
lean_dec_ref(v_a_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1(lean_object* v_x_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2));
lean_inc(v_x_215_);
v___x_219_ = l_Lean_Syntax_isOfKind(v_x_215_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v_x_215_);
v___x_220_ = lean_box(0);
v___x_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v_a_217_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = l_Lean_Syntax_getArg(v_x_215_, v___x_222_);
v___x_224_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_223_);
v___x_225_ = l_Lean_Syntax_isOfKind(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec(v___x_223_);
lean_dec(v_x_215_);
v___x_226_ = lean_box(0);
v___x_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_a_217_);
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = l_Lean_Syntax_getArg(v_x_215_, v___x_228_);
lean_dec(v_x_215_);
v___x_230_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_229_);
v___x_231_ = l_Lean_Syntax_matchesNull(v___x_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v___x_229_);
lean_dec(v___x_223_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v_a_217_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_ref_236_; uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_234_ = l_Lean_Syntax_getArg(v___x_229_, v___x_222_);
v___x_235_ = l_Lean_Syntax_getArg(v___x_229_, v___x_228_);
lean_dec(v___x_229_);
v_ref_236_ = l_Lean_replaceRef(v___x_223_, v_a_216_);
lean_dec(v___x_223_);
v___x_237_ = 0;
v___x_238_ = l_Lean_SourceInfo_fromRef(v_ref_236_, v___x_237_);
lean_dec(v_ref_236_);
v___x_239_ = ((lean_object*)(l_Std_TreeMap_Raw_term___x7em___00__closed__4));
v___x_240_ = ((lean_object*)(l_Std_TreeMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_238_);
v___x_241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_238_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = l_Lean_Syntax_node3(v___x_238_, v___x_239_, v___x_234_, v___x_241_, v___x_235_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v_a_217_);
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___boxed(lean_object* v_x_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1(v_x_244_, v_a_245_, v_a_246_);
lean_dec(v_a_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insert___redArg(lean_object* v_cmp_248_, lean_object* v_l_249_, lean_object* v_a_250_, lean_object* v_b_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_248_, v_a_250_, v_b_251_, v_l_249_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insert(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_cmp_255_, lean_object* v_l_256_, lean_object* v_a_257_, lean_object* v_b_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_255_, v_a_257_, v_b_258_, v_l_256_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0(lean_object* v_cmp_260_, lean_object* v_e_261_){
_start:
{
lean_object* v_fst_262_; lean_object* v_snd_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_fst_262_ = lean_ctor_get(v_e_261_, 0);
lean_inc(v_fst_262_);
v_snd_263_ = lean_ctor_get(v_e_261_, 1);
lean_inc(v_snd_263_);
lean_dec_ref(v_e_261_);
v___x_264_ = lean_box(1);
v___x_265_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_260_, v_fst_262_, v_snd_263_, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd___redArg(lean_object* v_cmp_266_){
_start:
{
lean_object* v___f_267_; 
v___f_267_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0), 2, 1);
lean_closure_set(v___f_267_, 0, v_cmp_266_);
return v___f_267_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd(lean_object* v_00_u03b1_268_, lean_object* v_00_u03b2_269_, lean_object* v_cmp_270_){
_start:
{
lean_object* v___f_271_; 
v___f_271_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0), 2, 1);
lean_closure_set(v___f_271_, 0, v_cmp_270_);
return v___f_271_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0(lean_object* v_cmp_272_, lean_object* v_e_273_, lean_object* v_s_274_){
_start:
{
lean_object* v_fst_275_; lean_object* v_snd_276_; lean_object* v___x_277_; 
v_fst_275_ = lean_ctor_get(v_e_273_, 0);
lean_inc(v_fst_275_);
v_snd_276_ = lean_ctor_get(v_e_273_, 1);
lean_inc(v_snd_276_);
lean_dec_ref(v_e_273_);
v___x_277_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_272_, v_fst_275_, v_snd_276_, v_s_274_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd___redArg(lean_object* v_cmp_278_){
_start:
{
lean_object* v___f_279_; 
v___f_279_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_279_, 0, v_cmp_278_);
return v___f_279_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_cmp_282_){
_start:
{
lean_object* v___f_283_; 
v___f_283_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_283_, 0, v_cmp_282_);
return v___f_283_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertIfNew___redArg(lean_object* v_cmp_284_, lean_object* v_t_285_, lean_object* v_a_286_, lean_object* v_b_287_){
_start:
{
uint8_t v___x_288_; 
lean_inc(v_t_285_);
lean_inc(v_a_286_);
lean_inc_ref(v_cmp_284_);
v___x_288_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_284_, v_a_286_, v_t_285_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_284_, v_a_286_, v_b_287_, v_t_285_);
return v___x_289_;
}
else
{
lean_dec(v_b_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_cmp_284_);
return v_t_285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertIfNew(lean_object* v_00_u03b1_290_, lean_object* v_00_u03b2_291_, lean_object* v_cmp_292_, lean_object* v_t_293_, lean_object* v_a_294_, lean_object* v_b_295_){
_start:
{
uint8_t v___x_296_; 
lean_inc(v_t_293_);
lean_inc(v_a_294_);
lean_inc_ref(v_cmp_292_);
v___x_296_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_292_, v_a_294_, v_t_293_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_292_, v_a_294_, v_b_295_, v_t_293_);
return v___x_297_;
}
else
{
lean_dec(v_b_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_cmp_292_);
return v_t_293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsert___redArg(lean_object* v_cmp_298_, lean_object* v_t_299_, lean_object* v_a_300_, lean_object* v_b_301_){
_start:
{
lean_object* v_sz_302_; lean_object* v_m_303_; lean_object* v___y_305_; 
v_sz_302_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_299_);
v_m_303_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_298_, v_a_300_, v_b_301_, v_t_299_);
if (lean_obj_tag(v_m_303_) == 0)
{
lean_object* v_size_309_; 
v_size_309_ = lean_ctor_get(v_m_303_, 0);
lean_inc(v_size_309_);
v___y_305_ = v_size_309_;
goto v___jp_304_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_unsigned_to_nat(0u);
v___y_305_ = v___x_310_;
goto v___jp_304_;
}
v___jp_304_:
{
uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_nat_dec_eq(v_sz_302_, v___y_305_);
lean_dec(v___y_305_);
lean_dec(v_sz_302_);
v___x_307_ = lean_box(v___x_306_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_m_303_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsert(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_cmp_313_, lean_object* v_t_314_, lean_object* v_a_315_, lean_object* v_b_316_){
_start:
{
lean_object* v_sz_317_; lean_object* v_m_318_; lean_object* v___y_320_; 
v_sz_317_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_314_);
v_m_318_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_313_, v_a_315_, v_b_316_, v_t_314_);
if (lean_obj_tag(v_m_318_) == 0)
{
lean_object* v_size_324_; 
v_size_324_ = lean_ctor_get(v_m_318_, 0);
lean_inc(v_size_324_);
v___y_320_ = v_size_324_;
goto v___jp_319_;
}
else
{
lean_object* v___x_325_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v___y_320_ = v___x_325_;
goto v___jp_319_;
}
v___jp_319_:
{
uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_nat_dec_eq(v_sz_317_, v___y_320_);
lean_dec(v___y_320_);
lean_dec(v_sz_317_);
v___x_322_ = lean_box(v___x_321_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_m_318_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_cmp_326_, lean_object* v_t_327_, lean_object* v_a_328_, lean_object* v_b_329_){
_start:
{
uint8_t v___x_330_; 
lean_inc(v_t_327_);
lean_inc(v_a_328_);
lean_inc_ref(v_cmp_326_);
v___x_330_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_326_, v_a_328_, v_t_327_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_326_, v_a_328_, v_b_329_, v_t_327_);
v___x_332_ = lean_box(v___x_330_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec(v_b_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_cmp_326_);
v___x_334_ = lean_box(v___x_330_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_t_327_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_336_, lean_object* v_00_u03b2_337_, lean_object* v_cmp_338_, lean_object* v_t_339_, lean_object* v_a_340_, lean_object* v_b_341_){
_start:
{
uint8_t v___x_342_; 
lean_inc(v_t_339_);
lean_inc(v_a_340_);
lean_inc_ref(v_cmp_338_);
v___x_342_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_338_, v_a_340_, v_t_339_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_338_, v_a_340_, v_b_341_, v_t_339_);
v___x_344_ = lean_box(v___x_342_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
return v___x_345_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec(v_b_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_cmp_338_);
v___x_346_ = lean_box(v___x_342_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v_t_339_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_348_, lean_object* v_t_349_, lean_object* v_a_350_, lean_object* v_b_351_){
_start:
{
lean_object* v___x_352_; 
lean_inc(v_a_350_);
lean_inc(v_t_349_);
lean_inc_ref(v_cmp_348_);
v___x_352_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_348_, v_t_349_, v_a_350_);
if (lean_obj_tag(v___x_352_) == 0)
{
uint8_t v___x_353_; 
lean_inc(v_t_349_);
lean_inc(v_a_350_);
lean_inc_ref(v_cmp_348_);
v___x_353_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_348_, v_a_350_, v_t_349_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_348_, v_a_350_, v_b_351_, v_t_349_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_352_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; 
lean_dec(v_b_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_cmp_348_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_352_);
lean_ctor_set(v___x_356_, 1, v_t_349_);
return v___x_356_;
}
}
else
{
lean_object* v___x_357_; 
lean_dec(v_b_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_cmp_348_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_352_);
lean_ctor_set(v___x_357_, 1, v_t_349_);
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_358_, lean_object* v_00_u03b2_359_, lean_object* v_cmp_360_, lean_object* v_t_361_, lean_object* v_a_362_, lean_object* v_b_363_){
_start:
{
lean_object* v___x_364_; 
lean_inc(v_a_362_);
lean_inc(v_t_361_);
lean_inc_ref(v_cmp_360_);
v___x_364_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_360_, v_t_361_, v_a_362_);
if (lean_obj_tag(v___x_364_) == 0)
{
uint8_t v___x_365_; 
lean_inc(v_t_361_);
lean_inc(v_a_362_);
lean_inc_ref(v_cmp_360_);
v___x_365_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_360_, v_a_362_, v_t_361_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_360_, v_a_362_, v_b_363_, v_t_361_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_364_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v___x_368_; 
lean_dec(v_b_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_cmp_360_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_364_);
lean_ctor_set(v___x_368_, 1, v_t_361_);
return v___x_368_;
}
}
else
{
lean_object* v___x_369_; 
lean_dec(v_b_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_cmp_360_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_364_);
lean_ctor_set(v___x_369_, 1, v_t_361_);
return v___x_369_;
}
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_contains___redArg(lean_object* v_cmp_370_, lean_object* v_l_371_, lean_object* v_a_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_370_, v_a_372_, v_l_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_contains___redArg___boxed(lean_object* v_cmp_374_, lean_object* v_l_375_, lean_object* v_a_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Std_TreeMap_Raw_contains___redArg(v_cmp_374_, v_l_375_, v_a_376_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_contains(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_cmp_381_, lean_object* v_l_382_, lean_object* v_a_383_){
_start:
{
uint8_t v___x_384_; 
v___x_384_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_381_, v_a_383_, v_l_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_contains___boxed(lean_object* v_00_u03b1_385_, lean_object* v_00_u03b2_386_, lean_object* v_cmp_387_, lean_object* v_l_388_, lean_object* v_a_389_){
_start:
{
uint8_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = l_Std_TreeMap_Raw_contains(v_00_u03b1_385_, v_00_u03b2_386_, v_cmp_387_, v_l_388_, v_a_389_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership___redArg(){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_box(0);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership___redArg___boxed(lean_object* v___dummy_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_TreeMap_Raw_instMembership___redArg();
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership(lean_object* v_00_u03b1_396_, lean_object* v_00_u03b2_397_, lean_object* v_cmp_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership___boxed(lean_object* v_00_u03b1_400_, lean_object* v_00_u03b2_401_, lean_object* v_cmp_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_TreeMap_Raw_instMembership(v_00_u03b1_400_, v_00_u03b2_401_, v_cmp_402_);
lean_dec_ref(v_cmp_402_);
return v_res_403_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_instDecidableMem___redArg(lean_object* v_cmp_404_, lean_object* v_t_405_, lean_object* v_a_406_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_404_, v_a_406_, v_t_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_408_, lean_object* v_t_409_, lean_object* v_a_410_){
_start:
{
uint8_t v_res_411_; lean_object* v_r_412_; 
v_res_411_ = l_Std_TreeMap_Raw_instDecidableMem___redArg(v_cmp_408_, v_t_409_, v_a_410_);
v_r_412_ = lean_box(v_res_411_);
return v_r_412_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_instDecidableMem(lean_object* v_00_u03b1_413_, lean_object* v_00_u03b2_414_, lean_object* v_cmp_415_, lean_object* v_t_416_, lean_object* v_a_417_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_415_, v_a_417_, v_t_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_419_, lean_object* v_00_u03b2_420_, lean_object* v_cmp_421_, lean_object* v_t_422_, lean_object* v_a_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Std_TreeMap_Raw_instDecidableMem(v_00_u03b1_419_, v_00_u03b2_420_, v_cmp_421_, v_t_422_, v_a_423_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___redArg(lean_object* v_t_426_){
_start:
{
if (lean_obj_tag(v_t_426_) == 0)
{
lean_object* v_size_427_; 
v_size_427_ = lean_ctor_get(v_t_426_, 0);
lean_inc(v_size_427_);
return v_size_427_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = lean_unsigned_to_nat(0u);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___redArg___boxed(lean_object* v_t_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_TreeMap_Raw_size___redArg(v_t_429_);
lean_dec(v_t_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size(lean_object* v_00_u03b1_431_, lean_object* v_00_u03b2_432_, lean_object* v_cmp_433_, lean_object* v_t_434_){
_start:
{
if (lean_obj_tag(v_t_434_) == 0)
{
lean_object* v_size_435_; 
v_size_435_ = lean_ctor_get(v_t_434_, 0);
lean_inc(v_size_435_);
return v_size_435_;
}
else
{
lean_object* v___x_436_; 
v___x_436_ = lean_unsigned_to_nat(0u);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___boxed(lean_object* v_00_u03b1_437_, lean_object* v_00_u03b2_438_, lean_object* v_cmp_439_, lean_object* v_t_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_TreeMap_Raw_size(v_00_u03b1_437_, v_00_u03b2_438_, v_cmp_439_, v_t_440_);
lean_dec(v_t_440_);
lean_dec_ref(v_cmp_439_);
return v_res_441_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_isEmpty___redArg(lean_object* v_t_442_){
_start:
{
if (lean_obj_tag(v_t_442_) == 0)
{
uint8_t v___x_443_; 
v___x_443_ = 0;
return v___x_443_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = 1;
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_isEmpty___redArg___boxed(lean_object* v_t_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Std_TreeMap_Raw_isEmpty___redArg(v_t_445_);
lean_dec(v_t_445_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_isEmpty(lean_object* v_00_u03b1_448_, lean_object* v_00_u03b2_449_, lean_object* v_cmp_450_, lean_object* v_t_451_){
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
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_454_, lean_object* v_00_u03b2_455_, lean_object* v_cmp_456_, lean_object* v_t_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Std_TreeMap_Raw_isEmpty(v_00_u03b1_454_, v_00_u03b2_455_, v_cmp_456_, v_t_457_);
lean_dec(v_t_457_);
lean_dec_ref(v_cmp_456_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_erase___redArg(lean_object* v_cmp_460_, lean_object* v_t_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_460_, v_a_462_, v_t_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_erase(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_cmp_466_, lean_object* v_t_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_466_, v_a_468_, v_t_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x3f___redArg(lean_object* v_cmp_470_, lean_object* v_t_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_470_, v_t_471_, v_a_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x3f(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_cmp_476_, lean_object* v_t_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_476_, v_t_477_, v_a_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get___redArg(lean_object* v_cmp_480_, lean_object* v_t_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_480_, v_t_481_, v_a_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_cmp_486_, lean_object* v_t_487_, lean_object* v_a_488_, lean_object* v_h_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_486_, v_t_487_, v_a_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21___redArg(lean_object* v_cmp_491_, lean_object* v_inst_492_, lean_object* v_t_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_491_, v_inst_492_, v_t_493_, v_a_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21___redArg___boxed(lean_object* v_cmp_496_, lean_object* v_inst_497_, lean_object* v_t_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_TreeMap_Raw_get_x21___redArg(v_cmp_496_, v_inst_497_, v_t_498_, v_a_499_);
lean_dec(v_inst_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21(lean_object* v_00_u03b1_501_, lean_object* v_00_u03b2_502_, lean_object* v_cmp_503_, lean_object* v_inst_504_, lean_object* v_t_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_503_, v_inst_504_, v_t_505_, v_a_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_, lean_object* v_cmp_510_, lean_object* v_inst_511_, lean_object* v_t_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_TreeMap_Raw_get_x21(v_00_u03b1_508_, v_00_u03b2_509_, v_cmp_510_, v_inst_511_, v_t_512_, v_a_513_);
lean_dec(v_inst_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___redArg(lean_object* v_cmp_515_, lean_object* v_t_516_, lean_object* v_a_517_, lean_object* v_fallback_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_515_, v_t_516_, v_a_517_, v_fallback_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___redArg___boxed(lean_object* v_cmp_520_, lean_object* v_t_521_, lean_object* v_a_522_, lean_object* v_fallback_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_TreeMap_Raw_getD___redArg(v_cmp_520_, v_t_521_, v_a_522_, v_fallback_523_);
lean_dec(v_fallback_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD(lean_object* v_00_u03b1_525_, lean_object* v_00_u03b2_526_, lean_object* v_cmp_527_, lean_object* v_t_528_, lean_object* v_a_529_, lean_object* v_fallback_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_527_, v_t_528_, v_a_529_, v_fallback_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___boxed(lean_object* v_00_u03b1_532_, lean_object* v_00_u03b2_533_, lean_object* v_cmp_534_, lean_object* v_t_535_, lean_object* v_a_536_, lean_object* v_fallback_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_TreeMap_Raw_getD(v_00_u03b1_532_, v_00_u03b2_533_, v_cmp_534_, v_t_535_, v_a_536_, v_fallback_537_);
lean_dec(v_fallback_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object* v_cmp_539_, lean_object* v_m_540_, lean_object* v_a_541_, lean_object* v_h_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_539_, v_m_540_, v_a_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object* v_cmp_544_, lean_object* v_m_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_544_, v_m_545_, v_a_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object* v_cmp_548_, lean_object* v_inst_549_, lean_object* v_m_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_548_, v_inst_549_, v_m_550_, v_a_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_cmp_553_, lean_object* v_inst_554_, lean_object* v_m_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2(v_cmp_553_, v_inst_554_, v_m_555_, v_a_556_);
lean_dec(v_inst_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg(lean_object* v_cmp_558_){
_start:
{
lean_object* v___f_559_; lean_object* v___f_560_; lean_object* v___f_561_; lean_object* v___x_562_; 
lean_inc_ref_n(v_cmp_558_, 2);
v___f_559_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__0), 4, 1);
lean_closure_set(v___f_559_, 0, v_cmp_558_);
v___f_560_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__1), 3, 1);
lean_closure_set(v___f_560_, 0, v_cmp_558_);
v___f_561_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_561_, 0, v_cmp_558_);
v___x_562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_562_, 0, v___f_559_);
lean_ctor_set(v___x_562_, 1, v___f_560_);
lean_ctor_set(v___x_562_, 2, v___f_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem(lean_object* v_00_u03b1_563_, lean_object* v_00_u03b2_564_, lean_object* v_cmp_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg(v_cmp_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x3f___redArg(lean_object* v_cmp_567_, lean_object* v_t_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_567_, v_t_568_, v_a_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x3f(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_cmp_573_, lean_object* v_t_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_573_, v_t_574_, v_a_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey___redArg(lean_object* v_cmp_577_, lean_object* v_t_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_577_, v_t_578_, v_a_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey(lean_object* v_00_u03b1_581_, lean_object* v_00_u03b2_582_, lean_object* v_cmp_583_, lean_object* v_t_584_, lean_object* v_a_585_, lean_object* v_h_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_583_, v_t_584_, v_a_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21___redArg(lean_object* v_cmp_588_, lean_object* v_inst_589_, lean_object* v_t_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_588_, v_t_590_, v_a_591_, v_inst_589_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21___redArg___boxed(lean_object* v_cmp_593_, lean_object* v_inst_594_, lean_object* v_t_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_TreeMap_Raw_getKey_x21___redArg(v_cmp_593_, v_inst_594_, v_t_595_, v_a_596_);
lean_dec(v_inst_594_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21(lean_object* v_00_u03b1_598_, lean_object* v_00_u03b2_599_, lean_object* v_cmp_600_, lean_object* v_inst_601_, lean_object* v_t_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_600_, v_t_602_, v_a_603_, v_inst_601_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_605_, lean_object* v_00_u03b2_606_, lean_object* v_cmp_607_, lean_object* v_inst_608_, lean_object* v_t_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_TreeMap_Raw_getKey_x21(v_00_u03b1_605_, v_00_u03b2_606_, v_cmp_607_, v_inst_608_, v_t_609_, v_a_610_);
lean_dec(v_inst_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___redArg(lean_object* v_cmp_612_, lean_object* v_t_613_, lean_object* v_a_614_, lean_object* v_fallback_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_612_, v_t_613_, v_a_614_, v_fallback_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___redArg___boxed(lean_object* v_cmp_617_, lean_object* v_t_618_, lean_object* v_a_619_, lean_object* v_fallback_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_TreeMap_Raw_getKeyD___redArg(v_cmp_617_, v_t_618_, v_a_619_, v_fallback_620_);
lean_dec(v_fallback_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD(lean_object* v_00_u03b1_622_, lean_object* v_00_u03b2_623_, lean_object* v_cmp_624_, lean_object* v_t_625_, lean_object* v_a_626_, lean_object* v_fallback_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_624_, v_t_625_, v_a_626_, v_fallback_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_cmp_631_, lean_object* v_t_632_, lean_object* v_a_633_, lean_object* v_fallback_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_TreeMap_Raw_getKeyD(v_00_u03b1_629_, v_00_u03b2_630_, v_cmp_631_, v_t_632_, v_a_633_, v_fallback_634_);
lean_dec(v_fallback_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___redArg(lean_object* v_t_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___redArg___boxed(lean_object* v_t_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_TreeMap_Raw_minEntry_x3f___redArg(v_t_638_);
lean_dec(v_t_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f(lean_object* v_00_u03b1_640_, lean_object* v_00_u03b2_641_, lean_object* v_cmp_642_, lean_object* v_t_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___boxed(lean_object* v_00_u03b1_645_, lean_object* v_00_u03b2_646_, lean_object* v_cmp_647_, lean_object* v_t_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Std_TreeMap_Raw_minEntry_x3f(v_00_u03b1_645_, v_00_u03b2_646_, v_cmp_647_, v_t_648_);
lean_dec(v_t_648_);
lean_dec_ref(v_cmp_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___redArg(lean_object* v_inst_650_, lean_object* v_t_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_650_, v_t_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___redArg___boxed(lean_object* v_inst_653_, lean_object* v_t_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std_TreeMap_Raw_minEntry_x21___redArg(v_inst_653_, v_t_654_);
lean_dec(v_t_654_);
lean_dec_ref(v_inst_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21(lean_object* v_00_u03b1_656_, lean_object* v_00_u03b2_657_, lean_object* v_cmp_658_, lean_object* v_inst_659_, lean_object* v_t_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_659_, v_t_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___boxed(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_cmp_664_, lean_object* v_inst_665_, lean_object* v_t_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Std_TreeMap_Raw_minEntry_x21(v_00_u03b1_662_, v_00_u03b2_663_, v_cmp_664_, v_inst_665_, v_t_666_);
lean_dec(v_t_666_);
lean_dec_ref(v_inst_665_);
lean_dec_ref(v_cmp_664_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___redArg(lean_object* v_t_668_, lean_object* v_fallback_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_668_, v_fallback_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___redArg___boxed(lean_object* v_t_671_, lean_object* v_fallback_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_TreeMap_Raw_minEntryD___redArg(v_t_671_, v_fallback_672_);
lean_dec_ref(v_fallback_672_);
lean_dec(v_t_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_cmp_676_, lean_object* v_t_677_, lean_object* v_fallback_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_677_, v_fallback_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___boxed(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_cmp_682_, lean_object* v_t_683_, lean_object* v_fallback_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Std_TreeMap_Raw_minEntryD(v_00_u03b1_680_, v_00_u03b2_681_, v_cmp_682_, v_t_683_, v_fallback_684_);
lean_dec_ref(v_fallback_684_);
lean_dec(v_t_683_);
lean_dec_ref(v_cmp_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___redArg(lean_object* v_t_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___redArg___boxed(lean_object* v_t_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_TreeMap_Raw_maxEntry_x3f___redArg(v_t_688_);
lean_dec(v_t_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f(lean_object* v_00_u03b1_690_, lean_object* v_00_u03b2_691_, lean_object* v_cmp_692_, lean_object* v_t_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___boxed(lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_cmp_697_, lean_object* v_t_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_TreeMap_Raw_maxEntry_x3f(v_00_u03b1_695_, v_00_u03b2_696_, v_cmp_697_, v_t_698_);
lean_dec(v_t_698_);
lean_dec_ref(v_cmp_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___redArg(lean_object* v_inst_700_, lean_object* v_t_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_700_, v_t_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___redArg___boxed(lean_object* v_inst_703_, lean_object* v_t_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Std_TreeMap_Raw_maxEntry_x21___redArg(v_inst_703_, v_t_704_);
lean_dec(v_t_704_);
lean_dec_ref(v_inst_703_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21(lean_object* v_00_u03b1_706_, lean_object* v_00_u03b2_707_, lean_object* v_cmp_708_, lean_object* v_inst_709_, lean_object* v_t_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_709_, v_t_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___boxed(lean_object* v_00_u03b1_712_, lean_object* v_00_u03b2_713_, lean_object* v_cmp_714_, lean_object* v_inst_715_, lean_object* v_t_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_TreeMap_Raw_maxEntry_x21(v_00_u03b1_712_, v_00_u03b2_713_, v_cmp_714_, v_inst_715_, v_t_716_);
lean_dec(v_t_716_);
lean_dec_ref(v_inst_715_);
lean_dec_ref(v_cmp_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___redArg(lean_object* v_t_718_, lean_object* v_fallback_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_718_, v_fallback_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___redArg___boxed(lean_object* v_t_721_, lean_object* v_fallback_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Std_TreeMap_Raw_maxEntryD___redArg(v_t_721_, v_fallback_722_);
lean_dec_ref(v_fallback_722_);
lean_dec(v_t_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD(lean_object* v_00_u03b1_724_, lean_object* v_00_u03b2_725_, lean_object* v_cmp_726_, lean_object* v_t_727_, lean_object* v_fallback_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_727_, v_fallback_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___boxed(lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_cmp_732_, lean_object* v_t_733_, lean_object* v_fallback_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_TreeMap_Raw_maxEntryD(v_00_u03b1_730_, v_00_u03b2_731_, v_cmp_732_, v_t_733_, v_fallback_734_);
lean_dec_ref(v_fallback_734_);
lean_dec(v_t_733_);
lean_dec_ref(v_cmp_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___redArg(lean_object* v_t_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___redArg___boxed(lean_object* v_t_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_TreeMap_Raw_minKey_x3f___redArg(v_t_738_);
lean_dec(v_t_738_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f(lean_object* v_00_u03b1_740_, lean_object* v_00_u03b2_741_, lean_object* v_cmp_742_, lean_object* v_t_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___boxed(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_cmp_747_, lean_object* v_t_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_TreeMap_Raw_minKey_x3f(v_00_u03b1_745_, v_00_u03b2_746_, v_cmp_747_, v_t_748_);
lean_dec(v_t_748_);
lean_dec_ref(v_cmp_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___redArg(lean_object* v_inst_750_, lean_object* v_t_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_750_, v_t_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___redArg___boxed(lean_object* v_inst_753_, lean_object* v_t_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Std_TreeMap_Raw_minKey_x21___redArg(v_inst_753_, v_t_754_);
lean_dec(v_t_754_);
lean_dec(v_inst_753_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_cmp_758_, lean_object* v_inst_759_, lean_object* v_t_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_759_, v_t_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___boxed(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_cmp_764_, lean_object* v_inst_765_, lean_object* v_t_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_TreeMap_Raw_minKey_x21(v_00_u03b1_762_, v_00_u03b2_763_, v_cmp_764_, v_inst_765_, v_t_766_);
lean_dec(v_t_766_);
lean_dec(v_inst_765_);
lean_dec_ref(v_cmp_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___redArg(lean_object* v_t_768_, lean_object* v_fallback_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_768_, v_fallback_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___redArg___boxed(lean_object* v_t_771_, lean_object* v_fallback_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Std_TreeMap_Raw_minKeyD___redArg(v_t_771_, v_fallback_772_);
lean_dec(v_fallback_772_);
lean_dec(v_t_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD(lean_object* v_00_u03b1_774_, lean_object* v_00_u03b2_775_, lean_object* v_cmp_776_, lean_object* v_t_777_, lean_object* v_fallback_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_777_, v_fallback_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___boxed(lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_cmp_782_, lean_object* v_t_783_, lean_object* v_fallback_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_TreeMap_Raw_minKeyD(v_00_u03b1_780_, v_00_u03b2_781_, v_cmp_782_, v_t_783_, v_fallback_784_);
lean_dec(v_fallback_784_);
lean_dec(v_t_783_);
lean_dec_ref(v_cmp_782_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___redArg(lean_object* v_t_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___redArg___boxed(lean_object* v_t_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_TreeMap_Raw_maxKey_x3f___redArg(v_t_788_);
lean_dec(v_t_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f(lean_object* v_00_u03b1_790_, lean_object* v_00_u03b2_791_, lean_object* v_cmp_792_, lean_object* v_t_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___boxed(lean_object* v_00_u03b1_795_, lean_object* v_00_u03b2_796_, lean_object* v_cmp_797_, lean_object* v_t_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std_TreeMap_Raw_maxKey_x3f(v_00_u03b1_795_, v_00_u03b2_796_, v_cmp_797_, v_t_798_);
lean_dec(v_t_798_);
lean_dec_ref(v_cmp_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___redArg(lean_object* v_inst_800_, lean_object* v_t_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_800_, v_t_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___redArg___boxed(lean_object* v_inst_803_, lean_object* v_t_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_TreeMap_Raw_maxKey_x21___redArg(v_inst_803_, v_t_804_);
lean_dec(v_t_804_);
lean_dec(v_inst_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21(lean_object* v_00_u03b1_806_, lean_object* v_00_u03b2_807_, lean_object* v_cmp_808_, lean_object* v_inst_809_, lean_object* v_t_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_809_, v_t_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___boxed(lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_cmp_814_, lean_object* v_inst_815_, lean_object* v_t_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_TreeMap_Raw_maxKey_x21(v_00_u03b1_812_, v_00_u03b2_813_, v_cmp_814_, v_inst_815_, v_t_816_);
lean_dec(v_t_816_);
lean_dec(v_inst_815_);
lean_dec_ref(v_cmp_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___redArg(lean_object* v_t_818_, lean_object* v_fallback_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_818_, v_fallback_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___redArg___boxed(lean_object* v_t_821_, lean_object* v_fallback_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_TreeMap_Raw_maxKeyD___redArg(v_t_821_, v_fallback_822_);
lean_dec(v_fallback_822_);
lean_dec(v_t_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD(lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_cmp_826_, lean_object* v_t_827_, lean_object* v_fallback_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_827_, v_fallback_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___boxed(lean_object* v_00_u03b1_830_, lean_object* v_00_u03b2_831_, lean_object* v_cmp_832_, lean_object* v_t_833_, lean_object* v_fallback_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Std_TreeMap_Raw_maxKeyD(v_00_u03b1_830_, v_00_u03b2_831_, v_cmp_832_, v_t_833_, v_fallback_834_);
lean_dec(v_fallback_834_);
lean_dec(v_t_833_);
lean_dec_ref(v_cmp_832_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg(lean_object* v_t_836_, lean_object* v_n_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_836_, v_n_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_839_, lean_object* v_n_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg(v_t_839_, v_n_840_);
lean_dec(v_t_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f(lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_cmp_844_, lean_object* v_t_845_, lean_object* v_n_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_845_, v_n_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_848_, lean_object* v_00_u03b2_849_, lean_object* v_cmp_850_, lean_object* v_t_851_, lean_object* v_n_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_TreeMap_Raw_entryAtIdx_x3f(v_00_u03b1_848_, v_00_u03b2_849_, v_cmp_850_, v_t_851_, v_n_852_);
lean_dec(v_t_851_);
lean_dec_ref(v_cmp_850_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___redArg(lean_object* v_inst_854_, lean_object* v_t_855_, lean_object* v_n_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_854_, v_t_855_, v_n_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_858_, lean_object* v_t_859_, lean_object* v_n_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_TreeMap_Raw_entryAtIdx_x21___redArg(v_inst_858_, v_t_859_, v_n_860_);
lean_dec(v_t_859_);
lean_dec_ref(v_inst_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21(lean_object* v_00_u03b1_862_, lean_object* v_00_u03b2_863_, lean_object* v_cmp_864_, lean_object* v_inst_865_, lean_object* v_t_866_, lean_object* v_n_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_865_, v_t_866_, v_n_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_869_, lean_object* v_00_u03b2_870_, lean_object* v_cmp_871_, lean_object* v_inst_872_, lean_object* v_t_873_, lean_object* v_n_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_TreeMap_Raw_entryAtIdx_x21(v_00_u03b1_869_, v_00_u03b2_870_, v_cmp_871_, v_inst_872_, v_t_873_, v_n_874_);
lean_dec(v_t_873_);
lean_dec_ref(v_inst_872_);
lean_dec_ref(v_cmp_871_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___redArg(lean_object* v_t_876_, lean_object* v_n_877_, lean_object* v_fallback_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_876_, v_n_877_, v_fallback_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___redArg___boxed(lean_object* v_t_880_, lean_object* v_n_881_, lean_object* v_fallback_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Std_TreeMap_Raw_entryAtIdxD___redArg(v_t_880_, v_n_881_, v_fallback_882_);
lean_dec_ref(v_fallback_882_);
lean_dec(v_t_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD(lean_object* v_00_u03b1_884_, lean_object* v_00_u03b2_885_, lean_object* v_cmp_886_, lean_object* v_t_887_, lean_object* v_n_888_, lean_object* v_fallback_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_887_, v_n_888_, v_fallback_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___boxed(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_cmp_893_, lean_object* v_t_894_, lean_object* v_n_895_, lean_object* v_fallback_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Std_TreeMap_Raw_entryAtIdxD(v_00_u03b1_891_, v_00_u03b2_892_, v_cmp_893_, v_t_894_, v_n_895_, v_fallback_896_);
lean_dec_ref(v_fallback_896_);
lean_dec(v_t_894_);
lean_dec_ref(v_cmp_893_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg(lean_object* v_t_898_, lean_object* v_n_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_898_, v_n_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_901_, lean_object* v_n_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg(v_t_901_, v_n_902_);
lean_dec(v_t_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f(lean_object* v_00_u03b1_904_, lean_object* v_00_u03b2_905_, lean_object* v_cmp_906_, lean_object* v_t_907_, lean_object* v_n_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_907_, v_n_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_910_, lean_object* v_00_u03b2_911_, lean_object* v_cmp_912_, lean_object* v_t_913_, lean_object* v_n_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Std_TreeMap_Raw_keyAtIdx_x3f(v_00_u03b1_910_, v_00_u03b2_911_, v_cmp_912_, v_t_913_, v_n_914_);
lean_dec(v_t_913_);
lean_dec_ref(v_cmp_912_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___redArg(lean_object* v_inst_916_, lean_object* v_t_917_, lean_object* v_n_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_916_, v_t_917_, v_n_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_920_, lean_object* v_t_921_, lean_object* v_n_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_TreeMap_Raw_keyAtIdx_x21___redArg(v_inst_920_, v_t_921_, v_n_922_);
lean_dec(v_t_921_);
lean_dec(v_inst_920_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_cmp_926_, lean_object* v_inst_927_, lean_object* v_t_928_, lean_object* v_n_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_927_, v_t_928_, v_n_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_931_, lean_object* v_00_u03b2_932_, lean_object* v_cmp_933_, lean_object* v_inst_934_, lean_object* v_t_935_, lean_object* v_n_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_TreeMap_Raw_keyAtIdx_x21(v_00_u03b1_931_, v_00_u03b2_932_, v_cmp_933_, v_inst_934_, v_t_935_, v_n_936_);
lean_dec(v_t_935_);
lean_dec(v_inst_934_);
lean_dec_ref(v_cmp_933_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___redArg(lean_object* v_t_938_, lean_object* v_n_939_, lean_object* v_fallback_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_938_, v_n_939_, v_fallback_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___redArg___boxed(lean_object* v_t_942_, lean_object* v_n_943_, lean_object* v_fallback_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_TreeMap_Raw_keyAtIdxD___redArg(v_t_942_, v_n_943_, v_fallback_944_);
lean_dec(v_fallback_944_);
lean_dec(v_t_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_cmp_948_, lean_object* v_t_949_, lean_object* v_n_950_, lean_object* v_fallback_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_949_, v_n_950_, v_fallback_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___boxed(lean_object* v_00_u03b1_953_, lean_object* v_00_u03b2_954_, lean_object* v_cmp_955_, lean_object* v_t_956_, lean_object* v_n_957_, lean_object* v_fallback_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Std_TreeMap_Raw_keyAtIdxD(v_00_u03b1_953_, v_00_u03b2_954_, v_cmp_955_, v_t_956_, v_n_957_, v_fallback_958_);
lean_dec(v_fallback_958_);
lean_dec(v_t_956_);
lean_dec_ref(v_cmp_955_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x3f___redArg(lean_object* v_cmp_960_, lean_object* v_t_961_, lean_object* v_k_962_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_box(0);
v___x_964_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_960_, v_k_962_, v___x_963_, v_t_961_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x3f(lean_object* v_00_u03b1_965_, lean_object* v_00_u03b2_966_, lean_object* v_cmp_967_, lean_object* v_t_968_, lean_object* v_k_969_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_box(0);
v___x_971_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_967_, v_k_969_, v___x_970_, v_t_968_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x3f___redArg(lean_object* v_cmp_972_, lean_object* v_t_973_, lean_object* v_k_974_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_box(0);
v___x_976_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_972_, v_k_974_, v___x_975_, v_t_973_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x3f(lean_object* v_00_u03b1_977_, lean_object* v_00_u03b2_978_, lean_object* v_cmp_979_, lean_object* v_t_980_, lean_object* v_k_981_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_box(0);
v___x_983_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_979_, v_k_981_, v___x_982_, v_t_980_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x3f___redArg(lean_object* v_cmp_984_, lean_object* v_t_985_, lean_object* v_k_986_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_box(0);
v___x_988_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_984_, v_k_986_, v___x_987_, v_t_985_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x3f(lean_object* v_00_u03b1_989_, lean_object* v_00_u03b2_990_, lean_object* v_cmp_991_, lean_object* v_t_992_, lean_object* v_k_993_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_box(0);
v___x_995_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_991_, v_k_993_, v___x_994_, v_t_992_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x3f___redArg(lean_object* v_cmp_996_, lean_object* v_t_997_, lean_object* v_k_998_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_box(0);
v___x_1000_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_996_, v_k_998_, v___x_999_, v_t_997_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x3f(lean_object* v_00_u03b1_1001_, lean_object* v_00_u03b2_1002_, lean_object* v_cmp_1003_, lean_object* v_t_1004_, lean_object* v_k_1005_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_box(0);
v___x_1007_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1003_, v_k_1005_, v___x_1006_, v_t_1004_);
return v___x_1007_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1011_ = ((lean_object*)(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__2));
v___x_1012_ = lean_unsigned_to_nat(14u);
v___x_1013_ = lean_unsigned_to_nat(22u);
v___x_1014_ = ((lean_object*)(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__1));
v___x_1015_ = ((lean_object*)(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__0));
v___x_1016_ = l_mkPanicMessageWithDecl(v___x_1015_, v___x_1014_, v___x_1013_, v___x_1012_, v___x_1011_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___redArg(lean_object* v_cmp_1017_, lean_object* v_inst_1018_, lean_object* v_t_1019_, lean_object* v_k_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_box(0);
v___x_1022_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1017_, v_k_1020_, v___x_1021_, v_t_1019_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1024_ = l_panic___redArg(v_inst_1018_, v___x_1023_);
return v___x_1024_;
}
else
{
lean_object* v_val_1025_; 
v_val_1025_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_val_1025_);
lean_dec_ref_known(v___x_1022_, 1);
return v_val_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1026_, lean_object* v_inst_1027_, lean_object* v_t_1028_, lean_object* v_k_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Std_TreeMap_Raw_getEntryGE_x21___redArg(v_cmp_1026_, v_inst_1027_, v_t_1028_, v_k_1029_);
lean_dec_ref(v_inst_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21(lean_object* v_00_u03b1_1031_, lean_object* v_00_u03b2_1032_, lean_object* v_cmp_1033_, lean_object* v_inst_1034_, lean_object* v_t_1035_, lean_object* v_k_1036_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1033_, v_k_1036_, v___x_1037_, v_t_1035_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1040_ = l_panic___redArg(v_inst_1034_, v___x_1039_);
return v___x_1040_;
}
else
{
lean_object* v_val_1041_; 
v_val_1041_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_val_1041_);
lean_dec_ref_known(v___x_1038_, 1);
return v_val_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_cmp_1044_, lean_object* v_inst_1045_, lean_object* v_t_1046_, lean_object* v_k_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_TreeMap_Raw_getEntryGE_x21(v_00_u03b1_1042_, v_00_u03b2_1043_, v_cmp_1044_, v_inst_1045_, v_t_1046_, v_k_1047_);
lean_dec_ref(v_inst_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21___redArg(lean_object* v_cmp_1049_, lean_object* v_inst_1050_, lean_object* v_t_1051_, lean_object* v_k_1052_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_box(0);
v___x_1054_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1049_, v_k_1052_, v___x_1053_, v_t_1051_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1056_ = l_panic___redArg(v_inst_1050_, v___x_1055_);
return v___x_1056_;
}
else
{
lean_object* v_val_1057_; 
v_val_1057_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_val_1057_);
lean_dec_ref_known(v___x_1054_, 1);
return v_val_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1058_, lean_object* v_inst_1059_, lean_object* v_t_1060_, lean_object* v_k_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Std_TreeMap_Raw_getEntryGT_x21___redArg(v_cmp_1058_, v_inst_1059_, v_t_1060_, v_k_1061_);
lean_dec_ref(v_inst_1059_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21(lean_object* v_00_u03b1_1063_, lean_object* v_00_u03b2_1064_, lean_object* v_cmp_1065_, lean_object* v_inst_1066_, lean_object* v_t_1067_, lean_object* v_k_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_box(0);
v___x_1070_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1065_, v_k_1068_, v___x_1069_, v_t_1067_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1072_ = l_panic___redArg(v_inst_1066_, v___x_1071_);
return v___x_1072_;
}
else
{
lean_object* v_val_1073_; 
v_val_1073_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_val_1073_);
lean_dec_ref_known(v___x_1070_, 1);
return v_val_1073_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1074_, lean_object* v_00_u03b2_1075_, lean_object* v_cmp_1076_, lean_object* v_inst_1077_, lean_object* v_t_1078_, lean_object* v_k_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Std_TreeMap_Raw_getEntryGT_x21(v_00_u03b1_1074_, v_00_u03b2_1075_, v_cmp_1076_, v_inst_1077_, v_t_1078_, v_k_1079_);
lean_dec_ref(v_inst_1077_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21___redArg(lean_object* v_cmp_1081_, lean_object* v_inst_1082_, lean_object* v_t_1083_, lean_object* v_k_1084_){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_box(0);
v___x_1086_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1081_, v_k_1084_, v___x_1085_, v_t_1083_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1088_ = l_panic___redArg(v_inst_1082_, v___x_1087_);
return v___x_1088_;
}
else
{
lean_object* v_val_1089_; 
v_val_1089_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_val_1089_);
lean_dec_ref_known(v___x_1086_, 1);
return v_val_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1090_, lean_object* v_inst_1091_, lean_object* v_t_1092_, lean_object* v_k_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Std_TreeMap_Raw_getEntryLE_x21___redArg(v_cmp_1090_, v_inst_1091_, v_t_1092_, v_k_1093_);
lean_dec_ref(v_inst_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21(lean_object* v_00_u03b1_1095_, lean_object* v_00_u03b2_1096_, lean_object* v_cmp_1097_, lean_object* v_inst_1098_, lean_object* v_t_1099_, lean_object* v_k_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_box(0);
v___x_1102_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1097_, v_k_1100_, v___x_1101_, v_t_1099_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1104_ = l_panic___redArg(v_inst_1098_, v___x_1103_);
return v___x_1104_;
}
else
{
lean_object* v_val_1105_; 
v_val_1105_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_val_1105_);
lean_dec_ref_known(v___x_1102_, 1);
return v_val_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_cmp_1108_, lean_object* v_inst_1109_, lean_object* v_t_1110_, lean_object* v_k_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Std_TreeMap_Raw_getEntryLE_x21(v_00_u03b1_1106_, v_00_u03b2_1107_, v_cmp_1108_, v_inst_1109_, v_t_1110_, v_k_1111_);
lean_dec_ref(v_inst_1109_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21___redArg(lean_object* v_cmp_1113_, lean_object* v_inst_1114_, lean_object* v_t_1115_, lean_object* v_k_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_box(0);
v___x_1118_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1113_, v_k_1116_, v___x_1117_, v_t_1115_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1120_ = l_panic___redArg(v_inst_1114_, v___x_1119_);
return v___x_1120_;
}
else
{
lean_object* v_val_1121_; 
v_val_1121_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_val_1121_);
lean_dec_ref_known(v___x_1118_, 1);
return v_val_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1122_, lean_object* v_inst_1123_, lean_object* v_t_1124_, lean_object* v_k_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Std_TreeMap_Raw_getEntryLT_x21___redArg(v_cmp_1122_, v_inst_1123_, v_t_1124_, v_k_1125_);
lean_dec_ref(v_inst_1123_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21(lean_object* v_00_u03b1_1127_, lean_object* v_00_u03b2_1128_, lean_object* v_cmp_1129_, lean_object* v_inst_1130_, lean_object* v_t_1131_, lean_object* v_k_1132_){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_box(0);
v___x_1134_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1129_, v_k_1132_, v___x_1133_, v_t_1131_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1136_ = l_panic___redArg(v_inst_1130_, v___x_1135_);
return v___x_1136_;
}
else
{
lean_object* v_val_1137_; 
v_val_1137_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_val_1137_);
lean_dec_ref_known(v___x_1134_, 1);
return v_val_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1138_, lean_object* v_00_u03b2_1139_, lean_object* v_cmp_1140_, lean_object* v_inst_1141_, lean_object* v_t_1142_, lean_object* v_k_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_TreeMap_Raw_getEntryLT_x21(v_00_u03b1_1138_, v_00_u03b2_1139_, v_cmp_1140_, v_inst_1141_, v_t_1142_, v_k_1143_);
lean_dec_ref(v_inst_1141_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___redArg(lean_object* v_cmp_1145_, lean_object* v_t_1146_, lean_object* v_k_1147_, lean_object* v_fallback_1148_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1145_, v_k_1147_, v___x_1149_, v_t_1146_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_inc_ref(v_fallback_1148_);
return v_fallback_1148_;
}
else
{
lean_object* v_val_1151_; 
v_val_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_val_1151_);
lean_dec_ref_known(v___x_1150_, 1);
return v_val_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___redArg___boxed(lean_object* v_cmp_1152_, lean_object* v_t_1153_, lean_object* v_k_1154_, lean_object* v_fallback_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_TreeMap_Raw_getEntryGED___redArg(v_cmp_1152_, v_t_1153_, v_k_1154_, v_fallback_1155_);
lean_dec_ref(v_fallback_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_cmp_1159_, lean_object* v_t_1160_, lean_object* v_k_1161_, lean_object* v_fallback_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_box(0);
v___x_1164_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1159_, v_k_1161_, v___x_1163_, v_t_1160_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_inc_ref(v_fallback_1162_);
return v_fallback_1162_;
}
else
{
lean_object* v_val_1165_; 
v_val_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_val_1165_);
lean_dec_ref_known(v___x_1164_, 1);
return v_val_1165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___boxed(lean_object* v_00_u03b1_1166_, lean_object* v_00_u03b2_1167_, lean_object* v_cmp_1168_, lean_object* v_t_1169_, lean_object* v_k_1170_, lean_object* v_fallback_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Std_TreeMap_Raw_getEntryGED(v_00_u03b1_1166_, v_00_u03b2_1167_, v_cmp_1168_, v_t_1169_, v_k_1170_, v_fallback_1171_);
lean_dec_ref(v_fallback_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___redArg(lean_object* v_cmp_1173_, lean_object* v_t_1174_, lean_object* v_k_1175_, lean_object* v_fallback_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1173_, v_k_1175_, v___x_1177_, v_t_1174_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_inc_ref(v_fallback_1176_);
return v_fallback_1176_;
}
else
{
lean_object* v_val_1179_; 
v_val_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_val_1179_);
lean_dec_ref_known(v___x_1178_, 1);
return v_val_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___redArg___boxed(lean_object* v_cmp_1180_, lean_object* v_t_1181_, lean_object* v_k_1182_, lean_object* v_fallback_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_TreeMap_Raw_getEntryGTD___redArg(v_cmp_1180_, v_t_1181_, v_k_1182_, v_fallback_1183_);
lean_dec_ref(v_fallback_1183_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD(lean_object* v_00_u03b1_1185_, lean_object* v_00_u03b2_1186_, lean_object* v_cmp_1187_, lean_object* v_t_1188_, lean_object* v_k_1189_, lean_object* v_fallback_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1187_, v_k_1189_, v___x_1191_, v_t_1188_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_inc_ref(v_fallback_1190_);
return v_fallback_1190_;
}
else
{
lean_object* v_val_1193_; 
v_val_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_val_1193_);
lean_dec_ref_known(v___x_1192_, 1);
return v_val_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_cmp_1196_, lean_object* v_t_1197_, lean_object* v_k_1198_, lean_object* v_fallback_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_TreeMap_Raw_getEntryGTD(v_00_u03b1_1194_, v_00_u03b2_1195_, v_cmp_1196_, v_t_1197_, v_k_1198_, v_fallback_1199_);
lean_dec_ref(v_fallback_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___redArg(lean_object* v_cmp_1201_, lean_object* v_t_1202_, lean_object* v_k_1203_, lean_object* v_fallback_1204_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_box(0);
v___x_1206_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1201_, v_k_1203_, v___x_1205_, v_t_1202_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_inc_ref(v_fallback_1204_);
return v_fallback_1204_;
}
else
{
lean_object* v_val_1207_; 
v_val_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_val_1207_);
lean_dec_ref_known(v___x_1206_, 1);
return v_val_1207_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___redArg___boxed(lean_object* v_cmp_1208_, lean_object* v_t_1209_, lean_object* v_k_1210_, lean_object* v_fallback_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Std_TreeMap_Raw_getEntryLED___redArg(v_cmp_1208_, v_t_1209_, v_k_1210_, v_fallback_1211_);
lean_dec_ref(v_fallback_1211_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED(lean_object* v_00_u03b1_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_cmp_1215_, lean_object* v_t_1216_, lean_object* v_k_1217_, lean_object* v_fallback_1218_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_box(0);
v___x_1220_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1215_, v_k_1217_, v___x_1219_, v_t_1216_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_inc_ref(v_fallback_1218_);
return v_fallback_1218_;
}
else
{
lean_object* v_val_1221_; 
v_val_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_val_1221_);
lean_dec_ref_known(v___x_1220_, 1);
return v_val_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___boxed(lean_object* v_00_u03b1_1222_, lean_object* v_00_u03b2_1223_, lean_object* v_cmp_1224_, lean_object* v_t_1225_, lean_object* v_k_1226_, lean_object* v_fallback_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Std_TreeMap_Raw_getEntryLED(v_00_u03b1_1222_, v_00_u03b2_1223_, v_cmp_1224_, v_t_1225_, v_k_1226_, v_fallback_1227_);
lean_dec_ref(v_fallback_1227_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___redArg(lean_object* v_cmp_1229_, lean_object* v_t_1230_, lean_object* v_k_1231_, lean_object* v_fallback_1232_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_box(0);
v___x_1234_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1229_, v_k_1231_, v___x_1233_, v_t_1230_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_inc_ref(v_fallback_1232_);
return v_fallback_1232_;
}
else
{
lean_object* v_val_1235_; 
v_val_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_val_1235_);
lean_dec_ref_known(v___x_1234_, 1);
return v_val_1235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___redArg___boxed(lean_object* v_cmp_1236_, lean_object* v_t_1237_, lean_object* v_k_1238_, lean_object* v_fallback_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Std_TreeMap_Raw_getEntryLTD___redArg(v_cmp_1236_, v_t_1237_, v_k_1238_, v_fallback_1239_);
lean_dec_ref(v_fallback_1239_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD(lean_object* v_00_u03b1_1241_, lean_object* v_00_u03b2_1242_, lean_object* v_cmp_1243_, lean_object* v_t_1244_, lean_object* v_k_1245_, lean_object* v_fallback_1246_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_box(0);
v___x_1248_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1243_, v_k_1245_, v___x_1247_, v_t_1244_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_inc_ref(v_fallback_1246_);
return v_fallback_1246_;
}
else
{
lean_object* v_val_1249_; 
v_val_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_val_1249_);
lean_dec_ref_known(v___x_1248_, 1);
return v_val_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___boxed(lean_object* v_00_u03b1_1250_, lean_object* v_00_u03b2_1251_, lean_object* v_cmp_1252_, lean_object* v_t_1253_, lean_object* v_k_1254_, lean_object* v_fallback_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_TreeMap_Raw_getEntryLTD(v_00_u03b1_1250_, v_00_u03b2_1251_, v_cmp_1252_, v_t_1253_, v_k_1254_, v_fallback_1255_);
lean_dec_ref(v_fallback_1255_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x3f___redArg(lean_object* v_cmp_1257_, lean_object* v_t_1258_, lean_object* v_k_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_box(0);
v___x_1261_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1257_, v_k_1259_, v___x_1260_, v_t_1258_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x3f(lean_object* v_00_u03b1_1262_, lean_object* v_00_u03b2_1263_, lean_object* v_cmp_1264_, lean_object* v_t_1265_, lean_object* v_k_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1264_, v_k_1266_, v___x_1267_, v_t_1265_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x3f___redArg(lean_object* v_cmp_1269_, lean_object* v_t_1270_, lean_object* v_k_1271_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_box(0);
v___x_1273_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1269_, v_k_1271_, v___x_1272_, v_t_1270_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x3f(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_cmp_1276_, lean_object* v_t_1277_, lean_object* v_k_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_box(0);
v___x_1280_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1276_, v_k_1278_, v___x_1279_, v_t_1277_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x3f___redArg(lean_object* v_cmp_1281_, lean_object* v_t_1282_, lean_object* v_k_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_box(0);
v___x_1285_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1281_, v_k_1283_, v___x_1284_, v_t_1282_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x3f(lean_object* v_00_u03b1_1286_, lean_object* v_00_u03b2_1287_, lean_object* v_cmp_1288_, lean_object* v_t_1289_, lean_object* v_k_1290_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_box(0);
v___x_1292_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1288_, v_k_1290_, v___x_1291_, v_t_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x3f___redArg(lean_object* v_cmp_1293_, lean_object* v_t_1294_, lean_object* v_k_1295_){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1293_, v_k_1295_, v___x_1296_, v_t_1294_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x3f(lean_object* v_00_u03b1_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_cmp_1300_, lean_object* v_t_1301_, lean_object* v_k_1302_){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_box(0);
v___x_1304_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1300_, v_k_1302_, v___x_1303_, v_t_1301_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21___redArg(lean_object* v_cmp_1305_, lean_object* v_inst_1306_, lean_object* v_t_1307_, lean_object* v_k_1308_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1305_, v_k_1308_, v___x_1309_, v_t_1307_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1312_ = l_panic___redArg(v_inst_1306_, v___x_1311_);
return v___x_1312_;
}
else
{
lean_object* v_val_1313_; 
v_val_1313_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v___x_1310_, 1);
return v_val_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1314_, lean_object* v_inst_1315_, lean_object* v_t_1316_, lean_object* v_k_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Std_TreeMap_Raw_getKeyGE_x21___redArg(v_cmp_1314_, v_inst_1315_, v_t_1316_, v_k_1317_);
lean_dec(v_inst_1315_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21(lean_object* v_00_u03b1_1319_, lean_object* v_00_u03b2_1320_, lean_object* v_cmp_1321_, lean_object* v_inst_1322_, lean_object* v_t_1323_, lean_object* v_k_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_box(0);
v___x_1326_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1321_, v_k_1324_, v___x_1325_, v_t_1323_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1328_ = l_panic___redArg(v_inst_1322_, v___x_1327_);
return v___x_1328_;
}
else
{
lean_object* v_val_1329_; 
v_val_1329_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_val_1329_);
lean_dec_ref_known(v___x_1326_, 1);
return v_val_1329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1330_, lean_object* v_00_u03b2_1331_, lean_object* v_cmp_1332_, lean_object* v_inst_1333_, lean_object* v_t_1334_, lean_object* v_k_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_TreeMap_Raw_getKeyGE_x21(v_00_u03b1_1330_, v_00_u03b2_1331_, v_cmp_1332_, v_inst_1333_, v_t_1334_, v_k_1335_);
lean_dec(v_inst_1333_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21___redArg(lean_object* v_cmp_1337_, lean_object* v_inst_1338_, lean_object* v_t_1339_, lean_object* v_k_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1337_, v_k_1340_, v___x_1341_, v_t_1339_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1344_ = l_panic___redArg(v_inst_1338_, v___x_1343_);
return v___x_1344_;
}
else
{
lean_object* v_val_1345_; 
v_val_1345_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v___x_1342_, 1);
return v_val_1345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1346_, lean_object* v_inst_1347_, lean_object* v_t_1348_, lean_object* v_k_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Std_TreeMap_Raw_getKeyGT_x21___redArg(v_cmp_1346_, v_inst_1347_, v_t_1348_, v_k_1349_);
lean_dec(v_inst_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21(lean_object* v_00_u03b1_1351_, lean_object* v_00_u03b2_1352_, lean_object* v_cmp_1353_, lean_object* v_inst_1354_, lean_object* v_t_1355_, lean_object* v_k_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_box(0);
v___x_1358_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1353_, v_k_1356_, v___x_1357_, v_t_1355_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1360_ = l_panic___redArg(v_inst_1354_, v___x_1359_);
return v___x_1360_;
}
else
{
lean_object* v_val_1361_; 
v_val_1361_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_val_1361_);
lean_dec_ref_known(v___x_1358_, 1);
return v_val_1361_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1362_, lean_object* v_00_u03b2_1363_, lean_object* v_cmp_1364_, lean_object* v_inst_1365_, lean_object* v_t_1366_, lean_object* v_k_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Std_TreeMap_Raw_getKeyGT_x21(v_00_u03b1_1362_, v_00_u03b2_1363_, v_cmp_1364_, v_inst_1365_, v_t_1366_, v_k_1367_);
lean_dec(v_inst_1365_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21___redArg(lean_object* v_cmp_1369_, lean_object* v_inst_1370_, lean_object* v_t_1371_, lean_object* v_k_1372_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_box(0);
v___x_1374_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1369_, v_k_1372_, v___x_1373_, v_t_1371_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1376_ = l_panic___redArg(v_inst_1370_, v___x_1375_);
return v___x_1376_;
}
else
{
lean_object* v_val_1377_; 
v_val_1377_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v___x_1374_, 1);
return v_val_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1378_, lean_object* v_inst_1379_, lean_object* v_t_1380_, lean_object* v_k_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Std_TreeMap_Raw_getKeyLE_x21___redArg(v_cmp_1378_, v_inst_1379_, v_t_1380_, v_k_1381_);
lean_dec(v_inst_1379_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21(lean_object* v_00_u03b1_1383_, lean_object* v_00_u03b2_1384_, lean_object* v_cmp_1385_, lean_object* v_inst_1386_, lean_object* v_t_1387_, lean_object* v_k_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1385_, v_k_1388_, v___x_1389_, v_t_1387_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1392_ = l_panic___redArg(v_inst_1386_, v___x_1391_);
return v___x_1392_;
}
else
{
lean_object* v_val_1393_; 
v_val_1393_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_val_1393_);
lean_dec_ref_known(v___x_1390_, 1);
return v_val_1393_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1394_, lean_object* v_00_u03b2_1395_, lean_object* v_cmp_1396_, lean_object* v_inst_1397_, lean_object* v_t_1398_, lean_object* v_k_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Std_TreeMap_Raw_getKeyLE_x21(v_00_u03b1_1394_, v_00_u03b2_1395_, v_cmp_1396_, v_inst_1397_, v_t_1398_, v_k_1399_);
lean_dec(v_inst_1397_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21___redArg(lean_object* v_cmp_1401_, lean_object* v_inst_1402_, lean_object* v_t_1403_, lean_object* v_k_1404_){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_box(0);
v___x_1406_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1401_, v_k_1404_, v___x_1405_, v_t_1403_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1408_ = l_panic___redArg(v_inst_1402_, v___x_1407_);
return v___x_1408_;
}
else
{
lean_object* v_val_1409_; 
v_val_1409_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_val_1409_);
lean_dec_ref_known(v___x_1406_, 1);
return v_val_1409_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1410_, lean_object* v_inst_1411_, lean_object* v_t_1412_, lean_object* v_k_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Std_TreeMap_Raw_getKeyLT_x21___redArg(v_cmp_1410_, v_inst_1411_, v_t_1412_, v_k_1413_);
lean_dec(v_inst_1411_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_cmp_1417_, lean_object* v_inst_1418_, lean_object* v_t_1419_, lean_object* v_k_1420_){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_box(0);
v___x_1422_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1417_, v_k_1420_, v___x_1421_, v_t_1419_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1424_ = l_panic___redArg(v_inst_1418_, v___x_1423_);
return v___x_1424_;
}
else
{
lean_object* v_val_1425_; 
v_val_1425_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_val_1425_);
lean_dec_ref_known(v___x_1422_, 1);
return v_val_1425_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1426_, lean_object* v_00_u03b2_1427_, lean_object* v_cmp_1428_, lean_object* v_inst_1429_, lean_object* v_t_1430_, lean_object* v_k_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Std_TreeMap_Raw_getKeyLT_x21(v_00_u03b1_1426_, v_00_u03b2_1427_, v_cmp_1428_, v_inst_1429_, v_t_1430_, v_k_1431_);
lean_dec(v_inst_1429_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___redArg(lean_object* v_cmp_1433_, lean_object* v_t_1434_, lean_object* v_k_1435_, lean_object* v_fallback_1436_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_box(0);
v___x_1438_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1433_, v_k_1435_, v___x_1437_, v_t_1434_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_inc(v_fallback_1436_);
return v_fallback_1436_;
}
else
{
lean_object* v_val_1439_; 
v_val_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_val_1439_);
lean_dec_ref_known(v___x_1438_, 1);
return v_val_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___redArg___boxed(lean_object* v_cmp_1440_, lean_object* v_t_1441_, lean_object* v_k_1442_, lean_object* v_fallback_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Std_TreeMap_Raw_getKeyGED___redArg(v_cmp_1440_, v_t_1441_, v_k_1442_, v_fallback_1443_);
lean_dec(v_fallback_1443_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED(lean_object* v_00_u03b1_1445_, lean_object* v_00_u03b2_1446_, lean_object* v_cmp_1447_, lean_object* v_t_1448_, lean_object* v_k_1449_, lean_object* v_fallback_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_box(0);
v___x_1452_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1447_, v_k_1449_, v___x_1451_, v_t_1448_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_inc(v_fallback_1450_);
return v_fallback_1450_;
}
else
{
lean_object* v_val_1453_; 
v_val_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_val_1453_);
lean_dec_ref_known(v___x_1452_, 1);
return v_val_1453_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___boxed(lean_object* v_00_u03b1_1454_, lean_object* v_00_u03b2_1455_, lean_object* v_cmp_1456_, lean_object* v_t_1457_, lean_object* v_k_1458_, lean_object* v_fallback_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Std_TreeMap_Raw_getKeyGED(v_00_u03b1_1454_, v_00_u03b2_1455_, v_cmp_1456_, v_t_1457_, v_k_1458_, v_fallback_1459_);
lean_dec(v_fallback_1459_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___redArg(lean_object* v_cmp_1461_, lean_object* v_t_1462_, lean_object* v_k_1463_, lean_object* v_fallback_1464_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_box(0);
v___x_1466_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1461_, v_k_1463_, v___x_1465_, v_t_1462_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_inc(v_fallback_1464_);
return v_fallback_1464_;
}
else
{
lean_object* v_val_1467_; 
v_val_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_val_1467_);
lean_dec_ref_known(v___x_1466_, 1);
return v_val_1467_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___redArg___boxed(lean_object* v_cmp_1468_, lean_object* v_t_1469_, lean_object* v_k_1470_, lean_object* v_fallback_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Std_TreeMap_Raw_getKeyGTD___redArg(v_cmp_1468_, v_t_1469_, v_k_1470_, v_fallback_1471_);
lean_dec(v_fallback_1471_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD(lean_object* v_00_u03b1_1473_, lean_object* v_00_u03b2_1474_, lean_object* v_cmp_1475_, lean_object* v_t_1476_, lean_object* v_k_1477_, lean_object* v_fallback_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_box(0);
v___x_1480_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1475_, v_k_1477_, v___x_1479_, v_t_1476_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_inc(v_fallback_1478_);
return v_fallback_1478_;
}
else
{
lean_object* v_val_1481_; 
v_val_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_val_1481_);
lean_dec_ref_known(v___x_1480_, 1);
return v_val_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___boxed(lean_object* v_00_u03b1_1482_, lean_object* v_00_u03b2_1483_, lean_object* v_cmp_1484_, lean_object* v_t_1485_, lean_object* v_k_1486_, lean_object* v_fallback_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Std_TreeMap_Raw_getKeyGTD(v_00_u03b1_1482_, v_00_u03b2_1483_, v_cmp_1484_, v_t_1485_, v_k_1486_, v_fallback_1487_);
lean_dec(v_fallback_1487_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___redArg(lean_object* v_cmp_1489_, lean_object* v_t_1490_, lean_object* v_k_1491_, lean_object* v_fallback_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1489_, v_k_1491_, v___x_1493_, v_t_1490_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_inc(v_fallback_1492_);
return v_fallback_1492_;
}
else
{
lean_object* v_val_1495_; 
v_val_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v___x_1494_, 1);
return v_val_1495_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___redArg___boxed(lean_object* v_cmp_1496_, lean_object* v_t_1497_, lean_object* v_k_1498_, lean_object* v_fallback_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Std_TreeMap_Raw_getKeyLED___redArg(v_cmp_1496_, v_t_1497_, v_k_1498_, v_fallback_1499_);
lean_dec(v_fallback_1499_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED(lean_object* v_00_u03b1_1501_, lean_object* v_00_u03b2_1502_, lean_object* v_cmp_1503_, lean_object* v_t_1504_, lean_object* v_k_1505_, lean_object* v_fallback_1506_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_box(0);
v___x_1508_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1503_, v_k_1505_, v___x_1507_, v_t_1504_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_inc(v_fallback_1506_);
return v_fallback_1506_;
}
else
{
lean_object* v_val_1509_; 
v_val_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v___x_1508_, 1);
return v_val_1509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___boxed(lean_object* v_00_u03b1_1510_, lean_object* v_00_u03b2_1511_, lean_object* v_cmp_1512_, lean_object* v_t_1513_, lean_object* v_k_1514_, lean_object* v_fallback_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Std_TreeMap_Raw_getKeyLED(v_00_u03b1_1510_, v_00_u03b2_1511_, v_cmp_1512_, v_t_1513_, v_k_1514_, v_fallback_1515_);
lean_dec(v_fallback_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___redArg(lean_object* v_cmp_1517_, lean_object* v_t_1518_, lean_object* v_k_1519_, lean_object* v_fallback_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_box(0);
v___x_1522_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1517_, v_k_1519_, v___x_1521_, v_t_1518_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_inc(v_fallback_1520_);
return v_fallback_1520_;
}
else
{
lean_object* v_val_1523_; 
v_val_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_val_1523_);
lean_dec_ref_known(v___x_1522_, 1);
return v_val_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___redArg___boxed(lean_object* v_cmp_1524_, lean_object* v_t_1525_, lean_object* v_k_1526_, lean_object* v_fallback_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Std_TreeMap_Raw_getKeyLTD___redArg(v_cmp_1524_, v_t_1525_, v_k_1526_, v_fallback_1527_);
lean_dec(v_fallback_1527_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD(lean_object* v_00_u03b1_1529_, lean_object* v_00_u03b2_1530_, lean_object* v_cmp_1531_, lean_object* v_t_1532_, lean_object* v_k_1533_, lean_object* v_fallback_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_box(0);
v___x_1536_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1531_, v_k_1533_, v___x_1535_, v_t_1532_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_inc(v_fallback_1534_);
return v_fallback_1534_;
}
else
{
lean_object* v_val_1537_; 
v_val_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_val_1537_);
lean_dec_ref_known(v___x_1536_, 1);
return v_val_1537_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___boxed(lean_object* v_00_u03b1_1538_, lean_object* v_00_u03b2_1539_, lean_object* v_cmp_1540_, lean_object* v_t_1541_, lean_object* v_k_1542_, lean_object* v_fallback_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Std_TreeMap_Raw_getKeyLTD(v_00_u03b1_1538_, v_00_u03b2_1539_, v_cmp_1540_, v_t_1541_, v_k_1542_, v_fallback_1543_);
lean_dec(v_fallback_1543_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter___redArg(lean_object* v_f_1545_, lean_object* v_t_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_1545_, v_t_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter(lean_object* v_00_u03b1_1548_, lean_object* v_00_u03b2_1549_, lean_object* v_cmp_1550_, lean_object* v_f_1551_, lean_object* v_t_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_1551_, v_t_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter___boxed(lean_object* v_00_u03b1_1554_, lean_object* v_00_u03b2_1555_, lean_object* v_cmp_1556_, lean_object* v_f_1557_, lean_object* v_t_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Std_TreeMap_Raw_filter(v_00_u03b1_1554_, v_00_u03b2_1555_, v_cmp_1556_, v_f_1557_, v_t_1558_);
lean_dec_ref(v_cmp_1556_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM___redArg(lean_object* v_inst_1560_, lean_object* v_f_1561_, lean_object* v_init_1562_, lean_object* v_t_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1560_, v_f_1561_, v_init_1562_, v_t_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM(lean_object* v_00_u03b1_1565_, lean_object* v_00_u03b2_1566_, lean_object* v_cmp_1567_, lean_object* v_00_u03b4_1568_, lean_object* v_m_1569_, lean_object* v_inst_1570_, lean_object* v_f_1571_, lean_object* v_init_1572_, lean_object* v_t_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1570_, v_f_1571_, v_init_1572_, v_t_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM___boxed(lean_object* v_00_u03b1_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_cmp_1577_, lean_object* v_00_u03b4_1578_, lean_object* v_m_1579_, lean_object* v_inst_1580_, lean_object* v_f_1581_, lean_object* v_init_1582_, lean_object* v_t_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Std_TreeMap_Raw_foldlM(v_00_u03b1_1575_, v_00_u03b2_1576_, v_cmp_1577_, v_00_u03b4_1578_, v_m_1579_, v_inst_1580_, v_f_1581_, v_init_1582_, v_t_1583_);
lean_dec_ref(v_cmp_1577_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl___redArg(lean_object* v_f_1585_, lean_object* v_init_1586_, lean_object* v_t_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1585_, v_init_1586_, v_t_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl(lean_object* v_00_u03b1_1589_, lean_object* v_00_u03b2_1590_, lean_object* v_cmp_1591_, lean_object* v_00_u03b4_1592_, lean_object* v_f_1593_, lean_object* v_init_1594_, lean_object* v_t_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1593_, v_init_1594_, v_t_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl___boxed(lean_object* v_00_u03b1_1597_, lean_object* v_00_u03b2_1598_, lean_object* v_cmp_1599_, lean_object* v_00_u03b4_1600_, lean_object* v_f_1601_, lean_object* v_init_1602_, lean_object* v_t_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Std_TreeMap_Raw_foldl(v_00_u03b1_1597_, v_00_u03b2_1598_, v_cmp_1599_, v_00_u03b4_1600_, v_f_1601_, v_init_1602_, v_t_1603_);
lean_dec_ref(v_cmp_1599_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM___redArg(lean_object* v_inst_1605_, lean_object* v_f_1606_, lean_object* v_init_1607_, lean_object* v_t_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1605_, v_f_1606_, v_init_1607_, v_t_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM(lean_object* v_00_u03b1_1610_, lean_object* v_00_u03b2_1611_, lean_object* v_cmp_1612_, lean_object* v_00_u03b4_1613_, lean_object* v_m_1614_, lean_object* v_inst_1615_, lean_object* v_f_1616_, lean_object* v_init_1617_, lean_object* v_t_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1615_, v_f_1616_, v_init_1617_, v_t_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM___boxed(lean_object* v_00_u03b1_1620_, lean_object* v_00_u03b2_1621_, lean_object* v_cmp_1622_, lean_object* v_00_u03b4_1623_, lean_object* v_m_1624_, lean_object* v_inst_1625_, lean_object* v_f_1626_, lean_object* v_init_1627_, lean_object* v_t_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Std_TreeMap_Raw_foldrM(v_00_u03b1_1620_, v_00_u03b2_1621_, v_cmp_1622_, v_00_u03b4_1623_, v_m_1624_, v_inst_1625_, v_f_1626_, v_init_1627_, v_t_1628_);
lean_dec_ref(v_cmp_1622_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___redArg___lam__0(lean_object* v_f_1630_, lean_object* v_x1_1631_, lean_object* v_x2_1632_, lean_object* v_x3_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_apply_3(v_f_1630_, v_x1_1631_, v_x2_1632_, v_x3_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___redArg(lean_object* v_f_1654_, lean_object* v_init_1655_, lean_object* v_t_1656_){
_start:
{
lean_object* v___f_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___f_1657_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1657_, 0, v_f_1654_);
v___x_1658_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1659_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1658_, v___f_1657_, v_init_1655_, v_t_1656_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr(lean_object* v_00_u03b1_1660_, lean_object* v_00_u03b2_1661_, lean_object* v_cmp_1662_, lean_object* v_00_u03b4_1663_, lean_object* v_f_1664_, lean_object* v_init_1665_, lean_object* v_t_1666_){
_start:
{
lean_object* v___f_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___f_1667_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1667_, 0, v_f_1664_);
v___x_1668_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1669_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1668_, v___f_1667_, v_init_1665_, v_t_1666_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___boxed(lean_object* v_00_u03b1_1670_, lean_object* v_00_u03b2_1671_, lean_object* v_cmp_1672_, lean_object* v_00_u03b4_1673_, lean_object* v_f_1674_, lean_object* v_init_1675_, lean_object* v_t_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Std_TreeMap_Raw_foldr(v_00_u03b1_1670_, v_00_u03b2_1671_, v_cmp_1672_, v_00_u03b4_1673_, v_f_1674_, v_init_1675_, v_t_1676_);
lean_dec_ref(v_cmp_1672_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition___redArg___lam__0(lean_object* v_f_1678_, lean_object* v_cmp_1679_, lean_object* v_x_1680_, lean_object* v_a_1681_, lean_object* v_b_1682_){
_start:
{
lean_object* v_fst_1683_; lean_object* v_snd_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1698_; 
v_fst_1683_ = lean_ctor_get(v_x_1680_, 0);
v_snd_1684_ = lean_ctor_get(v_x_1680_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_x_1680_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1686_ = v_x_1680_;
v_isShared_1687_ = v_isSharedCheck_1698_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_snd_1684_);
lean_inc(v_fst_1683_);
lean_dec(v_x_1680_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1698_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
lean_inc(v_b_1682_);
lean_inc(v_a_1681_);
v___x_1688_ = lean_apply_2(v_f_1678_, v_a_1681_, v_b_1682_);
v___x_1689_ = lean_unbox(v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1679_, v_a_1681_, v_b_1682_, v_snd_1684_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v___x_1690_);
v___x_1692_ = v___x_1686_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_fst_1683_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1679_, v_a_1681_, v_b_1682_, v_fst_1683_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1694_);
v___x_1696_ = v___x_1686_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_snd_1684_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition___redArg(lean_object* v_cmp_1701_, lean_object* v_f_1702_, lean_object* v_t_1703_){
_start:
{
lean_object* v___f_1704_; lean_object* v___x_1705_; lean_object* v_p_1706_; lean_object* v_fst_1707_; lean_object* v_snd_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v___f_1704_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1704_, 0, v_f_1702_);
lean_closure_set(v___f_1704_, 1, v_cmp_1701_);
v___x_1705_ = ((lean_object*)(l_Std_TreeMap_Raw_partition___redArg___closed__0));
v_p_1706_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1704_, v___x_1705_, v_t_1703_);
v_fst_1707_ = lean_ctor_get(v_p_1706_, 0);
v_snd_1708_ = lean_ctor_get(v_p_1706_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_p_1706_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v_p_1706_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_snd_1708_);
lean_inc(v_fst_1707_);
lean_dec(v_p_1706_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_fst_1707_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_snd_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition(lean_object* v_00_u03b1_1716_, lean_object* v_00_u03b2_1717_, lean_object* v_cmp_1718_, lean_object* v_f_1719_, lean_object* v_t_1720_){
_start:
{
lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v_p_1723_; lean_object* v_fst_1724_; lean_object* v_snd_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
v___f_1721_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1721_, 0, v_f_1719_);
lean_closure_set(v___f_1721_, 1, v_cmp_1718_);
v___x_1722_ = ((lean_object*)(l_Std_TreeMap_Raw_partition___redArg___closed__0));
v_p_1723_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1721_, v___x_1722_, v_t_1720_);
v_fst_1724_ = lean_ctor_get(v_p_1723_, 0);
v_snd_1725_ = lean_ctor_get(v_p_1723_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_p_1723_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v_p_1723_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_snd_1725_);
lean_inc(v_fst_1724_);
lean_dec(v_p_1723_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_fst_1724_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_snd_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___redArg___lam__0(lean_object* v_f_1733_, lean_object* v_x_1734_, lean_object* v_k_1735_, lean_object* v_v_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_apply_2(v_f_1733_, v_k_1735_, v_v_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___redArg(lean_object* v_inst_1738_, lean_object* v_f_1739_, lean_object* v_t_1740_){
_start:
{
lean_object* v___f_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___f_1741_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1741_, 0, v_f_1739_);
v___x_1742_ = lean_box(0);
v___x_1743_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1738_, v___f_1741_, v___x_1742_, v_t_1740_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM(lean_object* v_00_u03b1_1744_, lean_object* v_00_u03b2_1745_, lean_object* v_cmp_1746_, lean_object* v_m_1747_, lean_object* v_inst_1748_, lean_object* v_f_1749_, lean_object* v_t_1750_){
_start:
{
lean_object* v___f_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___f_1751_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1751_, 0, v_f_1749_);
v___x_1752_ = lean_box(0);
v___x_1753_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1748_, v___f_1751_, v___x_1752_, v_t_1750_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___boxed(lean_object* v_00_u03b1_1754_, lean_object* v_00_u03b2_1755_, lean_object* v_cmp_1756_, lean_object* v_m_1757_, lean_object* v_inst_1758_, lean_object* v_f_1759_, lean_object* v_t_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Std_TreeMap_Raw_forM(v_00_u03b1_1754_, v_00_u03b2_1755_, v_cmp_1756_, v_m_1757_, v_inst_1758_, v_f_1759_, v_t_1760_);
lean_dec_ref(v_cmp_1756_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg___lam__0(lean_object* v_f_1762_, lean_object* v_a_1763_, lean_object* v_b_1764_, lean_object* v_c_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_apply_3(v_f_1762_, v_a_1763_, v_b_1764_, v_c_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg___lam__1(lean_object* v_toPure_1767_, lean_object* v_____do__lift_1768_){
_start:
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v_____do__lift_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v_____do__lift_1768_);
v___x_1770_ = lean_apply_2(v_toPure_1767_, lean_box(0), v_a_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg(lean_object* v_inst_1771_, lean_object* v_f_1772_, lean_object* v_init_1773_, lean_object* v_t_1774_){
_start:
{
lean_object* v_toApplicative_1775_; lean_object* v_toBind_1776_; lean_object* v_toPure_1777_; lean_object* v___f_1778_; lean_object* v___x_1779_; lean_object* v___f_1780_; lean_object* v___x_1781_; 
v_toApplicative_1775_ = lean_ctor_get(v_inst_1771_, 0);
v_toBind_1776_ = lean_ctor_get(v_inst_1771_, 1);
lean_inc(v_toBind_1776_);
v_toPure_1777_ = lean_ctor_get(v_toApplicative_1775_, 1);
lean_inc(v_toPure_1777_);
v___f_1778_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1778_, 0, v_f_1772_);
v___x_1779_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1771_, v___f_1778_, v_init_1773_, v_t_1774_);
v___f_1780_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1780_, 0, v_toPure_1777_);
v___x_1781_ = lean_apply_4(v_toBind_1776_, lean_box(0), lean_box(0), v___x_1779_, v___f_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn(lean_object* v_00_u03b1_1782_, lean_object* v_00_u03b2_1783_, lean_object* v_cmp_1784_, lean_object* v_00_u03b4_1785_, lean_object* v_m_1786_, lean_object* v_inst_1787_, lean_object* v_f_1788_, lean_object* v_init_1789_, lean_object* v_t_1790_){
_start:
{
lean_object* v_toApplicative_1791_; lean_object* v_toBind_1792_; lean_object* v_toPure_1793_; lean_object* v___f_1794_; lean_object* v___x_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; 
v_toApplicative_1791_ = lean_ctor_get(v_inst_1787_, 0);
v_toBind_1792_ = lean_ctor_get(v_inst_1787_, 1);
lean_inc(v_toBind_1792_);
v_toPure_1793_ = lean_ctor_get(v_toApplicative_1791_, 1);
lean_inc(v_toPure_1793_);
v___f_1794_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1794_, 0, v_f_1788_);
v___x_1795_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1787_, v___f_1794_, v_init_1789_, v_t_1790_);
v___f_1796_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1796_, 0, v_toPure_1793_);
v___x_1797_ = lean_apply_4(v_toBind_1792_, lean_box(0), lean_box(0), v___x_1795_, v___f_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___boxed(lean_object* v_00_u03b1_1798_, lean_object* v_00_u03b2_1799_, lean_object* v_cmp_1800_, lean_object* v_00_u03b4_1801_, lean_object* v_m_1802_, lean_object* v_inst_1803_, lean_object* v_f_1804_, lean_object* v_init_1805_, lean_object* v_t_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Std_TreeMap_Raw_forIn(v_00_u03b1_1798_, v_00_u03b2_1799_, v_cmp_1800_, v_00_u03b4_1801_, v_m_1802_, v_inst_1803_, v_f_1804_, v_init_1805_, v_t_1806_);
lean_dec_ref(v_cmp_1800_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1808_, lean_object* v_x_1809_, lean_object* v_k_1810_, lean_object* v_v_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1812_, 0, v_k_1810_);
lean_ctor_set(v___x_1812_, 1, v_v_1811_);
v___x_1813_ = lean_apply_1(v_f_1808_, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_1814_, lean_object* v_t_1815_, lean_object* v_f_1816_){
_start:
{
lean_object* v___f_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___f_1817_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1817_, 0, v_f_1816_);
v___x_1818_ = lean_box(0);
v___x_1819_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1814_, v___f_1817_, v___x_1818_, v_t_1815_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg(lean_object* v_inst_1820_){
_start:
{
lean_object* v___f_1821_; 
v___f_1821_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1821_, 0, v_inst_1820_);
return v___f_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad(lean_object* v_00_u03b1_1822_, lean_object* v_00_u03b2_1823_, lean_object* v_cmp_1824_, lean_object* v_m_1825_, lean_object* v_inst_1826_){
_start:
{
lean_object* v___f_1827_; 
v___f_1827_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1827_, 0, v_inst_1826_);
return v___f_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_1828_, lean_object* v_00_u03b2_1829_, lean_object* v_cmp_1830_, lean_object* v_m_1831_, lean_object* v_inst_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Std_TreeMap_Raw_instForMProdOfMonad(v_00_u03b1_1828_, v_00_u03b2_1829_, v_cmp_1830_, v_m_1831_, v_inst_1832_);
lean_dec_ref(v_cmp_1830_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1834_, lean_object* v_a_1835_, lean_object* v_b_1836_, lean_object* v_c_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_a_1835_);
lean_ctor_set(v___x_1838_, 1, v_b_1836_);
v___x_1839_ = lean_apply_2(v_f_1834_, v___x_1838_, v_c_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1840_, lean_object* v_00_u03b2_1841_, lean_object* v_t_1842_, lean_object* v_init_1843_, lean_object* v_f_1844_){
_start:
{
lean_object* v_toApplicative_1845_; lean_object* v_toBind_1846_; lean_object* v_toPure_1847_; lean_object* v___f_1848_; lean_object* v___x_1849_; lean_object* v___f_1850_; lean_object* v___x_1851_; 
v_toApplicative_1845_ = lean_ctor_get(v_inst_1840_, 0);
v_toBind_1846_ = lean_ctor_get(v_inst_1840_, 1);
lean_inc(v_toBind_1846_);
v_toPure_1847_ = lean_ctor_get(v_toApplicative_1845_, 1);
lean_inc(v_toPure_1847_);
v___f_1848_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1848_, 0, v_f_1844_);
v___x_1849_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1840_, v___f_1848_, v_init_1843_, v_t_1842_);
v___f_1850_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1850_, 0, v_toPure_1847_);
v___x_1851_ = lean_apply_4(v_toBind_1846_, lean_box(0), lean_box(0), v___x_1849_, v___f_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg(lean_object* v_inst_1852_){
_start:
{
lean_object* v___f_1853_; 
v___f_1853_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1853_, 0, v_inst_1852_);
return v___f_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad(lean_object* v_00_u03b1_1854_, lean_object* v_00_u03b2_1855_, lean_object* v_cmp_1856_, lean_object* v_m_1857_, lean_object* v_inst_1858_){
_start:
{
lean_object* v___f_1859_; 
v___f_1859_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1859_, 0, v_inst_1858_);
return v___f_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1860_, lean_object* v_00_u03b2_1861_, lean_object* v_cmp_1862_, lean_object* v_m_1863_, lean_object* v_inst_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Std_TreeMap_Raw_instForInProdOfMonad(v_00_u03b1_1860_, v_00_u03b2_1861_, v_cmp_1862_, v_m_1863_, v_inst_1864_);
lean_dec_ref(v_cmp_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___lam__0(lean_object* v_p_1866_, lean_object* v___x_1867_, lean_object* v___x_1868_, lean_object* v_a_1869_, lean_object* v_b_1870_, lean_object* v_acc_1871_){
_start:
{
lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1872_ = lean_apply_2(v_p_1866_, v_a_1869_, v_b_1870_);
v___x_1873_ = lean_unbox(v___x_1872_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1867_);
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref(v___x_1867_);
v___x_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1872_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1868_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1878_, lean_object* v___x_1879_, lean_object* v___x_1880_, lean_object* v_a_1881_, lean_object* v_b_1882_, lean_object* v_acc_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Std_TreeMap_Raw_any___redArg___lam__0(v_p_1878_, v___x_1879_, v___x_1880_, v_a_1881_, v_b_1882_, v_acc_1883_);
lean_dec_ref(v_acc_1883_);
return v_res_1884_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_any___redArg(lean_object* v_t_1888_, lean_object* v_p_1889_){
_start:
{
lean_object* v___y_1891_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___x_1900_; lean_object* v_a_1901_; 
v___x_1896_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1897_ = lean_box(0);
v___x_1898_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1899_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1899_, 0, v_p_1889_);
lean_closure_set(v___f_1899_, 1, v___x_1898_);
lean_closure_set(v___f_1899_, 2, v___x_1897_);
v___x_1900_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1896_, v___f_1899_, v___x_1898_, v_t_1888_);
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___y_1891_ = v_a_1901_;
goto v___jp_1890_;
v___jp_1890_:
{
lean_object* v_fst_1892_; 
v_fst_1892_ = lean_ctor_get(v___y_1891_, 0);
lean_inc(v_fst_1892_);
lean_dec_ref(v___y_1891_);
if (lean_obj_tag(v_fst_1892_) == 0)
{
uint8_t v___x_1893_; 
v___x_1893_ = 0;
return v___x_1893_;
}
else
{
lean_object* v_val_1894_; uint8_t v___x_1895_; 
v_val_1894_ = lean_ctor_get(v_fst_1892_, 0);
lean_inc(v_val_1894_);
lean_dec_ref_known(v_fst_1892_, 1);
v___x_1895_ = lean_unbox(v_val_1894_);
lean_dec(v_val_1894_);
return v___x_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___boxed(lean_object* v_t_1902_, lean_object* v_p_1903_){
_start:
{
uint8_t v_res_1904_; lean_object* v_r_1905_; 
v_res_1904_ = l_Std_TreeMap_Raw_any___redArg(v_t_1902_, v_p_1903_);
v_r_1905_ = lean_box(v_res_1904_);
return v_r_1905_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_any(lean_object* v_00_u03b1_1906_, lean_object* v_00_u03b2_1907_, lean_object* v_cmp_1908_, lean_object* v_t_1909_, lean_object* v_p_1910_){
_start:
{
lean_object* v___y_1912_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___f_1920_; lean_object* v___x_1921_; lean_object* v_a_1922_; 
v___x_1917_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1918_ = lean_box(0);
v___x_1919_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1920_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1920_, 0, v_p_1910_);
lean_closure_set(v___f_1920_, 1, v___x_1919_);
lean_closure_set(v___f_1920_, 2, v___x_1918_);
v___x_1921_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1917_, v___f_1920_, v___x_1919_, v_t_1909_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
v___y_1912_ = v_a_1922_;
goto v___jp_1911_;
v___jp_1911_:
{
lean_object* v_fst_1913_; 
v_fst_1913_ = lean_ctor_get(v___y_1912_, 0);
lean_inc(v_fst_1913_);
lean_dec_ref(v___y_1912_);
if (lean_obj_tag(v_fst_1913_) == 0)
{
uint8_t v___x_1914_; 
v___x_1914_ = 0;
return v___x_1914_;
}
else
{
lean_object* v_val_1915_; uint8_t v___x_1916_; 
v_val_1915_ = lean_ctor_get(v_fst_1913_, 0);
lean_inc(v_val_1915_);
lean_dec_ref_known(v_fst_1913_, 1);
v___x_1916_ = lean_unbox(v_val_1915_);
lean_dec(v_val_1915_);
return v___x_1916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___boxed(lean_object* v_00_u03b1_1923_, lean_object* v_00_u03b2_1924_, lean_object* v_cmp_1925_, lean_object* v_t_1926_, lean_object* v_p_1927_){
_start:
{
uint8_t v_res_1928_; lean_object* v_r_1929_; 
v_res_1928_ = l_Std_TreeMap_Raw_any(v_00_u03b1_1923_, v_00_u03b2_1924_, v_cmp_1925_, v_t_1926_, v_p_1927_);
lean_dec_ref(v_cmp_1925_);
v_r_1929_ = lean_box(v_res_1928_);
return v_r_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___lam__0(lean_object* v_p_1930_, lean_object* v___x_1931_, lean_object* v___x_1932_, lean_object* v_a_1933_, lean_object* v_b_1934_, lean_object* v_acc_1935_){
_start:
{
lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1936_ = lean_apply_2(v_p_1930_, v_a_1933_, v_b_1934_);
v___x_1937_ = lean_unbox(v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_dec_ref(v___x_1932_);
v___x_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___x_1931_);
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
else
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1932_);
return v___x_1941_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1942_, lean_object* v___x_1943_, lean_object* v___x_1944_, lean_object* v_a_1945_, lean_object* v_b_1946_, lean_object* v_acc_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_TreeMap_Raw_all___redArg___lam__0(v_p_1942_, v___x_1943_, v___x_1944_, v_a_1945_, v_b_1946_, v_acc_1947_);
lean_dec_ref(v_acc_1947_);
return v_res_1948_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_all___redArg(lean_object* v_t_1949_, lean_object* v_p_1950_){
_start:
{
lean_object* v___y_1952_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___f_1960_; lean_object* v___x_1961_; lean_object* v_a_1962_; 
v___x_1957_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1958_ = lean_box(0);
v___x_1959_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1960_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1960_, 0, v_p_1950_);
lean_closure_set(v___f_1960_, 1, v___x_1958_);
lean_closure_set(v___f_1960_, 2, v___x_1959_);
v___x_1961_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1957_, v___f_1960_, v___x_1959_, v_t_1949_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___y_1952_ = v_a_1962_;
goto v___jp_1951_;
v___jp_1951_:
{
lean_object* v_fst_1953_; 
v_fst_1953_ = lean_ctor_get(v___y_1952_, 0);
lean_inc(v_fst_1953_);
lean_dec_ref(v___y_1952_);
if (lean_obj_tag(v_fst_1953_) == 0)
{
uint8_t v___x_1954_; 
v___x_1954_ = 1;
return v___x_1954_;
}
else
{
lean_object* v_val_1955_; uint8_t v___x_1956_; 
v_val_1955_ = lean_ctor_get(v_fst_1953_, 0);
lean_inc(v_val_1955_);
lean_dec_ref_known(v_fst_1953_, 1);
v___x_1956_ = lean_unbox(v_val_1955_);
lean_dec(v_val_1955_);
return v___x_1956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___boxed(lean_object* v_t_1963_, lean_object* v_p_1964_){
_start:
{
uint8_t v_res_1965_; lean_object* v_r_1966_; 
v_res_1965_ = l_Std_TreeMap_Raw_all___redArg(v_t_1963_, v_p_1964_);
v_r_1966_ = lean_box(v_res_1965_);
return v_r_1966_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_all(lean_object* v_00_u03b1_1967_, lean_object* v_00_u03b2_1968_, lean_object* v_cmp_1969_, lean_object* v_t_1970_, lean_object* v_p_1971_){
_start:
{
lean_object* v___y_1973_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___f_1981_; lean_object* v___x_1982_; lean_object* v_a_1983_; 
v___x_1978_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1979_ = lean_box(0);
v___x_1980_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1981_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1981_, 0, v_p_1971_);
lean_closure_set(v___f_1981_, 1, v___x_1979_);
lean_closure_set(v___f_1981_, 2, v___x_1980_);
v___x_1982_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1978_, v___f_1981_, v___x_1980_, v_t_1970_);
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___y_1973_ = v_a_1983_;
goto v___jp_1972_;
v___jp_1972_:
{
lean_object* v_fst_1974_; 
v_fst_1974_ = lean_ctor_get(v___y_1973_, 0);
lean_inc(v_fst_1974_);
lean_dec_ref(v___y_1973_);
if (lean_obj_tag(v_fst_1974_) == 0)
{
uint8_t v___x_1975_; 
v___x_1975_ = 1;
return v___x_1975_;
}
else
{
lean_object* v_val_1976_; uint8_t v___x_1977_; 
v_val_1976_ = lean_ctor_get(v_fst_1974_, 0);
lean_inc(v_val_1976_);
lean_dec_ref_known(v_fst_1974_, 1);
v___x_1977_ = lean_unbox(v_val_1976_);
lean_dec(v_val_1976_);
return v___x_1977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___boxed(lean_object* v_00_u03b1_1984_, lean_object* v_00_u03b2_1985_, lean_object* v_cmp_1986_, lean_object* v_t_1987_, lean_object* v_p_1988_){
_start:
{
uint8_t v_res_1989_; lean_object* v_r_1990_; 
v_res_1989_ = l_Std_TreeMap_Raw_all(v_00_u03b1_1984_, v_00_u03b2_1985_, v_cmp_1986_, v_t_1987_, v_p_1988_);
lean_dec_ref(v_cmp_1986_);
v_r_1990_ = lean_box(v_res_1989_);
return v_r_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg___lam__0(lean_object* v_x1_1991_, lean_object* v_x2_1992_, lean_object* v_x3_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1994_, 0, v_x1_1991_);
lean_ctor_set(v___x_1994_, 1, v_x3_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_x1_1995_, lean_object* v_x2_1996_, lean_object* v_x3_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Std_TreeMap_Raw_keys___redArg___lam__0(v_x1_1995_, v_x2_1996_, v_x3_1997_);
lean_dec(v_x2_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg(lean_object* v_t_2000_){
_start:
{
lean_object* v___f_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___f_2001_ = ((lean_object*)(l_Std_TreeMap_Raw_keys___redArg___closed__0));
v___x_2002_ = lean_box(0);
v___x_2003_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2004_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2003_, v___f_2001_, v___x_2002_, v_t_2000_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys(lean_object* v_00_u03b1_2005_, lean_object* v_00_u03b2_2006_, lean_object* v_cmp_2007_, lean_object* v_t_2008_){
_start:
{
lean_object* v___f_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___f_2009_ = ((lean_object*)(l_Std_TreeMap_Raw_keys___redArg___closed__0));
v___x_2010_ = lean_box(0);
v___x_2011_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2012_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2011_, v___f_2009_, v___x_2010_, v_t_2008_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___boxed(lean_object* v_00_u03b1_2013_, lean_object* v_00_u03b2_2014_, lean_object* v_cmp_2015_, lean_object* v_t_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Std_TreeMap_Raw_keys(v_00_u03b1_2013_, v_00_u03b2_2014_, v_cmp_2015_, v_t_2016_);
lean_dec_ref(v_cmp_2015_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg___lam__0(lean_object* v_l_2018_, lean_object* v_k_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_array_push(v_l_2018_, v_k_2019_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_l_2022_, lean_object* v_k_2023_, lean_object* v_x_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Std_TreeMap_Raw_keysArray___redArg___lam__0(v_l_2022_, v_k_2023_, v_x_2024_);
lean_dec(v_x_2024_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg(lean_object* v_t_2027_){
_start:
{
lean_object* v___f_2028_; lean_object* v___y_2030_; 
v___f_2028_ = ((lean_object*)(l_Std_TreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2027_) == 0)
{
lean_object* v_size_2033_; 
v_size_2033_ = lean_ctor_get(v_t_2027_, 0);
lean_inc(v_size_2033_);
v___y_2030_ = v_size_2033_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_unsigned_to_nat(0u);
v___y_2030_ = v___x_2034_;
goto v___jp_2029_;
}
v___jp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_mk_empty_array_with_capacity(v___y_2030_);
lean_dec(v___y_2030_);
v___x_2032_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2028_, v___x_2031_, v_t_2027_);
return v___x_2032_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray(lean_object* v_00_u03b1_2035_, lean_object* v_00_u03b2_2036_, lean_object* v_cmp_2037_, lean_object* v_t_2038_){
_start:
{
lean_object* v___f_2039_; lean_object* v___y_2041_; 
v___f_2039_ = ((lean_object*)(l_Std_TreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2038_) == 0)
{
lean_object* v_size_2044_; 
v_size_2044_ = lean_ctor_get(v_t_2038_, 0);
lean_inc(v_size_2044_);
v___y_2041_ = v_size_2044_;
goto v___jp_2040_;
}
else
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_unsigned_to_nat(0u);
v___y_2041_ = v___x_2045_;
goto v___jp_2040_;
}
v___jp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_mk_empty_array_with_capacity(v___y_2041_);
lean_dec(v___y_2041_);
v___x_2043_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2039_, v___x_2042_, v_t_2038_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___boxed(lean_object* v_00_u03b1_2046_, lean_object* v_00_u03b2_2047_, lean_object* v_cmp_2048_, lean_object* v_t_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Std_TreeMap_Raw_keysArray(v_00_u03b1_2046_, v_00_u03b2_2047_, v_cmp_2048_, v_t_2049_);
lean_dec_ref(v_cmp_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg___lam__0(lean_object* v_x1_2051_, lean_object* v_x2_2052_, lean_object* v_x3_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_x2_2052_);
lean_ctor_set(v___x_2054_, 1, v_x3_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg___lam__0___boxed(lean_object* v_x1_2055_, lean_object* v_x2_2056_, lean_object* v_x3_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Std_TreeMap_Raw_values___redArg___lam__0(v_x1_2055_, v_x2_2056_, v_x3_2057_);
lean_dec(v_x1_2055_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg(lean_object* v_t_2060_){
_start:
{
lean_object* v___f_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___f_2061_ = ((lean_object*)(l_Std_TreeMap_Raw_values___redArg___closed__0));
v___x_2062_ = lean_box(0);
v___x_2063_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2064_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2063_, v___f_2061_, v___x_2062_, v_t_2060_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values(lean_object* v_00_u03b1_2065_, lean_object* v_00_u03b2_2066_, lean_object* v_cmp_2067_, lean_object* v_t_2068_){
_start:
{
lean_object* v___f_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___f_2069_ = ((lean_object*)(l_Std_TreeMap_Raw_values___redArg___closed__0));
v___x_2070_ = lean_box(0);
v___x_2071_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2072_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2071_, v___f_2069_, v___x_2070_, v_t_2068_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___boxed(lean_object* v_00_u03b1_2073_, lean_object* v_00_u03b2_2074_, lean_object* v_cmp_2075_, lean_object* v_t_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Std_TreeMap_Raw_values(v_00_u03b1_2073_, v_00_u03b2_2074_, v_cmp_2075_, v_t_2076_);
lean_dec_ref(v_cmp_2075_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg___lam__0(lean_object* v_l_2078_, lean_object* v_x_2079_, lean_object* v_v_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_array_push(v_l_2078_, v_v_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2082_, lean_object* v_x_2083_, lean_object* v_v_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Std_TreeMap_Raw_valuesArray___redArg___lam__0(v_l_2082_, v_x_2083_, v_v_2084_);
lean_dec(v_x_2083_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg(lean_object* v_t_2087_){
_start:
{
lean_object* v___f_2088_; lean_object* v___y_2090_; 
v___f_2088_ = ((lean_object*)(l_Std_TreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2087_) == 0)
{
lean_object* v_size_2093_; 
v_size_2093_ = lean_ctor_get(v_t_2087_, 0);
lean_inc(v_size_2093_);
v___y_2090_ = v_size_2093_;
goto v___jp_2089_;
}
else
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_unsigned_to_nat(0u);
v___y_2090_ = v___x_2094_;
goto v___jp_2089_;
}
v___jp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_mk_empty_array_with_capacity(v___y_2090_);
lean_dec(v___y_2090_);
v___x_2092_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2088_, v___x_2091_, v_t_2087_);
return v___x_2092_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray(lean_object* v_00_u03b1_2095_, lean_object* v_00_u03b2_2096_, lean_object* v_cmp_2097_, lean_object* v_t_2098_){
_start:
{
lean_object* v___f_2099_; lean_object* v___y_2101_; 
v___f_2099_ = ((lean_object*)(l_Std_TreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2098_) == 0)
{
lean_object* v_size_2104_; 
v_size_2104_ = lean_ctor_get(v_t_2098_, 0);
lean_inc(v_size_2104_);
v___y_2101_ = v_size_2104_;
goto v___jp_2100_;
}
else
{
lean_object* v___x_2105_; 
v___x_2105_ = lean_unsigned_to_nat(0u);
v___y_2101_ = v___x_2105_;
goto v___jp_2100_;
}
v___jp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_mk_empty_array_with_capacity(v___y_2101_);
lean_dec(v___y_2101_);
v___x_2103_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2099_, v___x_2102_, v_t_2098_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___boxed(lean_object* v_00_u03b1_2106_, lean_object* v_00_u03b2_2107_, lean_object* v_cmp_2108_, lean_object* v_t_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Std_TreeMap_Raw_valuesArray(v_00_u03b1_2106_, v_00_u03b2_2107_, v_cmp_2108_, v_t_2109_);
lean_dec_ref(v_cmp_2108_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___redArg___lam__0(lean_object* v_x1_2111_, lean_object* v_x2_2112_, lean_object* v_x3_2113_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v_x1_2111_);
lean_ctor_set(v___x_2114_, 1, v_x2_2112_);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v_x3_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___redArg(lean_object* v_t_2117_){
_start:
{
lean_object* v___f_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___f_2118_ = ((lean_object*)(l_Std_TreeMap_Raw_toList___redArg___closed__0));
v___x_2119_ = lean_box(0);
v___x_2120_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2121_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2120_, v___f_2118_, v___x_2119_, v_t_2117_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList(lean_object* v_00_u03b1_2122_, lean_object* v_00_u03b2_2123_, lean_object* v_cmp_2124_, lean_object* v_t_2125_){
_start:
{
lean_object* v___f_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___f_2126_ = ((lean_object*)(l_Std_TreeMap_Raw_toList___redArg___closed__0));
v___x_2127_ = lean_box(0);
v___x_2128_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2129_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2128_, v___f_2126_, v___x_2127_, v_t_2125_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___boxed(lean_object* v_00_u03b1_2130_, lean_object* v_00_u03b2_2131_, lean_object* v_cmp_2132_, lean_object* v_t_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Std_TreeMap_Raw_toList(v_00_u03b1_2130_, v_00_u03b2_2131_, v_cmp_2132_, v_t_2133_);
lean_dec_ref(v_cmp_2132_);
return v_res_2134_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__25, &l_Std_TreeMap_Raw___auto__1___closed__25_once, _init_l_Std_TreeMap_Raw___auto__1___closed__25);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___redArg___lam__0(lean_object* v_cmp_2136_, lean_object* v_a_2137_, lean_object* v_x_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_fst_2140_; lean_object* v_snd_2141_; lean_object* v_r_2142_; lean_object* v___x_2143_; 
v_fst_2140_ = lean_ctor_get(v_a_2137_, 0);
lean_inc(v_fst_2140_);
v_snd_2141_ = lean_ctor_get(v_a_2137_, 1);
lean_inc(v_snd_2141_);
lean_dec_ref(v_a_2137_);
v_r_2142_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2136_, v_fst_2140_, v_snd_2141_, v___y_2139_);
v___x_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2143_, 0, v_r_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___redArg(lean_object* v_l_2144_, lean_object* v_cmp_2145_){
_start:
{
lean_object* v___f_2146_; lean_object* v___x_2147_; lean_object* v_r_2148_; lean_object* v___x_2149_; 
v___f_2146_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2146_, 0, v_cmp_2145_);
v___x_2147_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2148_ = lean_box(1);
v___x_2149_ = l_List_forIn_x27_loop___redArg(v___x_2147_, v___f_2146_, v_l_2144_, v_r_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___redArg___boxed(lean_object* v_l_2150_, lean_object* v_cmp_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Std_TreeMap_Raw_ofList___redArg(v_l_2150_, v_cmp_2151_);
lean_dec(v_l_2150_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList(lean_object* v_00_u03b1_2153_, lean_object* v_00_u03b2_2154_, lean_object* v_l_2155_, lean_object* v_cmp_2156_){
_start:
{
lean_object* v___f_2157_; lean_object* v___x_2158_; lean_object* v_r_2159_; lean_object* v___x_2160_; 
v___f_2157_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2157_, 0, v_cmp_2156_);
v___x_2158_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2159_ = lean_box(1);
v___x_2160_ = l_List_forIn_x27_loop___redArg(v___x_2158_, v___f_2157_, v_l_2155_, v_r_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___boxed(lean_object* v_00_u03b1_2161_, lean_object* v_00_u03b2_2162_, lean_object* v_l_2163_, lean_object* v_cmp_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Std_TreeMap_Raw_ofList(v_00_u03b1_2161_, v_00_u03b2_2162_, v_l_2163_, v_cmp_2164_);
lean_dec(v_l_2163_);
return v_res_2165_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__25, &l_Std_TreeMap_Raw___auto__1___closed__25_once, _init_l_Std_TreeMap_Raw___auto__1___closed__25);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg___lam__0(lean_object* v_cmp_2167_, lean_object* v_a_2168_, lean_object* v_x_2169_, lean_object* v___y_2170_){
_start:
{
uint8_t v___x_2171_; 
lean_inc(v___y_2170_);
lean_inc(v_a_2168_);
lean_inc_ref(v_cmp_2167_);
v___x_2171_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2167_, v_a_2168_, v___y_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = lean_box(0);
v___x_2173_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2167_, v_a_2168_, v___x_2172_, v___y_2170_);
v___x_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; 
lean_dec(v_a_2168_);
lean_dec_ref(v_cmp_2167_);
v___x_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2175_, 0, v___y_2170_);
return v___x_2175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg(lean_object* v_l_2176_, lean_object* v_cmp_2177_){
_start:
{
lean_object* v___f_2178_; lean_object* v___x_2179_; lean_object* v_r_2180_; lean_object* v___x_2181_; 
v___f_2178_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2178_, 0, v_cmp_2177_);
v___x_2179_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2180_ = lean_box(1);
v___x_2181_ = l_List_forIn_x27_loop___redArg(v___x_2179_, v___f_2178_, v_l_2176_, v_r_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg___boxed(lean_object* v_l_2182_, lean_object* v_cmp_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Std_TreeMap_Raw_unitOfList___redArg(v_l_2182_, v_cmp_2183_);
lean_dec(v_l_2182_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList(lean_object* v_00_u03b1_2185_, lean_object* v_l_2186_, lean_object* v_cmp_2187_){
_start:
{
lean_object* v___f_2188_; lean_object* v___x_2189_; lean_object* v_r_2190_; lean_object* v___x_2191_; 
v___f_2188_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2188_, 0, v_cmp_2187_);
v___x_2189_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2190_ = lean_box(1);
v___x_2191_ = l_List_forIn_x27_loop___redArg(v___x_2189_, v___f_2188_, v_l_2186_, v_r_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___boxed(lean_object* v_00_u03b1_2192_, lean_object* v_l_2193_, lean_object* v_cmp_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Std_TreeMap_Raw_unitOfList(v_00_u03b1_2192_, v_l_2193_, v_cmp_2194_);
lean_dec(v_l_2193_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___redArg___lam__0(lean_object* v_l_2196_, lean_object* v_k_2197_, lean_object* v_v_2198_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v_k_2197_);
lean_ctor_set(v___x_2199_, 1, v_v_2198_);
v___x_2200_ = lean_array_push(v_l_2196_, v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___redArg(lean_object* v_t_2202_){
_start:
{
lean_object* v___f_2203_; lean_object* v___y_2205_; 
v___f_2203_ = ((lean_object*)(l_Std_TreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2202_) == 0)
{
lean_object* v_size_2208_; 
v_size_2208_ = lean_ctor_get(v_t_2202_, 0);
lean_inc(v_size_2208_);
v___y_2205_ = v_size_2208_;
goto v___jp_2204_;
}
else
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_unsigned_to_nat(0u);
v___y_2205_ = v___x_2209_;
goto v___jp_2204_;
}
v___jp_2204_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = lean_mk_empty_array_with_capacity(v___y_2205_);
lean_dec(v___y_2205_);
v___x_2207_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2203_, v___x_2206_, v_t_2202_);
return v___x_2207_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray(lean_object* v_00_u03b1_2210_, lean_object* v_00_u03b2_2211_, lean_object* v_cmp_2212_, lean_object* v_t_2213_){
_start:
{
lean_object* v___f_2214_; lean_object* v___y_2216_; 
v___f_2214_ = ((lean_object*)(l_Std_TreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2213_) == 0)
{
lean_object* v_size_2219_; 
v_size_2219_ = lean_ctor_get(v_t_2213_, 0);
lean_inc(v_size_2219_);
v___y_2216_ = v_size_2219_;
goto v___jp_2215_;
}
else
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_unsigned_to_nat(0u);
v___y_2216_ = v___x_2220_;
goto v___jp_2215_;
}
v___jp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = lean_mk_empty_array_with_capacity(v___y_2216_);
lean_dec(v___y_2216_);
v___x_2218_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2214_, v___x_2217_, v_t_2213_);
return v___x_2218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___boxed(lean_object* v_00_u03b1_2221_, lean_object* v_00_u03b2_2222_, lean_object* v_cmp_2223_, lean_object* v_t_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Std_TreeMap_Raw_toArray(v_00_u03b1_2221_, v_00_u03b2_2222_, v_cmp_2223_, v_t_2224_);
lean_dec_ref(v_cmp_2223_);
return v_res_2225_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__25, &l_Std_TreeMap_Raw___auto__1___closed__25_once, _init_l_Std_TreeMap_Raw___auto__1___closed__25);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofArray___redArg(lean_object* v_a_2227_, lean_object* v_cmp_2228_){
_start:
{
lean_object* v___f_2229_; lean_object* v___x_2230_; lean_object* v_r_2231_; size_t v_sz_2232_; size_t v___x_2233_; lean_object* v___x_2234_; 
v___f_2229_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2229_, 0, v_cmp_2228_);
v___x_2230_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2231_ = lean_box(1);
v_sz_2232_ = lean_array_size(v_a_2227_);
v___x_2233_ = ((size_t)0ULL);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2230_, v_a_2227_, v___f_2229_, v_sz_2232_, v___x_2233_, v_r_2231_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofArray(lean_object* v_00_u03b1_2235_, lean_object* v_00_u03b2_2236_, lean_object* v_a_2237_, lean_object* v_cmp_2238_){
_start:
{
lean_object* v___f_2239_; lean_object* v___x_2240_; lean_object* v_r_2241_; size_t v_sz_2242_; size_t v___x_2243_; lean_object* v___x_2244_; 
v___f_2239_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2239_, 0, v_cmp_2238_);
v___x_2240_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2241_ = lean_box(1);
v_sz_2242_ = lean_array_size(v_a_2237_);
v___x_2243_ = ((size_t)0ULL);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2240_, v_a_2237_, v___f_2239_, v_sz_2242_, v___x_2243_, v_r_2241_);
return v___x_2244_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__25, &l_Std_TreeMap_Raw___auto__1___closed__25_once, _init_l_Std_TreeMap_Raw___auto__1___closed__25);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfArray___redArg(lean_object* v_a_2246_, lean_object* v_cmp_2247_){
_start:
{
lean_object* v___f_2248_; lean_object* v___x_2249_; lean_object* v_r_2250_; size_t v_sz_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
v___f_2248_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2248_, 0, v_cmp_2247_);
v___x_2249_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2250_ = lean_box(1);
v_sz_2251_ = lean_array_size(v_a_2246_);
v___x_2252_ = ((size_t)0ULL);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2249_, v_a_2246_, v___f_2248_, v_sz_2251_, v___x_2252_, v_r_2250_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfArray(lean_object* v_00_u03b1_2254_, lean_object* v_a_2255_, lean_object* v_cmp_2256_){
_start:
{
lean_object* v___f_2257_; lean_object* v___x_2258_; lean_object* v_r_2259_; size_t v_sz_2260_; size_t v___x_2261_; lean_object* v___x_2262_; 
v___f_2257_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2257_, 0, v_cmp_2256_);
v___x_2258_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2259_ = lean_box(1);
v_sz_2260_ = lean_array_size(v_a_2255_);
v___x_2261_ = ((size_t)0ULL);
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2258_, v_a_2255_, v___f_2257_, v_sz_2260_, v___x_2261_, v_r_2259_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_modify___redArg(lean_object* v_cmp_2263_, lean_object* v_t_2264_, lean_object* v_a_2265_, lean_object* v_f_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2263_, v_a_2265_, v_f_2266_, v_t_2264_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_modify(lean_object* v_00_u03b1_2268_, lean_object* v_00_u03b2_2269_, lean_object* v_cmp_2270_, lean_object* v_t_2271_, lean_object* v_a_2272_, lean_object* v_f_2273_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2270_, v_a_2272_, v_f_2273_, v_t_2271_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_alter___redArg(lean_object* v_cmp_2275_, lean_object* v_t_2276_, lean_object* v_a_2277_, lean_object* v_f_2278_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2275_, v_a_2277_, v_f_2278_, v_t_2276_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_alter(lean_object* v_00_u03b1_2280_, lean_object* v_00_u03b2_2281_, lean_object* v_cmp_2282_, lean_object* v_t_2283_, lean_object* v_a_2284_, lean_object* v_f_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2282_, v_a_2284_, v_f_2285_, v_t_2283_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2287_, lean_object* v_mergeFn_2288_, lean_object* v_a_2289_, lean_object* v_x_2290_){
_start:
{
if (lean_obj_tag(v_x_2290_) == 0)
{
lean_object* v___x_2291_; 
lean_dec(v_a_2289_);
lean_dec(v_mergeFn_2288_);
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v_b_u2082_2287_);
return v___x_2291_;
}
else
{
lean_object* v_val_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2300_; 
v_val_2292_ = lean_ctor_get(v_x_2290_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_x_2290_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2294_ = v_x_2290_;
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_val_2292_);
lean_dec(v_x_2290_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2296_ = lean_apply_3(v_mergeFn_2288_, v_a_2289_, v_val_2292_, v_b_u2082_2287_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2296_);
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2301_, lean_object* v_cmp_2302_, lean_object* v_t_2303_, lean_object* v_a_2304_, lean_object* v_b_u2082_2305_){
_start:
{
lean_object* v___f_2306_; lean_object* v___x_2307_; 
lean_inc(v_a_2304_);
v___f_2306_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2306_, 0, v_b_u2082_2305_);
lean_closure_set(v___f_2306_, 1, v_mergeFn_2301_);
lean_closure_set(v___f_2306_, 2, v_a_2304_);
v___x_2307_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2302_, v_a_2304_, v___f_2306_, v_t_2303_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg(lean_object* v_cmp_2308_, lean_object* v_mergeFn_2309_, lean_object* v_t_u2081_2310_, lean_object* v_t_u2082_2311_){
_start:
{
lean_object* v___f_2312_; lean_object* v___x_2313_; 
v___f_2312_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2312_, 0, v_mergeFn_2309_);
lean_closure_set(v___f_2312_, 1, v_cmp_2308_);
v___x_2313_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2312_, v_t_u2081_2310_, v_t_u2082_2311_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith(lean_object* v_00_u03b1_2314_, lean_object* v_00_u03b2_2315_, lean_object* v_cmp_2316_, lean_object* v_mergeFn_2317_, lean_object* v_t_u2081_2318_, lean_object* v_t_u2082_2319_){
_start:
{
lean_object* v___f_2320_; lean_object* v___x_2321_; 
v___f_2320_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2320_, 0, v_mergeFn_2317_);
lean_closure_set(v___f_2320_, 1, v_cmp_2316_);
v___x_2321_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2320_, v_t_u2081_2318_, v_t_u2082_2319_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_2322_, lean_object* v_x_2323_, lean_object* v_____s_2324_){
_start:
{
lean_object* v_fst_2325_; lean_object* v_snd_2326_; lean_object* v_r_2327_; lean_object* v___x_2328_; 
v_fst_2325_ = lean_ctor_get(v_x_2323_, 0);
lean_inc(v_fst_2325_);
v_snd_2326_ = lean_ctor_get(v_x_2323_, 1);
lean_inc(v_snd_2326_);
lean_dec_ref(v_x_2323_);
v_r_2327_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2322_, v_fst_2325_, v_snd_2326_, v_____s_2324_);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_r_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany___redArg(lean_object* v_cmp_2329_, lean_object* v_inst_2330_, lean_object* v_t_2331_, lean_object* v_l_2332_){
_start:
{
lean_object* v___f_2333_; lean_object* v___x_2334_; 
v___f_2333_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2333_, 0, v_cmp_2329_);
v___x_2334_ = lean_apply_4(v_inst_2330_, lean_box(0), v_l_2332_, v_t_2331_, v___f_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany(lean_object* v_00_u03b1_2335_, lean_object* v_00_u03b2_2336_, lean_object* v_cmp_2337_, lean_object* v_00_u03c1_2338_, lean_object* v_inst_2339_, lean_object* v_t_2340_, lean_object* v_l_2341_){
_start:
{
lean_object* v___f_2342_; lean_object* v___x_2343_; 
v___f_2342_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2342_, 0, v_cmp_2337_);
v___x_2343_ = lean_apply_4(v_inst_2339_, lean_box(0), v_l_2341_, v_t_2340_, v___f_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_union___redArg(lean_object* v_cmp_2344_, lean_object* v_t_u2081_2345_, lean_object* v_t_u2082_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_2344_, v_t_u2081_2345_, v_t_u2082_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_union(lean_object* v_00_u03b1_2348_, lean_object* v_00_u03b2_2349_, lean_object* v_cmp_2350_, lean_object* v_t_u2081_2351_, lean_object* v_t_u2082_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_2350_, v_t_u2081_2351_, v_t_u2082_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instUnion___redArg(lean_object* v_cmp_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_2355_, 0, lean_box(0));
lean_closure_set(v___x_2355_, 1, lean_box(0));
lean_closure_set(v___x_2355_, 2, v_cmp_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instUnion(lean_object* v_00_u03b1_2356_, lean_object* v_00_u03b2_2357_, lean_object* v_cmp_2358_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_2359_, 0, lean_box(0));
lean_closure_set(v___x_2359_, 1, lean_box(0));
lean_closure_set(v___x_2359_, 2, v_cmp_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_inter___redArg(lean_object* v_cmp_2360_, lean_object* v_t_u2081_2361_, lean_object* v_t_u2082_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_2360_, v_t_u2081_2361_, v_t_u2082_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_inter(lean_object* v_00_u03b1_2364_, lean_object* v_00_u03b2_2365_, lean_object* v_cmp_2366_, lean_object* v_t_u2081_2367_, lean_object* v_t_u2082_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_2366_, v_t_u2081_2367_, v_t_u2082_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInter___redArg(lean_object* v_cmp_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_2371_, 0, lean_box(0));
lean_closure_set(v___x_2371_, 1, lean_box(0));
lean_closure_set(v___x_2371_, 2, v_cmp_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInter(lean_object* v_00_u03b1_2372_, lean_object* v_00_u03b2_2373_, lean_object* v_cmp_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_2375_, 0, lean_box(0));
lean_closure_set(v___x_2375_, 1, lean_box(0));
lean_closure_set(v___x_2375_, 2, v_cmp_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___redArg(lean_object* v_cmp_2376_, lean_object* v_inst_2377_, lean_object* v_t_u2081_2378_, lean_object* v_t_u2082_2379_){
_start:
{
uint8_t v___x_2380_; 
v___x_2380_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2376_, v_inst_2377_, v_t_u2081_2378_, v_t_u2082_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___redArg___boxed(lean_object* v_cmp_2381_, lean_object* v_inst_2382_, lean_object* v_t_u2081_2383_, lean_object* v_t_u2082_2384_){
_start:
{
uint8_t v_res_2385_; lean_object* v_r_2386_; 
v_res_2385_ = l_Std_TreeMap_Raw_beq___redArg(v_cmp_2381_, v_inst_2382_, v_t_u2081_2383_, v_t_u2082_2384_);
v_r_2386_ = lean_box(v_res_2385_);
return v_r_2386_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq(lean_object* v_00_u03b1_2387_, lean_object* v_00_u03b2_2388_, lean_object* v_cmp_2389_, lean_object* v_inst_2390_, lean_object* v_t_u2081_2391_, lean_object* v_t_u2082_2392_){
_start:
{
uint8_t v___x_2393_; 
v___x_2393_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2389_, v_inst_2390_, v_t_u2081_2391_, v_t_u2082_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___boxed(lean_object* v_00_u03b1_2394_, lean_object* v_00_u03b2_2395_, lean_object* v_cmp_2396_, lean_object* v_inst_2397_, lean_object* v_t_u2081_2398_, lean_object* v_t_u2082_2399_){
_start:
{
uint8_t v_res_2400_; lean_object* v_r_2401_; 
v_res_2400_ = l_Std_TreeMap_Raw_beq(v_00_u03b1_2394_, v_00_u03b2_2395_, v_cmp_2396_, v_inst_2397_, v_t_u2081_2398_, v_t_u2082_2399_);
v_r_2401_ = lean_box(v_res_2400_);
return v_r_2401_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instBEq___redArg(lean_object* v_cmp_2402_, lean_object* v_inst_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_beq___boxed), 6, 4);
lean_closure_set(v___x_2404_, 0, lean_box(0));
lean_closure_set(v___x_2404_, 1, lean_box(0));
lean_closure_set(v___x_2404_, 2, v_cmp_2402_);
lean_closure_set(v___x_2404_, 3, v_inst_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instBEq(lean_object* v_00_u03b1_2405_, lean_object* v_00_u03b2_2406_, lean_object* v_cmp_2407_, lean_object* v_inst_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_beq___boxed), 6, 4);
lean_closure_set(v___x_2409_, 0, lean_box(0));
lean_closure_set(v___x_2409_, 1, lean_box(0));
lean_closure_set(v___x_2409_, 2, v_cmp_2407_);
lean_closure_set(v___x_2409_, 3, v_inst_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_diff___redArg(lean_object* v_cmp_2410_, lean_object* v_t_u2081_2411_, lean_object* v_t_u2082_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_2410_, v_t_u2081_2411_, v_t_u2082_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_diff(lean_object* v_00_u03b1_2414_, lean_object* v_00_u03b2_2415_, lean_object* v_cmp_2416_, lean_object* v_t_u2081_2417_, lean_object* v_t_u2082_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_2416_, v_t_u2081_2417_, v_t_u2082_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSDiff___redArg(lean_object* v_cmp_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_2421_, 0, lean_box(0));
lean_closure_set(v___x_2421_, 1, lean_box(0));
lean_closure_set(v___x_2421_, 2, v_cmp_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSDiff(lean_object* v_00_u03b1_2422_, lean_object* v_00_u03b2_2423_, lean_object* v_cmp_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_2425_, 0, lean_box(0));
lean_closure_set(v___x_2425_, 1, lean_box(0));
lean_closure_set(v___x_2425_, 2, v_cmp_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_2426_, lean_object* v_a_2427_, lean_object* v_____s_2428_){
_start:
{
uint8_t v___x_2429_; 
lean_inc(v_____s_2428_);
lean_inc(v_a_2427_);
lean_inc_ref(v_cmp_2426_);
v___x_2429_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2426_, v_a_2427_, v_____s_2428_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2430_ = lean_box(0);
v___x_2431_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2426_, v_a_2427_, v___x_2430_, v_____s_2428_);
v___x_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
return v___x_2432_;
}
else
{
lean_object* v___x_2433_; 
lean_dec(v_a_2427_);
lean_dec_ref(v_cmp_2426_);
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_____s_2428_);
return v___x_2433_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg(lean_object* v_cmp_2434_, lean_object* v_inst_2435_, lean_object* v_t_2436_, lean_object* v_l_2437_){
_start:
{
lean_object* v___f_2438_; lean_object* v___x_2439_; 
v___f_2438_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2438_, 0, v_cmp_2434_);
v___x_2439_ = lean_apply_4(v_inst_2435_, lean_box(0), v_l_2437_, v_t_2436_, v___f_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit(lean_object* v_00_u03b1_2440_, lean_object* v_cmp_2441_, lean_object* v_00_u03c1_2442_, lean_object* v_inst_2443_, lean_object* v_t_2444_, lean_object* v_l_2445_){
_start:
{
lean_object* v___f_2446_; lean_object* v___x_2447_; 
v___f_2446_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2446_, 0, v_cmp_2441_);
v___x_2447_ = lean_apply_4(v_inst_2443_, lean_box(0), v_l_2445_, v_t_2444_, v___f_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_2448_, lean_object* v_a_2449_, lean_object* v_____s_2450_){
_start:
{
lean_object* v_r_2451_; lean_object* v___x_2452_; 
v_r_2451_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_2448_, v_a_2449_, v_____s_2450_);
v___x_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2452_, 0, v_r_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany___redArg(lean_object* v_cmp_2453_, lean_object* v_inst_2454_, lean_object* v_t_2455_, lean_object* v_l_2456_){
_start:
{
lean_object* v___f_2457_; lean_object* v___x_2458_; 
v___f_2457_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2457_, 0, v_cmp_2453_);
v___x_2458_ = lean_apply_4(v_inst_2454_, lean_box(0), v_l_2456_, v_t_2455_, v___f_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany(lean_object* v_00_u03b1_2459_, lean_object* v_00_u03b2_2460_, lean_object* v_cmp_2461_, lean_object* v_00_u03c1_2462_, lean_object* v_inst_2463_, lean_object* v_t_2464_, lean_object* v_l_2465_){
_start:
{
lean_object* v___f_2466_; lean_object* v___x_2467_; 
v___f_2466_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2466_, 0, v_cmp_2461_);
v___x_2467_ = lean_apply_4(v_inst_2463_, lean_box(0), v_l_2465_, v_t_2464_, v___f_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg___lam__1(lean_object* v___f_2471_, lean_object* v___x_2472_, lean_object* v_m_2473_, lean_object* v_prec_2474_){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2475_ = ((lean_object*)(l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__1));
v___x_2476_ = lean_box(0);
v___x_2477_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2478_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2477_, v___f_2471_, v___x_2476_, v_m_2473_);
v___x_2479_ = l_List_repr___redArg(v___x_2472_, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2475_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = l_Repr_addAppParen(v___x_2480_, v_prec_2474_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_2482_, lean_object* v___x_2483_, lean_object* v_m_2484_, lean_object* v_prec_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Std_TreeMap_Raw_instRepr___redArg___lam__1(v___f_2482_, v___x_2483_, v_m_2484_, v_prec_2485_);
lean_dec(v_prec_2485_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg(lean_object* v_inst_2487_, lean_object* v_inst_2488_){
_start:
{
lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; lean_object* v___f_2492_; 
v___f_2489_ = ((lean_object*)(l_Std_TreeMap_Raw_toList___redArg___closed__0));
v___f_2490_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2490_, 0, v_inst_2488_);
v___x_2491_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2491_, 0, lean_box(0));
lean_closure_set(v___x_2491_, 1, lean_box(0));
lean_closure_set(v___x_2491_, 2, v_inst_2487_);
lean_closure_set(v___x_2491_, 3, v___f_2490_);
v___f_2492_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2492_, 0, v___f_2489_);
lean_closure_set(v___f_2492_, 1, v___x_2491_);
return v___f_2492_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr(lean_object* v_00_u03b1_2493_, lean_object* v_00_u03b2_2494_, lean_object* v_cmp_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Std_TreeMap_Raw_instRepr___redArg(v_inst_2496_, v_inst_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___boxed(lean_object* v_00_u03b1_2499_, lean_object* v_00_u03b2_2500_, lean_object* v_cmp_2501_, lean_object* v_inst_2502_, lean_object* v_inst_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Std_TreeMap_Raw_instRepr(v_00_u03b1_2499_, v_00_u03b2_2500_, v_cmp_2501_, v_inst_2502_, v_inst_2503_);
lean_dec_ref(v_cmp_2501_);
return v_res_2504_;
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
