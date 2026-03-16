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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__15;
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__16;
static const lean_ctor_object l_Std_TreeMap_Raw___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
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
static lean_once_cell_t l_Std_TreeMap_Raw___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__14));
v___x_34_ = lean_string_utf8_byte_size(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__16(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__15, &l_Std_TreeMap_Raw___auto__1___closed__15_once, _init_l_Std_TreeMap_Raw___auto__1___closed__15);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__14));
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_box(0);
v___x_42_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__17));
v___x_43_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__16, &l_Std_TreeMap_Raw___auto__1___closed__16_once, _init_l_Std_TreeMap_Raw___auto__1___closed__16);
v___x_44_ = lean_box(2);
v___x_45_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
lean_ctor_set(v___x_45_, 2, v___x_42_);
lean_ctor_set(v___x_45_, 3, v___x_41_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__18, &l_Std_TreeMap_Raw___auto__1___closed__18_once, _init_l_Std_TreeMap_Raw___auto__1___closed__18);
v___x_47_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__13, &l_Std_TreeMap_Raw___auto__1___closed__13_once, _init_l_Std_TreeMap_Raw___auto__1___closed__13);
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__19, &l_Std_TreeMap_Raw___auto__1___closed__19_once, _init_l_Std_TreeMap_Raw___auto__1___closed__19);
v___x_50_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__11));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__21(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__20, &l_Std_TreeMap_Raw___auto__1___closed__20_once, _init_l_Std_TreeMap_Raw___auto__1___closed__20);
v___x_54_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__5));
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__22(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__21, &l_Std_TreeMap_Raw___auto__1___closed__21_once, _init_l_Std_TreeMap_Raw___auto__1___closed__21);
v___x_57_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__9));
v___x_58_ = lean_box(2);
v___x_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__23(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__22, &l_Std_TreeMap_Raw___auto__1___closed__22_once, _init_l_Std_TreeMap_Raw___auto__1___closed__22);
v___x_61_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__24(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__23, &l_Std_TreeMap_Raw___auto__1___closed__23_once, _init_l_Std_TreeMap_Raw___auto__1___closed__23);
v___x_64_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__7));
v___x_65_ = lean_box(2);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__25(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__24, &l_Std_TreeMap_Raw___auto__1___closed__24_once, _init_l_Std_TreeMap_Raw___auto__1___closed__24);
v___x_68_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__5));
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1___closed__26(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__25, &l_Std_TreeMap_Raw___auto__1___closed__25_once, _init_l_Std_TreeMap_Raw___auto__1___closed__25);
v___x_71_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__4));
v___x_72_ = lean_box(2);
v___x_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___auto__1(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__26, &l_Std_TreeMap_Raw___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw___auto__1___closed__26);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_cmp_77_, lean_object* v_t_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_box(0);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instCoeWFWFInner___boxed(lean_object* v_00_u03b1_80_, lean_object* v_00_u03b2_81_, lean_object* v_cmp_82_, lean_object* v_t_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_TreeMap_Raw_instCoeWFWFInner(v_00_u03b1_80_, v_00_u03b2_81_, v_cmp_82_, v_t_83_);
lean_dec(v_t_83_);
lean_dec_ref(v_cmp_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_cmp_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(1);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_empty___boxed(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_cmp_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_TreeMap_Raw_empty(v_00_u03b1_89_, v_00_u03b2_90_, v_cmp_91_);
lean_dec_ref(v_cmp_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_cmp_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instEmptyCollection___boxed(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_cmp_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_TreeMap_Raw_instEmptyCollection(v_00_u03b1_97_, v_00_u03b2_98_, v_cmp_99_);
lean_dec_ref(v_cmp_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_cmp_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(1);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInhabited___boxed(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_cmp_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_TreeMap_Raw_instInhabited(v_00_u03b1_105_, v_00_u03b2_106_, v_cmp_107_);
lean_dec_ref(v_cmp_107_);
return v_res_108_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3));
v___x_149_ = l_String_toRawSubstring_x27(v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1(lean_object* v_x_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l_Std_TreeMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_168_);
v___x_172_ = l_Lean_Syntax_isOfKind(v_x_168_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec_ref(v_a_169_);
lean_dec(v_x_168_);
v___x_173_ = lean_box(1);
v___x_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_a_170_);
return v___x_174_;
}
else
{
lean_object* v_quotContext_175_; lean_object* v_currMacroScope_176_; lean_object* v_ref_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_quotContext_175_ = lean_ctor_get(v_a_169_, 1);
lean_inc(v_quotContext_175_);
v_currMacroScope_176_ = lean_ctor_get(v_a_169_, 2);
lean_inc(v_currMacroScope_176_);
v_ref_177_ = lean_ctor_get(v_a_169_, 5);
lean_inc(v_ref_177_);
lean_dec_ref(v_a_169_);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = l_Lean_Syntax_getArg(v_x_168_, v___x_178_);
v___x_180_ = lean_unsigned_to_nat(2u);
v___x_181_ = l_Lean_Syntax_getArg(v_x_168_, v___x_180_);
lean_dec(v_x_168_);
v___x_182_ = 0;
v___x_183_ = l_Lean_SourceInfo_fromRef(v_ref_177_, v___x_182_);
lean_dec(v_ref_177_);
v___x_184_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2));
v___x_185_ = lean_obj_once(&l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4, &l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4_once, _init_l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4);
v___x_186_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__5));
v___x_187_ = l_Lean_addMacroScope(v_quotContext_175_, v___x_186_, v_currMacroScope_176_);
v___x_188_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__10));
lean_inc(v___x_183_);
v___x_189_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_189_, 0, v___x_183_);
lean_ctor_set(v___x_189_, 1, v___x_185_);
lean_ctor_set(v___x_189_, 2, v___x_187_);
lean_ctor_set(v___x_189_, 3, v___x_188_);
v___x_190_ = ((lean_object*)(l_Std_TreeMap_Raw___auto__1___closed__9));
lean_inc(v___x_183_);
v___x_191_ = l_Lean_Syntax_node2(v___x_183_, v___x_190_, v___x_179_, v___x_181_);
v___x_192_ = l_Lean_Syntax_node2(v___x_183_, v___x_184_, v___x_189_, v___x_191_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v_a_170_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1(lean_object* v_x_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2));
lean_inc(v_x_197_);
v___x_201_ = l_Lean_Syntax_isOfKind(v_x_197_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_x_197_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_a_199_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = l_Lean_Syntax_getArg(v_x_197_, v___x_204_);
v___x_206_ = ((lean_object*)(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_205_);
v___x_207_ = l_Lean_Syntax_isOfKind(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v___x_205_);
lean_dec(v_x_197_);
v___x_208_ = lean_box(0);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v_a_199_);
return v___x_209_;
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = l_Lean_Syntax_getArg(v_x_197_, v___x_210_);
lean_dec(v_x_197_);
v___x_212_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_211_);
v___x_213_ = l_Lean_Syntax_matchesNull(v___x_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v___x_211_);
lean_dec(v___x_205_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v_a_199_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_ref_218_; uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_216_ = l_Lean_Syntax_getArg(v___x_211_, v___x_204_);
v___x_217_ = l_Lean_Syntax_getArg(v___x_211_, v___x_210_);
lean_dec(v___x_211_);
v_ref_218_ = l_Lean_replaceRef(v___x_205_, v_a_198_);
lean_dec(v___x_205_);
v___x_219_ = 0;
v___x_220_ = l_Lean_SourceInfo_fromRef(v_ref_218_, v___x_219_);
lean_dec(v_ref_218_);
v___x_221_ = ((lean_object*)(l_Std_TreeMap_Raw_term___x7em___00__closed__4));
v___x_222_ = ((lean_object*)(l_Std_TreeMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_220_);
v___x_223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_220_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = l_Lean_Syntax_node3(v___x_220_, v___x_221_, v___x_216_, v___x_223_, v___x_217_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v_a_199_);
return v___x_225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___boxed(lean_object* v_x_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1(v_x_226_, v_a_227_, v_a_228_);
lean_dec(v_a_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insert___redArg(lean_object* v_cmp_230_, lean_object* v_l_231_, lean_object* v_a_232_, lean_object* v_b_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_230_, v_a_232_, v_b_233_, v_l_231_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insert(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_cmp_237_, lean_object* v_l_238_, lean_object* v_a_239_, lean_object* v_b_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_237_, v_a_239_, v_b_240_, v_l_238_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0(lean_object* v_cmp_242_, lean_object* v_e_243_){
_start:
{
lean_object* v_fst_244_; lean_object* v_snd_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_fst_244_ = lean_ctor_get(v_e_243_, 0);
lean_inc(v_fst_244_);
v_snd_245_ = lean_ctor_get(v_e_243_, 1);
lean_inc(v_snd_245_);
lean_dec_ref(v_e_243_);
v___x_246_ = lean_box(1);
v___x_247_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_242_, v_fst_244_, v_snd_245_, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd___redArg(lean_object* v_cmp_248_){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0), 2, 1);
lean_closure_set(v___f_249_, 0, v_cmp_248_);
return v___f_249_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSingletonProd(lean_object* v_00_u03b1_250_, lean_object* v_00_u03b2_251_, lean_object* v_cmp_252_){
_start:
{
lean_object* v___f_253_; 
v___f_253_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0), 2, 1);
lean_closure_set(v___f_253_, 0, v_cmp_252_);
return v___f_253_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0(lean_object* v_cmp_254_, lean_object* v_e_255_, lean_object* v_s_256_){
_start:
{
lean_object* v_fst_257_; lean_object* v_snd_258_; lean_object* v___x_259_; 
v_fst_257_ = lean_ctor_get(v_e_255_, 0);
lean_inc(v_fst_257_);
v_snd_258_ = lean_ctor_get(v_e_255_, 1);
lean_inc(v_snd_258_);
lean_dec_ref(v_e_255_);
v___x_259_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_254_, v_fst_257_, v_snd_258_, v_s_256_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd___redArg(lean_object* v_cmp_260_){
_start:
{
lean_object* v___f_261_; 
v___f_261_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_261_, 0, v_cmp_260_);
return v___f_261_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInsertProd(lean_object* v_00_u03b1_262_, lean_object* v_00_u03b2_263_, lean_object* v_cmp_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_265_, 0, v_cmp_264_);
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertIfNew___redArg(lean_object* v_cmp_266_, lean_object* v_t_267_, lean_object* v_a_268_, lean_object* v_b_269_){
_start:
{
uint8_t v___x_270_; 
lean_inc(v_t_267_);
lean_inc(v_a_268_);
lean_inc_ref(v_cmp_266_);
v___x_270_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_266_, v_a_268_, v_t_267_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_266_, v_a_268_, v_b_269_, v_t_267_);
return v___x_271_;
}
else
{
lean_dec(v_b_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_cmp_266_);
return v_t_267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertIfNew(lean_object* v_00_u03b1_272_, lean_object* v_00_u03b2_273_, lean_object* v_cmp_274_, lean_object* v_t_275_, lean_object* v_a_276_, lean_object* v_b_277_){
_start:
{
uint8_t v___x_278_; 
lean_inc(v_t_275_);
lean_inc(v_a_276_);
lean_inc_ref(v_cmp_274_);
v___x_278_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_274_, v_a_276_, v_t_275_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_274_, v_a_276_, v_b_277_, v_t_275_);
return v___x_279_;
}
else
{
lean_dec(v_b_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_cmp_274_);
return v_t_275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsert___redArg(lean_object* v_cmp_280_, lean_object* v_t_281_, lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
lean_object* v_sz_284_; lean_object* v_m_285_; lean_object* v___y_287_; 
v_sz_284_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_281_);
v_m_285_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_280_, v_a_282_, v_b_283_, v_t_281_);
if (lean_obj_tag(v_m_285_) == 0)
{
lean_object* v_size_291_; 
v_size_291_ = lean_ctor_get(v_m_285_, 0);
lean_inc(v_size_291_);
v___y_287_ = v_size_291_;
goto v___jp_286_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___y_287_ = v___x_292_;
goto v___jp_286_;
}
v___jp_286_:
{
uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_nat_dec_eq(v_sz_284_, v___y_287_);
lean_dec(v___y_287_);
lean_dec(v_sz_284_);
v___x_289_ = lean_box(v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_m_285_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsert(lean_object* v_00_u03b1_293_, lean_object* v_00_u03b2_294_, lean_object* v_cmp_295_, lean_object* v_t_296_, lean_object* v_a_297_, lean_object* v_b_298_){
_start:
{
lean_object* v_sz_299_; lean_object* v_m_300_; lean_object* v___y_302_; 
v_sz_299_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_296_);
v_m_300_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_295_, v_a_297_, v_b_298_, v_t_296_);
if (lean_obj_tag(v_m_300_) == 0)
{
lean_object* v_size_306_; 
v_size_306_ = lean_ctor_get(v_m_300_, 0);
lean_inc(v_size_306_);
v___y_302_ = v_size_306_;
goto v___jp_301_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___y_302_ = v___x_307_;
goto v___jp_301_;
}
v___jp_301_:
{
uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_nat_dec_eq(v_sz_299_, v___y_302_);
lean_dec(v___y_302_);
lean_dec(v_sz_299_);
v___x_304_ = lean_box(v___x_303_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v_m_300_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_cmp_308_, lean_object* v_t_309_, lean_object* v_a_310_, lean_object* v_b_311_){
_start:
{
uint8_t v___x_312_; 
lean_inc(v_t_309_);
lean_inc(v_a_310_);
lean_inc_ref(v_cmp_308_);
v___x_312_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_308_, v_a_310_, v_t_309_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_308_, v_a_310_, v_b_311_, v_t_309_);
v___x_314_ = lean_box(v___x_312_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_b_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_cmp_308_);
v___x_316_ = lean_box(v___x_312_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_t_309_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_318_, lean_object* v_00_u03b2_319_, lean_object* v_cmp_320_, lean_object* v_t_321_, lean_object* v_a_322_, lean_object* v_b_323_){
_start:
{
uint8_t v___x_324_; 
lean_inc(v_t_321_);
lean_inc(v_a_322_);
lean_inc_ref(v_cmp_320_);
v___x_324_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_320_, v_a_322_, v_t_321_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_320_, v_a_322_, v_b_323_, v_t_321_);
v___x_326_ = lean_box(v___x_324_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_b_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_cmp_320_);
v___x_328_ = lean_box(v___x_324_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_t_321_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_330_, lean_object* v_t_331_, lean_object* v_a_332_, lean_object* v_b_333_){
_start:
{
lean_object* v___x_334_; 
lean_inc(v_a_332_);
lean_inc(v_t_331_);
lean_inc_ref(v_cmp_330_);
v___x_334_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_330_, v_t_331_, v_a_332_);
if (lean_obj_tag(v___x_334_) == 0)
{
uint8_t v___x_335_; 
lean_inc(v_t_331_);
lean_inc(v_a_332_);
lean_inc_ref(v_cmp_330_);
v___x_335_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_330_, v_a_332_, v_t_331_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_330_, v_a_332_, v_b_333_, v_t_331_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_334_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
return v___x_337_;
}
else
{
lean_object* v___x_338_; 
lean_dec(v_b_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_cmp_330_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_334_);
lean_ctor_set(v___x_338_, 1, v_t_331_);
return v___x_338_;
}
}
else
{
lean_object* v___x_339_; 
lean_dec(v_b_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_cmp_330_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_334_);
lean_ctor_set(v___x_339_, 1, v_t_331_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_340_, lean_object* v_00_u03b2_341_, lean_object* v_cmp_342_, lean_object* v_t_343_, lean_object* v_a_344_, lean_object* v_b_345_){
_start:
{
lean_object* v___x_346_; 
lean_inc(v_a_344_);
lean_inc(v_t_343_);
lean_inc_ref(v_cmp_342_);
v___x_346_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_342_, v_t_343_, v_a_344_);
if (lean_obj_tag(v___x_346_) == 0)
{
uint8_t v___x_347_; 
lean_inc(v_t_343_);
lean_inc(v_a_344_);
lean_inc_ref(v_cmp_342_);
v___x_347_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_342_, v_a_344_, v_t_343_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_342_, v_a_344_, v_b_345_, v_t_343_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_346_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; 
lean_dec(v_b_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_cmp_342_);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_346_);
lean_ctor_set(v___x_350_, 1, v_t_343_);
return v___x_350_;
}
}
else
{
lean_object* v___x_351_; 
lean_dec(v_b_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_cmp_342_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_346_);
lean_ctor_set(v___x_351_, 1, v_t_343_);
return v___x_351_;
}
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_contains___redArg(lean_object* v_cmp_352_, lean_object* v_l_353_, lean_object* v_a_354_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_352_, v_a_354_, v_l_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_contains___redArg___boxed(lean_object* v_cmp_356_, lean_object* v_l_357_, lean_object* v_a_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Std_TreeMap_Raw_contains___redArg(v_cmp_356_, v_l_357_, v_a_358_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_contains(lean_object* v_00_u03b1_361_, lean_object* v_00_u03b2_362_, lean_object* v_cmp_363_, lean_object* v_l_364_, lean_object* v_a_365_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_363_, v_a_365_, v_l_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_contains___boxed(lean_object* v_00_u03b1_367_, lean_object* v_00_u03b2_368_, lean_object* v_cmp_369_, lean_object* v_l_370_, lean_object* v_a_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Std_TreeMap_Raw_contains(v_00_u03b1_367_, v_00_u03b2_368_, v_cmp_369_, v_l_370_, v_a_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_cmp_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instMembership___boxed(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_cmp_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_TreeMap_Raw_instMembership(v_00_u03b1_378_, v_00_u03b2_379_, v_cmp_380_);
lean_dec_ref(v_cmp_380_);
return v_res_381_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_instDecidableMem___redArg(lean_object* v_cmp_382_, lean_object* v_t_383_, lean_object* v_a_384_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_382_, v_a_384_, v_t_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_386_, lean_object* v_t_387_, lean_object* v_a_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Std_TreeMap_Raw_instDecidableMem___redArg(v_cmp_386_, v_t_387_, v_a_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_instDecidableMem(lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_cmp_393_, lean_object* v_t_394_, lean_object* v_a_395_){
_start:
{
uint8_t v___x_396_; 
v___x_396_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_393_, v_a_395_, v_t_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_397_, lean_object* v_00_u03b2_398_, lean_object* v_cmp_399_, lean_object* v_t_400_, lean_object* v_a_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Std_TreeMap_Raw_instDecidableMem(v_00_u03b1_397_, v_00_u03b2_398_, v_cmp_399_, v_t_400_, v_a_401_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___redArg(lean_object* v_t_404_){
_start:
{
if (lean_obj_tag(v_t_404_) == 0)
{
lean_object* v_size_405_; 
v_size_405_ = lean_ctor_get(v_t_404_, 0);
lean_inc(v_size_405_);
return v_size_405_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_unsigned_to_nat(0u);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___redArg___boxed(lean_object* v_t_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_TreeMap_Raw_size___redArg(v_t_407_);
lean_dec(v_t_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size(lean_object* v_00_u03b1_409_, lean_object* v_00_u03b2_410_, lean_object* v_cmp_411_, lean_object* v_t_412_){
_start:
{
if (lean_obj_tag(v_t_412_) == 0)
{
lean_object* v_size_413_; 
v_size_413_ = lean_ctor_get(v_t_412_, 0);
lean_inc(v_size_413_);
return v_size_413_;
}
else
{
lean_object* v___x_414_; 
v___x_414_ = lean_unsigned_to_nat(0u);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_size___boxed(lean_object* v_00_u03b1_415_, lean_object* v_00_u03b2_416_, lean_object* v_cmp_417_, lean_object* v_t_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_TreeMap_Raw_size(v_00_u03b1_415_, v_00_u03b2_416_, v_cmp_417_, v_t_418_);
lean_dec(v_t_418_);
lean_dec_ref(v_cmp_417_);
return v_res_419_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_isEmpty___redArg(lean_object* v_t_420_){
_start:
{
if (lean_obj_tag(v_t_420_) == 0)
{
uint8_t v___x_421_; 
v___x_421_ = 0;
return v___x_421_;
}
else
{
uint8_t v___x_422_; 
v___x_422_ = 1;
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_isEmpty___redArg___boxed(lean_object* v_t_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Std_TreeMap_Raw_isEmpty___redArg(v_t_423_);
lean_dec(v_t_423_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_isEmpty(lean_object* v_00_u03b1_426_, lean_object* v_00_u03b2_427_, lean_object* v_cmp_428_, lean_object* v_t_429_){
_start:
{
if (lean_obj_tag(v_t_429_) == 0)
{
uint8_t v___x_430_; 
v___x_430_ = 0;
return v___x_430_;
}
else
{
uint8_t v___x_431_; 
v___x_431_ = 1;
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_432_, lean_object* v_00_u03b2_433_, lean_object* v_cmp_434_, lean_object* v_t_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_Std_TreeMap_Raw_isEmpty(v_00_u03b1_432_, v_00_u03b2_433_, v_cmp_434_, v_t_435_);
lean_dec(v_t_435_);
lean_dec_ref(v_cmp_434_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_erase___redArg(lean_object* v_cmp_438_, lean_object* v_t_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_438_, v_a_440_, v_t_439_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_erase(lean_object* v_00_u03b1_442_, lean_object* v_00_u03b2_443_, lean_object* v_cmp_444_, lean_object* v_t_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_444_, v_a_446_, v_t_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x3f___redArg(lean_object* v_cmp_448_, lean_object* v_t_449_, lean_object* v_a_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_448_, v_t_449_, v_a_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x3f(lean_object* v_00_u03b1_452_, lean_object* v_00_u03b2_453_, lean_object* v_cmp_454_, lean_object* v_t_455_, lean_object* v_a_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_454_, v_t_455_, v_a_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get___redArg(lean_object* v_cmp_458_, lean_object* v_t_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_458_, v_t_459_, v_a_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get(lean_object* v_00_u03b1_462_, lean_object* v_00_u03b2_463_, lean_object* v_cmp_464_, lean_object* v_t_465_, lean_object* v_a_466_, lean_object* v_h_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_464_, v_t_465_, v_a_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21___redArg(lean_object* v_cmp_469_, lean_object* v_inst_470_, lean_object* v_t_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_469_, v_inst_470_, v_t_471_, v_a_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_get_x21(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_cmp_476_, lean_object* v_inst_477_, lean_object* v_t_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_476_, v_inst_477_, v_t_478_, v_a_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___redArg(lean_object* v_cmp_481_, lean_object* v_t_482_, lean_object* v_a_483_, lean_object* v_fallback_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_481_, v_t_482_, v_a_483_, v_fallback_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___redArg___boxed(lean_object* v_cmp_486_, lean_object* v_t_487_, lean_object* v_a_488_, lean_object* v_fallback_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_TreeMap_Raw_getD___redArg(v_cmp_486_, v_t_487_, v_a_488_, v_fallback_489_);
lean_dec(v_fallback_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD(lean_object* v_00_u03b1_491_, lean_object* v_00_u03b2_492_, lean_object* v_cmp_493_, lean_object* v_t_494_, lean_object* v_a_495_, lean_object* v_fallback_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_493_, v_t_494_, v_a_495_, v_fallback_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getD___boxed(lean_object* v_00_u03b1_498_, lean_object* v_00_u03b2_499_, lean_object* v_cmp_500_, lean_object* v_t_501_, lean_object* v_a_502_, lean_object* v_fallback_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_TreeMap_Raw_getD(v_00_u03b1_498_, v_00_u03b2_499_, v_cmp_500_, v_t_501_, v_a_502_, v_fallback_503_);
lean_dec(v_fallback_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object* v_cmp_505_, lean_object* v_m_506_, lean_object* v_a_507_, lean_object* v_h_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_505_, v_m_506_, v_a_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object* v_cmp_510_, lean_object* v_m_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_510_, v_m_511_, v_a_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object* v_cmp_514_, lean_object* v_inst_515_, lean_object* v_m_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_514_, v_inst_515_, v_m_516_, v_a_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg(lean_object* v_cmp_519_){
_start:
{
lean_object* v___f_520_; lean_object* v___f_521_; lean_object* v___f_522_; lean_object* v___x_523_; 
lean_inc_ref(v_cmp_519_);
v___f_520_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__0), 4, 1);
lean_closure_set(v___f_520_, 0, v_cmp_519_);
lean_inc_ref(v_cmp_519_);
v___f_521_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__1), 3, 1);
lean_closure_set(v___f_521_, 0, v_cmp_519_);
v___f_522_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2), 4, 1);
lean_closure_set(v___f_522_, 0, v_cmp_519_);
v___x_523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_523_, 0, v___f_520_);
lean_ctor_set(v___x_523_, 1, v___f_521_);
lean_ctor_set(v___x_523_, 2, v___f_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instGetElem_x3fMem(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, lean_object* v_cmp_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg(v_cmp_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x3f___redArg(lean_object* v_cmp_528_, lean_object* v_t_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_528_, v_t_529_, v_a_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x3f(lean_object* v_00_u03b1_532_, lean_object* v_00_u03b2_533_, lean_object* v_cmp_534_, lean_object* v_t_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_534_, v_t_535_, v_a_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey___redArg(lean_object* v_cmp_538_, lean_object* v_t_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_538_, v_t_539_, v_a_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_, lean_object* v_cmp_544_, lean_object* v_t_545_, lean_object* v_a_546_, lean_object* v_h_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_544_, v_t_545_, v_a_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21___redArg(lean_object* v_cmp_549_, lean_object* v_inst_550_, lean_object* v_t_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_549_, v_t_551_, v_a_552_, v_inst_550_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKey_x21(lean_object* v_00_u03b1_554_, lean_object* v_00_u03b2_555_, lean_object* v_cmp_556_, lean_object* v_inst_557_, lean_object* v_t_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_556_, v_t_558_, v_a_559_, v_inst_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___redArg(lean_object* v_cmp_561_, lean_object* v_t_562_, lean_object* v_a_563_, lean_object* v_fallback_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_561_, v_t_562_, v_a_563_, v_fallback_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___redArg___boxed(lean_object* v_cmp_566_, lean_object* v_t_567_, lean_object* v_a_568_, lean_object* v_fallback_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_TreeMap_Raw_getKeyD___redArg(v_cmp_566_, v_t_567_, v_a_568_, v_fallback_569_);
lean_dec(v_fallback_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_cmp_573_, lean_object* v_t_574_, lean_object* v_a_575_, lean_object* v_fallback_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_573_, v_t_574_, v_a_575_, v_fallback_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_cmp_580_, lean_object* v_t_581_, lean_object* v_a_582_, lean_object* v_fallback_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_TreeMap_Raw_getKeyD(v_00_u03b1_578_, v_00_u03b2_579_, v_cmp_580_, v_t_581_, v_a_582_, v_fallback_583_);
lean_dec(v_fallback_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___redArg(lean_object* v_t_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___redArg___boxed(lean_object* v_t_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_TreeMap_Raw_minEntry_x3f___redArg(v_t_587_);
lean_dec(v_t_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f(lean_object* v_00_u03b1_589_, lean_object* v_00_u03b2_590_, lean_object* v_cmp_591_, lean_object* v_t_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x3f___boxed(lean_object* v_00_u03b1_594_, lean_object* v_00_u03b2_595_, lean_object* v_cmp_596_, lean_object* v_t_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Std_TreeMap_Raw_minEntry_x3f(v_00_u03b1_594_, v_00_u03b2_595_, v_cmp_596_, v_t_597_);
lean_dec(v_t_597_);
lean_dec_ref(v_cmp_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___redArg(lean_object* v_inst_599_, lean_object* v_t_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_599_, v_t_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___redArg___boxed(lean_object* v_inst_602_, lean_object* v_t_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_TreeMap_Raw_minEntry_x21___redArg(v_inst_602_, v_t_603_);
lean_dec(v_t_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21(lean_object* v_00_u03b1_605_, lean_object* v_00_u03b2_606_, lean_object* v_cmp_607_, lean_object* v_inst_608_, lean_object* v_t_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_608_, v_t_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntry_x21___boxed(lean_object* v_00_u03b1_611_, lean_object* v_00_u03b2_612_, lean_object* v_cmp_613_, lean_object* v_inst_614_, lean_object* v_t_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_TreeMap_Raw_minEntry_x21(v_00_u03b1_611_, v_00_u03b2_612_, v_cmp_613_, v_inst_614_, v_t_615_);
lean_dec(v_t_615_);
lean_dec_ref(v_cmp_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___redArg(lean_object* v_t_617_, lean_object* v_fallback_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_617_, v_fallback_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___redArg___boxed(lean_object* v_t_620_, lean_object* v_fallback_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Std_TreeMap_Raw_minEntryD___redArg(v_t_620_, v_fallback_621_);
lean_dec_ref(v_fallback_621_);
lean_dec(v_t_620_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD(lean_object* v_00_u03b1_623_, lean_object* v_00_u03b2_624_, lean_object* v_cmp_625_, lean_object* v_t_626_, lean_object* v_fallback_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_626_, v_fallback_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minEntryD___boxed(lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_cmp_631_, lean_object* v_t_632_, lean_object* v_fallback_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_TreeMap_Raw_minEntryD(v_00_u03b1_629_, v_00_u03b2_630_, v_cmp_631_, v_t_632_, v_fallback_633_);
lean_dec_ref(v_fallback_633_);
lean_dec(v_t_632_);
lean_dec_ref(v_cmp_631_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___redArg(lean_object* v_t_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___redArg___boxed(lean_object* v_t_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_TreeMap_Raw_maxEntry_x3f___redArg(v_t_637_);
lean_dec(v_t_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f(lean_object* v_00_u03b1_639_, lean_object* v_00_u03b2_640_, lean_object* v_cmp_641_, lean_object* v_t_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x3f___boxed(lean_object* v_00_u03b1_644_, lean_object* v_00_u03b2_645_, lean_object* v_cmp_646_, lean_object* v_t_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_TreeMap_Raw_maxEntry_x3f(v_00_u03b1_644_, v_00_u03b2_645_, v_cmp_646_, v_t_647_);
lean_dec(v_t_647_);
lean_dec_ref(v_cmp_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___redArg(lean_object* v_inst_649_, lean_object* v_t_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_649_, v_t_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___redArg___boxed(lean_object* v_inst_652_, lean_object* v_t_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_TreeMap_Raw_maxEntry_x21___redArg(v_inst_652_, v_t_653_);
lean_dec(v_t_653_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21(lean_object* v_00_u03b1_655_, lean_object* v_00_u03b2_656_, lean_object* v_cmp_657_, lean_object* v_inst_658_, lean_object* v_t_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_658_, v_t_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntry_x21___boxed(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_cmp_663_, lean_object* v_inst_664_, lean_object* v_t_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_TreeMap_Raw_maxEntry_x21(v_00_u03b1_661_, v_00_u03b2_662_, v_cmp_663_, v_inst_664_, v_t_665_);
lean_dec(v_t_665_);
lean_dec_ref(v_cmp_663_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___redArg(lean_object* v_t_667_, lean_object* v_fallback_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_667_, v_fallback_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___redArg___boxed(lean_object* v_t_670_, lean_object* v_fallback_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Std_TreeMap_Raw_maxEntryD___redArg(v_t_670_, v_fallback_671_);
lean_dec_ref(v_fallback_671_);
lean_dec(v_t_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_cmp_675_, lean_object* v_t_676_, lean_object* v_fallback_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_676_, v_fallback_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxEntryD___boxed(lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_cmp_681_, lean_object* v_t_682_, lean_object* v_fallback_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_TreeMap_Raw_maxEntryD(v_00_u03b1_679_, v_00_u03b2_680_, v_cmp_681_, v_t_682_, v_fallback_683_);
lean_dec_ref(v_fallback_683_);
lean_dec(v_t_682_);
lean_dec_ref(v_cmp_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___redArg(lean_object* v_t_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___redArg___boxed(lean_object* v_t_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_TreeMap_Raw_minKey_x3f___redArg(v_t_687_);
lean_dec(v_t_687_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f(lean_object* v_00_u03b1_689_, lean_object* v_00_u03b2_690_, lean_object* v_cmp_691_, lean_object* v_t_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x3f___boxed(lean_object* v_00_u03b1_694_, lean_object* v_00_u03b2_695_, lean_object* v_cmp_696_, lean_object* v_t_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_TreeMap_Raw_minKey_x3f(v_00_u03b1_694_, v_00_u03b2_695_, v_cmp_696_, v_t_697_);
lean_dec(v_t_697_);
lean_dec_ref(v_cmp_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___redArg(lean_object* v_inst_699_, lean_object* v_t_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_699_, v_t_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___redArg___boxed(lean_object* v_inst_702_, lean_object* v_t_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_TreeMap_Raw_minKey_x21___redArg(v_inst_702_, v_t_703_);
lean_dec(v_t_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b2_706_, lean_object* v_cmp_707_, lean_object* v_inst_708_, lean_object* v_t_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_708_, v_t_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKey_x21___boxed(lean_object* v_00_u03b1_711_, lean_object* v_00_u03b2_712_, lean_object* v_cmp_713_, lean_object* v_inst_714_, lean_object* v_t_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_TreeMap_Raw_minKey_x21(v_00_u03b1_711_, v_00_u03b2_712_, v_cmp_713_, v_inst_714_, v_t_715_);
lean_dec(v_t_715_);
lean_dec_ref(v_cmp_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___redArg(lean_object* v_t_717_, lean_object* v_fallback_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_717_, v_fallback_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___redArg___boxed(lean_object* v_t_720_, lean_object* v_fallback_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_TreeMap_Raw_minKeyD___redArg(v_t_720_, v_fallback_721_);
lean_dec(v_fallback_721_);
lean_dec(v_t_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_cmp_725_, lean_object* v_t_726_, lean_object* v_fallback_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_726_, v_fallback_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_minKeyD___boxed(lean_object* v_00_u03b1_729_, lean_object* v_00_u03b2_730_, lean_object* v_cmp_731_, lean_object* v_t_732_, lean_object* v_fallback_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_TreeMap_Raw_minKeyD(v_00_u03b1_729_, v_00_u03b2_730_, v_cmp_731_, v_t_732_, v_fallback_733_);
lean_dec(v_fallback_733_);
lean_dec(v_t_732_);
lean_dec_ref(v_cmp_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___redArg(lean_object* v_t_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___redArg___boxed(lean_object* v_t_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_TreeMap_Raw_maxKey_x3f___redArg(v_t_737_);
lean_dec(v_t_737_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f(lean_object* v_00_u03b1_739_, lean_object* v_00_u03b2_740_, lean_object* v_cmp_741_, lean_object* v_t_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x3f___boxed(lean_object* v_00_u03b1_744_, lean_object* v_00_u03b2_745_, lean_object* v_cmp_746_, lean_object* v_t_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_TreeMap_Raw_maxKey_x3f(v_00_u03b1_744_, v_00_u03b2_745_, v_cmp_746_, v_t_747_);
lean_dec(v_t_747_);
lean_dec_ref(v_cmp_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___redArg(lean_object* v_inst_749_, lean_object* v_t_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_749_, v_t_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___redArg___boxed(lean_object* v_inst_752_, lean_object* v_t_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_TreeMap_Raw_maxKey_x21___redArg(v_inst_752_, v_t_753_);
lean_dec(v_t_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21(lean_object* v_00_u03b1_755_, lean_object* v_00_u03b2_756_, lean_object* v_cmp_757_, lean_object* v_inst_758_, lean_object* v_t_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_758_, v_t_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKey_x21___boxed(lean_object* v_00_u03b1_761_, lean_object* v_00_u03b2_762_, lean_object* v_cmp_763_, lean_object* v_inst_764_, lean_object* v_t_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_TreeMap_Raw_maxKey_x21(v_00_u03b1_761_, v_00_u03b2_762_, v_cmp_763_, v_inst_764_, v_t_765_);
lean_dec(v_t_765_);
lean_dec_ref(v_cmp_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___redArg(lean_object* v_t_767_, lean_object* v_fallback_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_767_, v_fallback_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___redArg___boxed(lean_object* v_t_770_, lean_object* v_fallback_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_TreeMap_Raw_maxKeyD___redArg(v_t_770_, v_fallback_771_);
lean_dec(v_fallback_771_);
lean_dec(v_t_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD(lean_object* v_00_u03b1_773_, lean_object* v_00_u03b2_774_, lean_object* v_cmp_775_, lean_object* v_t_776_, lean_object* v_fallback_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_776_, v_fallback_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_maxKeyD___boxed(lean_object* v_00_u03b1_779_, lean_object* v_00_u03b2_780_, lean_object* v_cmp_781_, lean_object* v_t_782_, lean_object* v_fallback_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_TreeMap_Raw_maxKeyD(v_00_u03b1_779_, v_00_u03b2_780_, v_cmp_781_, v_t_782_, v_fallback_783_);
lean_dec(v_fallback_783_);
lean_dec(v_t_782_);
lean_dec_ref(v_cmp_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg(lean_object* v_t_785_, lean_object* v_n_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_785_, v_n_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_788_, lean_object* v_n_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg(v_t_788_, v_n_789_);
lean_dec(v_t_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f(lean_object* v_00_u03b1_791_, lean_object* v_00_u03b2_792_, lean_object* v_cmp_793_, lean_object* v_t_794_, lean_object* v_n_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_794_, v_n_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_797_, lean_object* v_00_u03b2_798_, lean_object* v_cmp_799_, lean_object* v_t_800_, lean_object* v_n_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_TreeMap_Raw_entryAtIdx_x3f(v_00_u03b1_797_, v_00_u03b2_798_, v_cmp_799_, v_t_800_, v_n_801_);
lean_dec(v_t_800_);
lean_dec_ref(v_cmp_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___redArg(lean_object* v_inst_803_, lean_object* v_t_804_, lean_object* v_n_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_803_, v_t_804_, v_n_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_807_, lean_object* v_t_808_, lean_object* v_n_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_TreeMap_Raw_entryAtIdx_x21___redArg(v_inst_807_, v_t_808_, v_n_809_);
lean_dec(v_t_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21(lean_object* v_00_u03b1_811_, lean_object* v_00_u03b2_812_, lean_object* v_cmp_813_, lean_object* v_inst_814_, lean_object* v_t_815_, lean_object* v_n_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_814_, v_t_815_, v_n_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_818_, lean_object* v_00_u03b2_819_, lean_object* v_cmp_820_, lean_object* v_inst_821_, lean_object* v_t_822_, lean_object* v_n_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_TreeMap_Raw_entryAtIdx_x21(v_00_u03b1_818_, v_00_u03b2_819_, v_cmp_820_, v_inst_821_, v_t_822_, v_n_823_);
lean_dec(v_t_822_);
lean_dec_ref(v_cmp_820_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___redArg(lean_object* v_t_825_, lean_object* v_n_826_, lean_object* v_fallback_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_825_, v_n_826_, v_fallback_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___redArg___boxed(lean_object* v_t_829_, lean_object* v_n_830_, lean_object* v_fallback_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_TreeMap_Raw_entryAtIdxD___redArg(v_t_829_, v_n_830_, v_fallback_831_);
lean_dec_ref(v_fallback_831_);
lean_dec(v_t_829_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD(lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_cmp_835_, lean_object* v_t_836_, lean_object* v_n_837_, lean_object* v_fallback_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_836_, v_n_837_, v_fallback_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_entryAtIdxD___boxed(lean_object* v_00_u03b1_840_, lean_object* v_00_u03b2_841_, lean_object* v_cmp_842_, lean_object* v_t_843_, lean_object* v_n_844_, lean_object* v_fallback_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_TreeMap_Raw_entryAtIdxD(v_00_u03b1_840_, v_00_u03b2_841_, v_cmp_842_, v_t_843_, v_n_844_, v_fallback_845_);
lean_dec_ref(v_fallback_845_);
lean_dec(v_t_843_);
lean_dec_ref(v_cmp_842_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg(lean_object* v_t_847_, lean_object* v_n_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_847_, v_n_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_850_, lean_object* v_n_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg(v_t_850_, v_n_851_);
lean_dec(v_t_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f(lean_object* v_00_u03b1_853_, lean_object* v_00_u03b2_854_, lean_object* v_cmp_855_, lean_object* v_t_856_, lean_object* v_n_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_856_, v_n_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_859_, lean_object* v_00_u03b2_860_, lean_object* v_cmp_861_, lean_object* v_t_862_, lean_object* v_n_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_TreeMap_Raw_keyAtIdx_x3f(v_00_u03b1_859_, v_00_u03b2_860_, v_cmp_861_, v_t_862_, v_n_863_);
lean_dec(v_t_862_);
lean_dec_ref(v_cmp_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___redArg(lean_object* v_inst_865_, lean_object* v_t_866_, lean_object* v_n_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_865_, v_t_866_, v_n_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_869_, lean_object* v_t_870_, lean_object* v_n_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_TreeMap_Raw_keyAtIdx_x21___redArg(v_inst_869_, v_t_870_, v_n_871_);
lean_dec(v_t_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21(lean_object* v_00_u03b1_873_, lean_object* v_00_u03b2_874_, lean_object* v_cmp_875_, lean_object* v_inst_876_, lean_object* v_t_877_, lean_object* v_n_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_876_, v_t_877_, v_n_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_880_, lean_object* v_00_u03b2_881_, lean_object* v_cmp_882_, lean_object* v_inst_883_, lean_object* v_t_884_, lean_object* v_n_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_TreeMap_Raw_keyAtIdx_x21(v_00_u03b1_880_, v_00_u03b2_881_, v_cmp_882_, v_inst_883_, v_t_884_, v_n_885_);
lean_dec(v_t_884_);
lean_dec_ref(v_cmp_882_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___redArg(lean_object* v_t_887_, lean_object* v_n_888_, lean_object* v_fallback_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_887_, v_n_888_, v_fallback_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___redArg___boxed(lean_object* v_t_891_, lean_object* v_n_892_, lean_object* v_fallback_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Std_TreeMap_Raw_keyAtIdxD___redArg(v_t_891_, v_n_892_, v_fallback_893_);
lean_dec(v_fallback_893_);
lean_dec(v_t_891_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_cmp_897_, lean_object* v_t_898_, lean_object* v_n_899_, lean_object* v_fallback_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_898_, v_n_899_, v_fallback_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keyAtIdxD___boxed(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_cmp_904_, lean_object* v_t_905_, lean_object* v_n_906_, lean_object* v_fallback_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_TreeMap_Raw_keyAtIdxD(v_00_u03b1_902_, v_00_u03b2_903_, v_cmp_904_, v_t_905_, v_n_906_, v_fallback_907_);
lean_dec(v_fallback_907_);
lean_dec(v_t_905_);
lean_dec_ref(v_cmp_904_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x3f___redArg(lean_object* v_cmp_909_, lean_object* v_t_910_, lean_object* v_k_911_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_box(0);
v___x_913_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_909_, v_k_911_, v___x_912_, v_t_910_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x3f(lean_object* v_00_u03b1_914_, lean_object* v_00_u03b2_915_, lean_object* v_cmp_916_, lean_object* v_t_917_, lean_object* v_k_918_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_box(0);
v___x_920_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_916_, v_k_918_, v___x_919_, v_t_917_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x3f___redArg(lean_object* v_cmp_921_, lean_object* v_t_922_, lean_object* v_k_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_box(0);
v___x_925_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_921_, v_k_923_, v___x_924_, v_t_922_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x3f(lean_object* v_00_u03b1_926_, lean_object* v_00_u03b2_927_, lean_object* v_cmp_928_, lean_object* v_t_929_, lean_object* v_k_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_box(0);
v___x_932_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_928_, v_k_930_, v___x_931_, v_t_929_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x3f___redArg(lean_object* v_cmp_933_, lean_object* v_t_934_, lean_object* v_k_935_){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_box(0);
v___x_937_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_933_, v_k_935_, v___x_936_, v_t_934_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x3f(lean_object* v_00_u03b1_938_, lean_object* v_00_u03b2_939_, lean_object* v_cmp_940_, lean_object* v_t_941_, lean_object* v_k_942_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_box(0);
v___x_944_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_940_, v_k_942_, v___x_943_, v_t_941_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x3f___redArg(lean_object* v_cmp_945_, lean_object* v_t_946_, lean_object* v_k_947_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_box(0);
v___x_949_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_945_, v_k_947_, v___x_948_, v_t_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x3f(lean_object* v_00_u03b1_950_, lean_object* v_00_u03b2_951_, lean_object* v_cmp_952_, lean_object* v_t_953_, lean_object* v_k_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_box(0);
v___x_956_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_952_, v_k_954_, v___x_955_, v_t_953_);
return v___x_956_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_960_ = ((lean_object*)(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__2));
v___x_961_ = lean_unsigned_to_nat(14u);
v___x_962_ = lean_unsigned_to_nat(22u);
v___x_963_ = ((lean_object*)(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__1));
v___x_964_ = ((lean_object*)(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__0));
v___x_965_ = l_mkPanicMessageWithDecl(v___x_964_, v___x_963_, v___x_962_, v___x_961_, v___x_960_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21___redArg(lean_object* v_cmp_966_, lean_object* v_inst_967_, lean_object* v_t_968_, lean_object* v_k_969_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_box(0);
v___x_971_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_966_, v_k_969_, v___x_970_, v_t_968_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_973_ = l_panic___redArg(v_inst_967_, v___x_972_);
return v___x_973_;
}
else
{
lean_object* v_val_974_; 
lean_dec_ref(v_inst_967_);
v_val_974_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_val_974_);
lean_dec_ref(v___x_971_);
return v_val_974_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGE_x21(lean_object* v_00_u03b1_975_, lean_object* v_00_u03b2_976_, lean_object* v_cmp_977_, lean_object* v_inst_978_, lean_object* v_t_979_, lean_object* v_k_980_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_box(0);
v___x_982_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_977_, v_k_980_, v___x_981_, v_t_979_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_984_ = l_panic___redArg(v_inst_978_, v___x_983_);
return v___x_984_;
}
else
{
lean_object* v_val_985_; 
lean_dec_ref(v_inst_978_);
v_val_985_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_985_);
lean_dec_ref(v___x_982_);
return v_val_985_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21___redArg(lean_object* v_cmp_986_, lean_object* v_inst_987_, lean_object* v_t_988_, lean_object* v_k_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_box(0);
v___x_991_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_986_, v_k_989_, v___x_990_, v_t_988_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_993_ = l_panic___redArg(v_inst_987_, v___x_992_);
return v___x_993_;
}
else
{
lean_object* v_val_994_; 
lean_dec_ref(v_inst_987_);
v_val_994_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_val_994_);
lean_dec_ref(v___x_991_);
return v_val_994_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGT_x21(lean_object* v_00_u03b1_995_, lean_object* v_00_u03b2_996_, lean_object* v_cmp_997_, lean_object* v_inst_998_, lean_object* v_t_999_, lean_object* v_k_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_box(0);
v___x_1002_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_997_, v_k_1000_, v___x_1001_, v_t_999_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1004_ = l_panic___redArg(v_inst_998_, v___x_1003_);
return v___x_1004_;
}
else
{
lean_object* v_val_1005_; 
lean_dec_ref(v_inst_998_);
v_val_1005_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_val_1005_);
lean_dec_ref(v___x_1002_);
return v_val_1005_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21___redArg(lean_object* v_cmp_1006_, lean_object* v_inst_1007_, lean_object* v_t_1008_, lean_object* v_k_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1006_, v_k_1009_, v___x_1010_, v_t_1008_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1013_ = l_panic___redArg(v_inst_1007_, v___x_1012_);
return v___x_1013_;
}
else
{
lean_object* v_val_1014_; 
lean_dec_ref(v_inst_1007_);
v_val_1014_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_val_1014_);
lean_dec_ref(v___x_1011_);
return v_val_1014_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLE_x21(lean_object* v_00_u03b1_1015_, lean_object* v_00_u03b2_1016_, lean_object* v_cmp_1017_, lean_object* v_inst_1018_, lean_object* v_t_1019_, lean_object* v_k_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_box(0);
v___x_1022_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1017_, v_k_1020_, v___x_1021_, v_t_1019_);
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
lean_dec_ref(v_inst_1018_);
v_val_1025_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_val_1025_);
lean_dec_ref(v___x_1022_);
return v_val_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21___redArg(lean_object* v_cmp_1026_, lean_object* v_inst_1027_, lean_object* v_t_1028_, lean_object* v_k_1029_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1026_, v_k_1029_, v___x_1030_, v_t_1028_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1033_ = l_panic___redArg(v_inst_1027_, v___x_1032_);
return v___x_1033_;
}
else
{
lean_object* v_val_1034_; 
lean_dec_ref(v_inst_1027_);
v_val_1034_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_val_1034_);
lean_dec_ref(v___x_1031_);
return v_val_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLT_x21(lean_object* v_00_u03b1_1035_, lean_object* v_00_u03b2_1036_, lean_object* v_cmp_1037_, lean_object* v_inst_1038_, lean_object* v_t_1039_, lean_object* v_k_1040_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_box(0);
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1037_, v_k_1040_, v___x_1041_, v_t_1039_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1044_ = l_panic___redArg(v_inst_1038_, v___x_1043_);
return v___x_1044_;
}
else
{
lean_object* v_val_1045_; 
lean_dec_ref(v_inst_1038_);
v_val_1045_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_val_1045_);
lean_dec_ref(v___x_1042_);
return v_val_1045_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___redArg(lean_object* v_cmp_1046_, lean_object* v_t_1047_, lean_object* v_k_1048_, lean_object* v_fallback_1049_){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_box(0);
v___x_1051_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1046_, v_k_1048_, v___x_1050_, v_t_1047_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_inc_ref(v_fallback_1049_);
return v_fallback_1049_;
}
else
{
lean_object* v_val_1052_; 
v_val_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_val_1052_);
lean_dec_ref(v___x_1051_);
return v_val_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___redArg___boxed(lean_object* v_cmp_1053_, lean_object* v_t_1054_, lean_object* v_k_1055_, lean_object* v_fallback_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Std_TreeMap_Raw_getEntryGED___redArg(v_cmp_1053_, v_t_1054_, v_k_1055_, v_fallback_1056_);
lean_dec_ref(v_fallback_1056_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED(lean_object* v_00_u03b1_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_cmp_1060_, lean_object* v_t_1061_, lean_object* v_k_1062_, lean_object* v_fallback_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1060_, v_k_1062_, v___x_1064_, v_t_1061_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_inc_ref(v_fallback_1063_);
return v_fallback_1063_;
}
else
{
lean_object* v_val_1066_; 
v_val_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_val_1066_);
lean_dec_ref(v___x_1065_);
return v_val_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGED___boxed(lean_object* v_00_u03b1_1067_, lean_object* v_00_u03b2_1068_, lean_object* v_cmp_1069_, lean_object* v_t_1070_, lean_object* v_k_1071_, lean_object* v_fallback_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_TreeMap_Raw_getEntryGED(v_00_u03b1_1067_, v_00_u03b2_1068_, v_cmp_1069_, v_t_1070_, v_k_1071_, v_fallback_1072_);
lean_dec_ref(v_fallback_1072_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___redArg(lean_object* v_cmp_1074_, lean_object* v_t_1075_, lean_object* v_k_1076_, lean_object* v_fallback_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1074_, v_k_1076_, v___x_1078_, v_t_1075_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_inc_ref(v_fallback_1077_);
return v_fallback_1077_;
}
else
{
lean_object* v_val_1080_; 
v_val_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_val_1080_);
lean_dec_ref(v___x_1079_);
return v_val_1080_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___redArg___boxed(lean_object* v_cmp_1081_, lean_object* v_t_1082_, lean_object* v_k_1083_, lean_object* v_fallback_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Std_TreeMap_Raw_getEntryGTD___redArg(v_cmp_1081_, v_t_1082_, v_k_1083_, v_fallback_1084_);
lean_dec_ref(v_fallback_1084_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_cmp_1088_, lean_object* v_t_1089_, lean_object* v_k_1090_, lean_object* v_fallback_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1088_, v_k_1090_, v___x_1092_, v_t_1089_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_inc_ref(v_fallback_1091_);
return v_fallback_1091_;
}
else
{
lean_object* v_val_1094_; 
v_val_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_val_1094_);
lean_dec_ref(v___x_1093_);
return v_val_1094_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryGTD___boxed(lean_object* v_00_u03b1_1095_, lean_object* v_00_u03b2_1096_, lean_object* v_cmp_1097_, lean_object* v_t_1098_, lean_object* v_k_1099_, lean_object* v_fallback_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Std_TreeMap_Raw_getEntryGTD(v_00_u03b1_1095_, v_00_u03b2_1096_, v_cmp_1097_, v_t_1098_, v_k_1099_, v_fallback_1100_);
lean_dec_ref(v_fallback_1100_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___redArg(lean_object* v_cmp_1102_, lean_object* v_t_1103_, lean_object* v_k_1104_, lean_object* v_fallback_1105_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_box(0);
v___x_1107_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1102_, v_k_1104_, v___x_1106_, v_t_1103_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_inc_ref(v_fallback_1105_);
return v_fallback_1105_;
}
else
{
lean_object* v_val_1108_; 
v_val_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_val_1108_);
lean_dec_ref(v___x_1107_);
return v_val_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___redArg___boxed(lean_object* v_cmp_1109_, lean_object* v_t_1110_, lean_object* v_k_1111_, lean_object* v_fallback_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Std_TreeMap_Raw_getEntryLED___redArg(v_cmp_1109_, v_t_1110_, v_k_1111_, v_fallback_1112_);
lean_dec_ref(v_fallback_1112_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED(lean_object* v_00_u03b1_1114_, lean_object* v_00_u03b2_1115_, lean_object* v_cmp_1116_, lean_object* v_t_1117_, lean_object* v_k_1118_, lean_object* v_fallback_1119_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_box(0);
v___x_1121_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1116_, v_k_1118_, v___x_1120_, v_t_1117_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_inc_ref(v_fallback_1119_);
return v_fallback_1119_;
}
else
{
lean_object* v_val_1122_; 
v_val_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_val_1122_);
lean_dec_ref(v___x_1121_);
return v_val_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLED___boxed(lean_object* v_00_u03b1_1123_, lean_object* v_00_u03b2_1124_, lean_object* v_cmp_1125_, lean_object* v_t_1126_, lean_object* v_k_1127_, lean_object* v_fallback_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Std_TreeMap_Raw_getEntryLED(v_00_u03b1_1123_, v_00_u03b2_1124_, v_cmp_1125_, v_t_1126_, v_k_1127_, v_fallback_1128_);
lean_dec_ref(v_fallback_1128_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___redArg(lean_object* v_cmp_1130_, lean_object* v_t_1131_, lean_object* v_k_1132_, lean_object* v_fallback_1133_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1130_, v_k_1132_, v___x_1134_, v_t_1131_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_inc_ref(v_fallback_1133_);
return v_fallback_1133_;
}
else
{
lean_object* v_val_1136_; 
v_val_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_val_1136_);
lean_dec_ref(v___x_1135_);
return v_val_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___redArg___boxed(lean_object* v_cmp_1137_, lean_object* v_t_1138_, lean_object* v_k_1139_, lean_object* v_fallback_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Std_TreeMap_Raw_getEntryLTD___redArg(v_cmp_1137_, v_t_1138_, v_k_1139_, v_fallback_1140_);
lean_dec_ref(v_fallback_1140_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD(lean_object* v_00_u03b1_1142_, lean_object* v_00_u03b2_1143_, lean_object* v_cmp_1144_, lean_object* v_t_1145_, lean_object* v_k_1146_, lean_object* v_fallback_1147_){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_box(0);
v___x_1149_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1144_, v_k_1146_, v___x_1148_, v_t_1145_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_inc_ref(v_fallback_1147_);
return v_fallback_1147_;
}
else
{
lean_object* v_val_1150_; 
v_val_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_val_1150_);
lean_dec_ref(v___x_1149_);
return v_val_1150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getEntryLTD___boxed(lean_object* v_00_u03b1_1151_, lean_object* v_00_u03b2_1152_, lean_object* v_cmp_1153_, lean_object* v_t_1154_, lean_object* v_k_1155_, lean_object* v_fallback_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Std_TreeMap_Raw_getEntryLTD(v_00_u03b1_1151_, v_00_u03b2_1152_, v_cmp_1153_, v_t_1154_, v_k_1155_, v_fallback_1156_);
lean_dec_ref(v_fallback_1156_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x3f___redArg(lean_object* v_cmp_1158_, lean_object* v_t_1159_, lean_object* v_k_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_box(0);
v___x_1162_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1158_, v_k_1160_, v___x_1161_, v_t_1159_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x3f(lean_object* v_00_u03b1_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_cmp_1165_, lean_object* v_t_1166_, lean_object* v_k_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_box(0);
v___x_1169_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1165_, v_k_1167_, v___x_1168_, v_t_1166_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x3f___redArg(lean_object* v_cmp_1170_, lean_object* v_t_1171_, lean_object* v_k_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_box(0);
v___x_1174_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1170_, v_k_1172_, v___x_1173_, v_t_1171_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x3f(lean_object* v_00_u03b1_1175_, lean_object* v_00_u03b2_1176_, lean_object* v_cmp_1177_, lean_object* v_t_1178_, lean_object* v_k_1179_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_box(0);
v___x_1181_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1177_, v_k_1179_, v___x_1180_, v_t_1178_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x3f___redArg(lean_object* v_cmp_1182_, lean_object* v_t_1183_, lean_object* v_k_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_box(0);
v___x_1186_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1182_, v_k_1184_, v___x_1185_, v_t_1183_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x3f(lean_object* v_00_u03b1_1187_, lean_object* v_00_u03b2_1188_, lean_object* v_cmp_1189_, lean_object* v_t_1190_, lean_object* v_k_1191_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_box(0);
v___x_1193_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1189_, v_k_1191_, v___x_1192_, v_t_1190_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x3f___redArg(lean_object* v_cmp_1194_, lean_object* v_t_1195_, lean_object* v_k_1196_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_box(0);
v___x_1198_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1194_, v_k_1196_, v___x_1197_, v_t_1195_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x3f(lean_object* v_00_u03b1_1199_, lean_object* v_00_u03b2_1200_, lean_object* v_cmp_1201_, lean_object* v_t_1202_, lean_object* v_k_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1201_, v_k_1203_, v___x_1204_, v_t_1202_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21___redArg(lean_object* v_cmp_1206_, lean_object* v_inst_1207_, lean_object* v_t_1208_, lean_object* v_k_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_box(0);
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1206_, v_k_1209_, v___x_1210_, v_t_1208_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1213_ = l_panic___redArg(v_inst_1207_, v___x_1212_);
return v___x_1213_;
}
else
{
lean_object* v_val_1214_; 
lean_dec(v_inst_1207_);
v_val_1214_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_val_1214_);
lean_dec_ref(v___x_1211_);
return v_val_1214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGE_x21(lean_object* v_00_u03b1_1215_, lean_object* v_00_u03b2_1216_, lean_object* v_cmp_1217_, lean_object* v_inst_1218_, lean_object* v_t_1219_, lean_object* v_k_1220_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1217_, v_k_1220_, v___x_1221_, v_t_1219_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1224_ = l_panic___redArg(v_inst_1218_, v___x_1223_);
return v___x_1224_;
}
else
{
lean_object* v_val_1225_; 
lean_dec(v_inst_1218_);
v_val_1225_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_val_1225_);
lean_dec_ref(v___x_1222_);
return v_val_1225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21___redArg(lean_object* v_cmp_1226_, lean_object* v_inst_1227_, lean_object* v_t_1228_, lean_object* v_k_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_box(0);
v___x_1231_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1226_, v_k_1229_, v___x_1230_, v_t_1228_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1233_ = l_panic___redArg(v_inst_1227_, v___x_1232_);
return v___x_1233_;
}
else
{
lean_object* v_val_1234_; 
lean_dec(v_inst_1227_);
v_val_1234_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_val_1234_);
lean_dec_ref(v___x_1231_);
return v_val_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGT_x21(lean_object* v_00_u03b1_1235_, lean_object* v_00_u03b2_1236_, lean_object* v_cmp_1237_, lean_object* v_inst_1238_, lean_object* v_t_1239_, lean_object* v_k_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_box(0);
v___x_1242_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1237_, v_k_1240_, v___x_1241_, v_t_1239_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1244_ = l_panic___redArg(v_inst_1238_, v___x_1243_);
return v___x_1244_;
}
else
{
lean_object* v_val_1245_; 
lean_dec(v_inst_1238_);
v_val_1245_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_val_1245_);
lean_dec_ref(v___x_1242_);
return v_val_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21___redArg(lean_object* v_cmp_1246_, lean_object* v_inst_1247_, lean_object* v_t_1248_, lean_object* v_k_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_box(0);
v___x_1251_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1246_, v_k_1249_, v___x_1250_, v_t_1248_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1253_ = l_panic___redArg(v_inst_1247_, v___x_1252_);
return v___x_1253_;
}
else
{
lean_object* v_val_1254_; 
lean_dec(v_inst_1247_);
v_val_1254_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_val_1254_);
lean_dec_ref(v___x_1251_);
return v_val_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLE_x21(lean_object* v_00_u03b1_1255_, lean_object* v_00_u03b2_1256_, lean_object* v_cmp_1257_, lean_object* v_inst_1258_, lean_object* v_t_1259_, lean_object* v_k_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1257_, v_k_1260_, v___x_1261_, v_t_1259_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1264_ = l_panic___redArg(v_inst_1258_, v___x_1263_);
return v___x_1264_;
}
else
{
lean_object* v_val_1265_; 
lean_dec(v_inst_1258_);
v_val_1265_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_val_1265_);
lean_dec_ref(v___x_1262_);
return v_val_1265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21___redArg(lean_object* v_cmp_1266_, lean_object* v_inst_1267_, lean_object* v_t_1268_, lean_object* v_k_1269_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_box(0);
v___x_1271_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1266_, v_k_1269_, v___x_1270_, v_t_1268_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1273_ = l_panic___redArg(v_inst_1267_, v___x_1272_);
return v___x_1273_;
}
else
{
lean_object* v_val_1274_; 
lean_dec(v_inst_1267_);
v_val_1274_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_val_1274_);
lean_dec_ref(v___x_1271_);
return v_val_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLT_x21(lean_object* v_00_u03b1_1275_, lean_object* v_00_u03b2_1276_, lean_object* v_cmp_1277_, lean_object* v_inst_1278_, lean_object* v_t_1279_, lean_object* v_k_1280_){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_box(0);
v___x_1282_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1277_, v_k_1280_, v___x_1281_, v_t_1279_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_obj_once(&l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1284_ = l_panic___redArg(v_inst_1278_, v___x_1283_);
return v___x_1284_;
}
else
{
lean_object* v_val_1285_; 
lean_dec(v_inst_1278_);
v_val_1285_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_val_1285_);
lean_dec_ref(v___x_1282_);
return v_val_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___redArg(lean_object* v_cmp_1286_, lean_object* v_t_1287_, lean_object* v_k_1288_, lean_object* v_fallback_1289_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1286_, v_k_1288_, v___x_1290_, v_t_1287_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_inc(v_fallback_1289_);
return v_fallback_1289_;
}
else
{
lean_object* v_val_1292_; 
v_val_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_val_1292_);
lean_dec_ref(v___x_1291_);
return v_val_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___redArg___boxed(lean_object* v_cmp_1293_, lean_object* v_t_1294_, lean_object* v_k_1295_, lean_object* v_fallback_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Std_TreeMap_Raw_getKeyGED___redArg(v_cmp_1293_, v_t_1294_, v_k_1295_, v_fallback_1296_);
lean_dec(v_fallback_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED(lean_object* v_00_u03b1_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_cmp_1300_, lean_object* v_t_1301_, lean_object* v_k_1302_, lean_object* v_fallback_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1300_, v_k_1302_, v___x_1304_, v_t_1301_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_inc(v_fallback_1303_);
return v_fallback_1303_;
}
else
{
lean_object* v_val_1306_; 
v_val_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_val_1306_);
lean_dec_ref(v___x_1305_);
return v_val_1306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGED___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_00_u03b2_1308_, lean_object* v_cmp_1309_, lean_object* v_t_1310_, lean_object* v_k_1311_, lean_object* v_fallback_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Std_TreeMap_Raw_getKeyGED(v_00_u03b1_1307_, v_00_u03b2_1308_, v_cmp_1309_, v_t_1310_, v_k_1311_, v_fallback_1312_);
lean_dec(v_fallback_1312_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___redArg(lean_object* v_cmp_1314_, lean_object* v_t_1315_, lean_object* v_k_1316_, lean_object* v_fallback_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_box(0);
v___x_1319_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1314_, v_k_1316_, v___x_1318_, v_t_1315_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_inc(v_fallback_1317_);
return v_fallback_1317_;
}
else
{
lean_object* v_val_1320_; 
v_val_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_val_1320_);
lean_dec_ref(v___x_1319_);
return v_val_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___redArg___boxed(lean_object* v_cmp_1321_, lean_object* v_t_1322_, lean_object* v_k_1323_, lean_object* v_fallback_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_TreeMap_Raw_getKeyGTD___redArg(v_cmp_1321_, v_t_1322_, v_k_1323_, v_fallback_1324_);
lean_dec(v_fallback_1324_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD(lean_object* v_00_u03b1_1326_, lean_object* v_00_u03b2_1327_, lean_object* v_cmp_1328_, lean_object* v_t_1329_, lean_object* v_k_1330_, lean_object* v_fallback_1331_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_box(0);
v___x_1333_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1328_, v_k_1330_, v___x_1332_, v_t_1329_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_inc(v_fallback_1331_);
return v_fallback_1331_;
}
else
{
lean_object* v_val_1334_; 
v_val_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_val_1334_);
lean_dec_ref(v___x_1333_);
return v_val_1334_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyGTD___boxed(lean_object* v_00_u03b1_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_cmp_1337_, lean_object* v_t_1338_, lean_object* v_k_1339_, lean_object* v_fallback_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_TreeMap_Raw_getKeyGTD(v_00_u03b1_1335_, v_00_u03b2_1336_, v_cmp_1337_, v_t_1338_, v_k_1339_, v_fallback_1340_);
lean_dec(v_fallback_1340_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___redArg(lean_object* v_cmp_1342_, lean_object* v_t_1343_, lean_object* v_k_1344_, lean_object* v_fallback_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_box(0);
v___x_1347_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1342_, v_k_1344_, v___x_1346_, v_t_1343_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_inc(v_fallback_1345_);
return v_fallback_1345_;
}
else
{
lean_object* v_val_1348_; 
v_val_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_val_1348_);
lean_dec_ref(v___x_1347_);
return v_val_1348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___redArg___boxed(lean_object* v_cmp_1349_, lean_object* v_t_1350_, lean_object* v_k_1351_, lean_object* v_fallback_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Std_TreeMap_Raw_getKeyLED___redArg(v_cmp_1349_, v_t_1350_, v_k_1351_, v_fallback_1352_);
lean_dec(v_fallback_1352_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED(lean_object* v_00_u03b1_1354_, lean_object* v_00_u03b2_1355_, lean_object* v_cmp_1356_, lean_object* v_t_1357_, lean_object* v_k_1358_, lean_object* v_fallback_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_box(0);
v___x_1361_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1356_, v_k_1358_, v___x_1360_, v_t_1357_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_inc(v_fallback_1359_);
return v_fallback_1359_;
}
else
{
lean_object* v_val_1362_; 
v_val_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref(v___x_1361_);
return v_val_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLED___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_00_u03b2_1364_, lean_object* v_cmp_1365_, lean_object* v_t_1366_, lean_object* v_k_1367_, lean_object* v_fallback_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Std_TreeMap_Raw_getKeyLED(v_00_u03b1_1363_, v_00_u03b2_1364_, v_cmp_1365_, v_t_1366_, v_k_1367_, v_fallback_1368_);
lean_dec(v_fallback_1368_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___redArg(lean_object* v_cmp_1370_, lean_object* v_t_1371_, lean_object* v_k_1372_, lean_object* v_fallback_1373_){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1370_, v_k_1372_, v___x_1374_, v_t_1371_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_inc(v_fallback_1373_);
return v_fallback_1373_;
}
else
{
lean_object* v_val_1376_; 
v_val_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_val_1376_);
lean_dec_ref(v___x_1375_);
return v_val_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___redArg___boxed(lean_object* v_cmp_1377_, lean_object* v_t_1378_, lean_object* v_k_1379_, lean_object* v_fallback_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_TreeMap_Raw_getKeyLTD___redArg(v_cmp_1377_, v_t_1378_, v_k_1379_, v_fallback_1380_);
lean_dec(v_fallback_1380_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD(lean_object* v_00_u03b1_1382_, lean_object* v_00_u03b2_1383_, lean_object* v_cmp_1384_, lean_object* v_t_1385_, lean_object* v_k_1386_, lean_object* v_fallback_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_box(0);
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1384_, v_k_1386_, v___x_1388_, v_t_1385_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_inc(v_fallback_1387_);
return v_fallback_1387_;
}
else
{
lean_object* v_val_1390_; 
v_val_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_val_1390_);
lean_dec_ref(v___x_1389_);
return v_val_1390_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_getKeyLTD___boxed(lean_object* v_00_u03b1_1391_, lean_object* v_00_u03b2_1392_, lean_object* v_cmp_1393_, lean_object* v_t_1394_, lean_object* v_k_1395_, lean_object* v_fallback_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Std_TreeMap_Raw_getKeyLTD(v_00_u03b1_1391_, v_00_u03b2_1392_, v_cmp_1393_, v_t_1394_, v_k_1395_, v_fallback_1396_);
lean_dec(v_fallback_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter___redArg(lean_object* v_f_1398_, lean_object* v_t_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_1398_, v_t_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter(lean_object* v_00_u03b1_1401_, lean_object* v_00_u03b2_1402_, lean_object* v_cmp_1403_, lean_object* v_f_1404_, lean_object* v_t_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_1404_, v_t_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filter___boxed(lean_object* v_00_u03b1_1407_, lean_object* v_00_u03b2_1408_, lean_object* v_cmp_1409_, lean_object* v_f_1410_, lean_object* v_t_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Std_TreeMap_Raw_filter(v_00_u03b1_1407_, v_00_u03b2_1408_, v_cmp_1409_, v_f_1410_, v_t_1411_);
lean_dec_ref(v_cmp_1409_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM___redArg(lean_object* v_inst_1413_, lean_object* v_f_1414_, lean_object* v_init_1415_, lean_object* v_t_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1413_, v_f_1414_, v_init_1415_, v_t_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM(lean_object* v_00_u03b1_1418_, lean_object* v_00_u03b2_1419_, lean_object* v_cmp_1420_, lean_object* v_00_u03b4_1421_, lean_object* v_m_1422_, lean_object* v_inst_1423_, lean_object* v_f_1424_, lean_object* v_init_1425_, lean_object* v_t_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1423_, v_f_1424_, v_init_1425_, v_t_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldlM___boxed(lean_object* v_00_u03b1_1428_, lean_object* v_00_u03b2_1429_, lean_object* v_cmp_1430_, lean_object* v_00_u03b4_1431_, lean_object* v_m_1432_, lean_object* v_inst_1433_, lean_object* v_f_1434_, lean_object* v_init_1435_, lean_object* v_t_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Std_TreeMap_Raw_foldlM(v_00_u03b1_1428_, v_00_u03b2_1429_, v_cmp_1430_, v_00_u03b4_1431_, v_m_1432_, v_inst_1433_, v_f_1434_, v_init_1435_, v_t_1436_);
lean_dec_ref(v_cmp_1430_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl___redArg(lean_object* v_f_1438_, lean_object* v_init_1439_, lean_object* v_t_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1438_, v_init_1439_, v_t_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl(lean_object* v_00_u03b1_1442_, lean_object* v_00_u03b2_1443_, lean_object* v_cmp_1444_, lean_object* v_00_u03b4_1445_, lean_object* v_f_1446_, lean_object* v_init_1447_, lean_object* v_t_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1446_, v_init_1447_, v_t_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldl___boxed(lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_cmp_1452_, lean_object* v_00_u03b4_1453_, lean_object* v_f_1454_, lean_object* v_init_1455_, lean_object* v_t_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Std_TreeMap_Raw_foldl(v_00_u03b1_1450_, v_00_u03b2_1451_, v_cmp_1452_, v_00_u03b4_1453_, v_f_1454_, v_init_1455_, v_t_1456_);
lean_dec_ref(v_cmp_1452_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM___redArg(lean_object* v_inst_1458_, lean_object* v_f_1459_, lean_object* v_init_1460_, lean_object* v_t_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1458_, v_f_1459_, v_init_1460_, v_t_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM(lean_object* v_00_u03b1_1463_, lean_object* v_00_u03b2_1464_, lean_object* v_cmp_1465_, lean_object* v_00_u03b4_1466_, lean_object* v_m_1467_, lean_object* v_inst_1468_, lean_object* v_f_1469_, lean_object* v_init_1470_, lean_object* v_t_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1468_, v_f_1469_, v_init_1470_, v_t_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldrM___boxed(lean_object* v_00_u03b1_1473_, lean_object* v_00_u03b2_1474_, lean_object* v_cmp_1475_, lean_object* v_00_u03b4_1476_, lean_object* v_m_1477_, lean_object* v_inst_1478_, lean_object* v_f_1479_, lean_object* v_init_1480_, lean_object* v_t_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Std_TreeMap_Raw_foldrM(v_00_u03b1_1473_, v_00_u03b2_1474_, v_cmp_1475_, v_00_u03b4_1476_, v_m_1477_, v_inst_1478_, v_f_1479_, v_init_1480_, v_t_1481_);
lean_dec_ref(v_cmp_1475_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___redArg___lam__0(lean_object* v_f_1483_, lean_object* v_x1_1484_, lean_object* v_x2_1485_, lean_object* v_x3_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_apply_3(v_f_1483_, v_x1_1484_, v_x2_1485_, v_x3_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___redArg(lean_object* v_f_1507_, lean_object* v_init_1508_, lean_object* v_t_1509_){
_start:
{
lean_object* v___f_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___f_1510_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1510_, 0, v_f_1507_);
v___x_1511_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1512_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1511_, v___f_1510_, v_init_1508_, v_t_1509_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr(lean_object* v_00_u03b1_1513_, lean_object* v_00_u03b2_1514_, lean_object* v_cmp_1515_, lean_object* v_00_u03b4_1516_, lean_object* v_f_1517_, lean_object* v_init_1518_, lean_object* v_t_1519_){
_start:
{
lean_object* v___f_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___f_1520_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1520_, 0, v_f_1517_);
v___x_1521_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1522_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1521_, v___f_1520_, v_init_1518_, v_t_1519_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_foldr___boxed(lean_object* v_00_u03b1_1523_, lean_object* v_00_u03b2_1524_, lean_object* v_cmp_1525_, lean_object* v_00_u03b4_1526_, lean_object* v_f_1527_, lean_object* v_init_1528_, lean_object* v_t_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Std_TreeMap_Raw_foldr(v_00_u03b1_1523_, v_00_u03b2_1524_, v_cmp_1525_, v_00_u03b4_1526_, v_f_1527_, v_init_1528_, v_t_1529_);
lean_dec_ref(v_cmp_1525_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition___redArg___lam__0(lean_object* v_f_1531_, lean_object* v_cmp_1532_, lean_object* v_x_1533_, lean_object* v_a_1534_, lean_object* v_b_1535_){
_start:
{
lean_object* v_fst_1536_; lean_object* v_snd_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1551_; 
v_fst_1536_ = lean_ctor_get(v_x_1533_, 0);
v_snd_1537_ = lean_ctor_get(v_x_1533_, 1);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_x_1533_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1539_ = v_x_1533_;
v_isShared_1540_ = v_isSharedCheck_1551_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_snd_1537_);
lean_inc(v_fst_1536_);
lean_dec(v_x_1533_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1551_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
lean_inc(v_b_1535_);
lean_inc(v_a_1534_);
v___x_1541_ = lean_apply_2(v_f_1531_, v_a_1534_, v_b_1535_);
v___x_1542_ = lean_unbox(v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1532_, v_a_1534_, v_b_1535_, v_snd_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 1, v___x_1543_);
v___x_1545_ = v___x_1539_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_fst_1536_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1532_, v_a_1534_, v_b_1535_, v_fst_1536_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1547_);
v___x_1549_ = v___x_1539_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_snd_1537_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition___redArg(lean_object* v_cmp_1554_, lean_object* v_f_1555_, lean_object* v_t_1556_){
_start:
{
lean_object* v___f_1557_; lean_object* v___x_1558_; lean_object* v_p_1559_; lean_object* v_fst_1560_; lean_object* v_snd_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v___f_1557_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1557_, 0, v_f_1555_);
lean_closure_set(v___f_1557_, 1, v_cmp_1554_);
v___x_1558_ = ((lean_object*)(l_Std_TreeMap_Raw_partition___redArg___closed__0));
v_p_1559_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1557_, v___x_1558_, v_t_1556_);
v_fst_1560_ = lean_ctor_get(v_p_1559_, 0);
v_snd_1561_ = lean_ctor_get(v_p_1559_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_p_1559_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v_p_1559_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_snd_1561_);
lean_inc(v_fst_1560_);
lean_dec(v_p_1559_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_fst_1560_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_snd_1561_);
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
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_partition(lean_object* v_00_u03b1_1569_, lean_object* v_00_u03b2_1570_, lean_object* v_cmp_1571_, lean_object* v_f_1572_, lean_object* v_t_1573_){
_start:
{
lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v_p_1576_; lean_object* v_fst_1577_; lean_object* v_snd_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
v___f_1574_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1574_, 0, v_f_1572_);
lean_closure_set(v___f_1574_, 1, v_cmp_1571_);
v___x_1575_ = ((lean_object*)(l_Std_TreeMap_Raw_partition___redArg___closed__0));
v_p_1576_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1574_, v___x_1575_, v_t_1573_);
v_fst_1577_ = lean_ctor_get(v_p_1576_, 0);
v_snd_1578_ = lean_ctor_get(v_p_1576_, 1);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_p_1576_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v_p_1576_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_snd_1578_);
lean_inc(v_fst_1577_);
lean_dec(v_p_1576_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_fst_1577_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_snd_1578_);
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
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___redArg___lam__0(lean_object* v_f_1586_, lean_object* v_x_1587_, lean_object* v_k_1588_, lean_object* v_v_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_apply_2(v_f_1586_, v_k_1588_, v_v_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___redArg(lean_object* v_inst_1591_, lean_object* v_f_1592_, lean_object* v_t_1593_){
_start:
{
lean_object* v___f_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___f_1594_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1594_, 0, v_f_1592_);
v___x_1595_ = lean_box(0);
v___x_1596_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1591_, v___f_1594_, v___x_1595_, v_t_1593_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM(lean_object* v_00_u03b1_1597_, lean_object* v_00_u03b2_1598_, lean_object* v_cmp_1599_, lean_object* v_m_1600_, lean_object* v_inst_1601_, lean_object* v_f_1602_, lean_object* v_t_1603_){
_start:
{
lean_object* v___f_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___f_1604_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1604_, 0, v_f_1602_);
v___x_1605_ = lean_box(0);
v___x_1606_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1601_, v___f_1604_, v___x_1605_, v_t_1603_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forM___boxed(lean_object* v_00_u03b1_1607_, lean_object* v_00_u03b2_1608_, lean_object* v_cmp_1609_, lean_object* v_m_1610_, lean_object* v_inst_1611_, lean_object* v_f_1612_, lean_object* v_t_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Std_TreeMap_Raw_forM(v_00_u03b1_1607_, v_00_u03b2_1608_, v_cmp_1609_, v_m_1610_, v_inst_1611_, v_f_1612_, v_t_1613_);
lean_dec_ref(v_cmp_1609_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg___lam__0(lean_object* v_f_1615_, lean_object* v_a_1616_, lean_object* v_b_1617_, lean_object* v_c_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_apply_3(v_f_1615_, v_a_1616_, v_b_1617_, v_c_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg___lam__1(lean_object* v_toPure_1620_, lean_object* v_____do__lift_1621_){
_start:
{
lean_object* v_a_1622_; lean_object* v___x_1623_; 
v_a_1622_ = lean_ctor_get(v_____do__lift_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref(v_____do__lift_1621_);
v___x_1623_ = lean_apply_2(v_toPure_1620_, lean_box(0), v_a_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___redArg(lean_object* v_inst_1624_, lean_object* v_f_1625_, lean_object* v_init_1626_, lean_object* v_t_1627_){
_start:
{
lean_object* v_toApplicative_1628_; lean_object* v_toBind_1629_; lean_object* v_toPure_1630_; lean_object* v___f_1631_; lean_object* v___x_1632_; lean_object* v___f_1633_; lean_object* v___x_1634_; 
v_toApplicative_1628_ = lean_ctor_get(v_inst_1624_, 0);
v_toBind_1629_ = lean_ctor_get(v_inst_1624_, 1);
lean_inc(v_toBind_1629_);
v_toPure_1630_ = lean_ctor_get(v_toApplicative_1628_, 1);
lean_inc(v_toPure_1630_);
v___f_1631_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1631_, 0, v_f_1625_);
v___x_1632_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1624_, v___f_1631_, v_init_1626_, v_t_1627_);
v___f_1633_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1633_, 0, v_toPure_1630_);
v___x_1634_ = lean_apply_4(v_toBind_1629_, lean_box(0), lean_box(0), v___x_1632_, v___f_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn(lean_object* v_00_u03b1_1635_, lean_object* v_00_u03b2_1636_, lean_object* v_cmp_1637_, lean_object* v_00_u03b4_1638_, lean_object* v_m_1639_, lean_object* v_inst_1640_, lean_object* v_f_1641_, lean_object* v_init_1642_, lean_object* v_t_1643_){
_start:
{
lean_object* v_toApplicative_1644_; lean_object* v_toBind_1645_; lean_object* v_toPure_1646_; lean_object* v___f_1647_; lean_object* v___x_1648_; lean_object* v___f_1649_; lean_object* v___x_1650_; 
v_toApplicative_1644_ = lean_ctor_get(v_inst_1640_, 0);
v_toBind_1645_ = lean_ctor_get(v_inst_1640_, 1);
lean_inc(v_toBind_1645_);
v_toPure_1646_ = lean_ctor_get(v_toApplicative_1644_, 1);
lean_inc(v_toPure_1646_);
v___f_1647_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1647_, 0, v_f_1641_);
v___x_1648_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1640_, v___f_1647_, v_init_1642_, v_t_1643_);
v___f_1649_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1649_, 0, v_toPure_1646_);
v___x_1650_ = lean_apply_4(v_toBind_1645_, lean_box(0), lean_box(0), v___x_1648_, v___f_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_forIn___boxed(lean_object* v_00_u03b1_1651_, lean_object* v_00_u03b2_1652_, lean_object* v_cmp_1653_, lean_object* v_00_u03b4_1654_, lean_object* v_m_1655_, lean_object* v_inst_1656_, lean_object* v_f_1657_, lean_object* v_init_1658_, lean_object* v_t_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Std_TreeMap_Raw_forIn(v_00_u03b1_1651_, v_00_u03b2_1652_, v_cmp_1653_, v_00_u03b4_1654_, v_m_1655_, v_inst_1656_, v_f_1657_, v_init_1658_, v_t_1659_);
lean_dec_ref(v_cmp_1653_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1661_, lean_object* v_x_1662_, lean_object* v_k_1663_, lean_object* v_v_1664_){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v_k_1663_);
lean_ctor_set(v___x_1665_, 1, v_v_1664_);
v___x_1666_ = lean_apply_1(v_f_1661_, v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_1667_, lean_object* v_t_1668_, lean_object* v_f_1669_){
_start:
{
lean_object* v___f_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___f_1670_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1670_, 0, v_f_1669_);
v___x_1671_ = lean_box(0);
v___x_1672_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1667_, v___f_1670_, v___x_1671_, v_t_1668_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___redArg(lean_object* v_inst_1673_){
_start:
{
lean_object* v___f_1674_; 
v___f_1674_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1674_, 0, v_inst_1673_);
return v___f_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad(lean_object* v_00_u03b1_1675_, lean_object* v_00_u03b2_1676_, lean_object* v_cmp_1677_, lean_object* v_m_1678_, lean_object* v_inst_1679_){
_start:
{
lean_object* v___f_1680_; 
v___f_1680_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1680_, 0, v_inst_1679_);
return v___f_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_cmp_1683_, lean_object* v_m_1684_, lean_object* v_inst_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Std_TreeMap_Raw_instForMProdOfMonad(v_00_u03b1_1681_, v_00_u03b2_1682_, v_cmp_1683_, v_m_1684_, v_inst_1685_);
lean_dec_ref(v_cmp_1683_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1687_, lean_object* v_a_1688_, lean_object* v_b_1689_, lean_object* v_c_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_a_1688_);
lean_ctor_set(v___x_1691_, 1, v_b_1689_);
v___x_1692_ = lean_apply_2(v_f_1687_, v___x_1691_, v_c_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1693_, lean_object* v_00_u03b2_1694_, lean_object* v_t_1695_, lean_object* v_init_1696_, lean_object* v_f_1697_){
_start:
{
lean_object* v_toApplicative_1698_; lean_object* v_toBind_1699_; lean_object* v_toPure_1700_; lean_object* v___f_1701_; lean_object* v___x_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; 
v_toApplicative_1698_ = lean_ctor_get(v_inst_1693_, 0);
v_toBind_1699_ = lean_ctor_get(v_inst_1693_, 1);
lean_inc(v_toBind_1699_);
v_toPure_1700_ = lean_ctor_get(v_toApplicative_1698_, 1);
lean_inc(v_toPure_1700_);
v___f_1701_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1701_, 0, v_f_1697_);
v___x_1702_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1693_, v___f_1701_, v_init_1696_, v_t_1695_);
v___f_1703_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1703_, 0, v_toPure_1700_);
v___x_1704_ = lean_apply_4(v_toBind_1699_, lean_box(0), lean_box(0), v___x_1702_, v___f_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___redArg(lean_object* v_inst_1705_){
_start:
{
lean_object* v___f_1706_; 
v___f_1706_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1706_, 0, v_inst_1705_);
return v___f_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad(lean_object* v_00_u03b1_1707_, lean_object* v_00_u03b2_1708_, lean_object* v_cmp_1709_, lean_object* v_m_1710_, lean_object* v_inst_1711_){
_start:
{
lean_object* v___f_1712_; 
v___f_1712_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1712_, 0, v_inst_1711_);
return v___f_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_cmp_1715_, lean_object* v_m_1716_, lean_object* v_inst_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Std_TreeMap_Raw_instForInProdOfMonad(v_00_u03b1_1713_, v_00_u03b2_1714_, v_cmp_1715_, v_m_1716_, v_inst_1717_);
lean_dec_ref(v_cmp_1715_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___lam__0(lean_object* v_p_1719_, lean_object* v___x_1720_, lean_object* v___x_1721_, lean_object* v_a_1722_, lean_object* v_b_1723_, lean_object* v_acc_1724_){
_start:
{
lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = lean_apply_2(v_p_1719_, v_a_1722_, v_b_1723_);
v___x_1726_ = lean_unbox(v___x_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1720_);
return v___x_1727_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec_ref(v___x_1720_);
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1725_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v___x_1721_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1731_, lean_object* v___x_1732_, lean_object* v___x_1733_, lean_object* v_a_1734_, lean_object* v_b_1735_, lean_object* v_acc_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Std_TreeMap_Raw_any___redArg___lam__0(v_p_1731_, v___x_1732_, v___x_1733_, v_a_1734_, v_b_1735_, v_acc_1736_);
lean_dec_ref(v_acc_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_any___redArg(lean_object* v_t_1741_, lean_object* v_p_1742_){
_start:
{
lean_object* v___y_1744_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; lean_object* v_a_1754_; 
v___x_1749_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1750_ = lean_box(0);
v___x_1751_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1752_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1752_, 0, v_p_1742_);
lean_closure_set(v___f_1752_, 1, v___x_1751_);
lean_closure_set(v___f_1752_, 2, v___x_1750_);
v___x_1753_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1749_, v___f_1752_, v___x_1751_, v_t_1741_);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___y_1744_ = v_a_1754_;
goto v___jp_1743_;
v___jp_1743_:
{
lean_object* v_fst_1745_; 
v_fst_1745_ = lean_ctor_get(v___y_1744_, 0);
lean_inc(v_fst_1745_);
lean_dec_ref(v___y_1744_);
if (lean_obj_tag(v_fst_1745_) == 0)
{
uint8_t v___x_1746_; 
v___x_1746_ = 0;
return v___x_1746_;
}
else
{
lean_object* v_val_1747_; uint8_t v___x_1748_; 
v_val_1747_ = lean_ctor_get(v_fst_1745_, 0);
lean_inc(v_val_1747_);
lean_dec_ref(v_fst_1745_);
v___x_1748_ = lean_unbox(v_val_1747_);
lean_dec(v_val_1747_);
return v___x_1748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___redArg___boxed(lean_object* v_t_1755_, lean_object* v_p_1756_){
_start:
{
uint8_t v_res_1757_; lean_object* v_r_1758_; 
v_res_1757_ = l_Std_TreeMap_Raw_any___redArg(v_t_1755_, v_p_1756_);
v_r_1758_ = lean_box(v_res_1757_);
return v_r_1758_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_any(lean_object* v_00_u03b1_1759_, lean_object* v_00_u03b2_1760_, lean_object* v_cmp_1761_, lean_object* v_t_1762_, lean_object* v_p_1763_){
_start:
{
lean_object* v___y_1765_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v_a_1775_; 
v___x_1770_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1771_ = lean_box(0);
v___x_1772_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1773_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1773_, 0, v_p_1763_);
lean_closure_set(v___f_1773_, 1, v___x_1772_);
lean_closure_set(v___f_1773_, 2, v___x_1771_);
v___x_1774_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1770_, v___f_1773_, v___x_1772_, v_t_1762_);
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___y_1765_ = v_a_1775_;
goto v___jp_1764_;
v___jp_1764_:
{
lean_object* v_fst_1766_; 
v_fst_1766_ = lean_ctor_get(v___y_1765_, 0);
lean_inc(v_fst_1766_);
lean_dec_ref(v___y_1765_);
if (lean_obj_tag(v_fst_1766_) == 0)
{
uint8_t v___x_1767_; 
v___x_1767_ = 0;
return v___x_1767_;
}
else
{
lean_object* v_val_1768_; uint8_t v___x_1769_; 
v_val_1768_ = lean_ctor_get(v_fst_1766_, 0);
lean_inc(v_val_1768_);
lean_dec_ref(v_fst_1766_);
v___x_1769_ = lean_unbox(v_val_1768_);
lean_dec(v_val_1768_);
return v___x_1769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_any___boxed(lean_object* v_00_u03b1_1776_, lean_object* v_00_u03b2_1777_, lean_object* v_cmp_1778_, lean_object* v_t_1779_, lean_object* v_p_1780_){
_start:
{
uint8_t v_res_1781_; lean_object* v_r_1782_; 
v_res_1781_ = l_Std_TreeMap_Raw_any(v_00_u03b1_1776_, v_00_u03b2_1777_, v_cmp_1778_, v_t_1779_, v_p_1780_);
lean_dec_ref(v_cmp_1778_);
v_r_1782_ = lean_box(v_res_1781_);
return v_r_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___lam__0(lean_object* v_p_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v_a_1786_, lean_object* v_b_1787_, lean_object* v_acc_1788_){
_start:
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = lean_apply_2(v_p_1783_, v_a_1786_, v_b_1787_);
v___x_1790_ = lean_unbox(v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec_ref(v___x_1785_);
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
lean_ctor_set(v___x_1792_, 1, v___x_1784_);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1785_);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1795_, lean_object* v___x_1796_, lean_object* v___x_1797_, lean_object* v_a_1798_, lean_object* v_b_1799_, lean_object* v_acc_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Std_TreeMap_Raw_all___redArg___lam__0(v_p_1795_, v___x_1796_, v___x_1797_, v_a_1798_, v_b_1799_, v_acc_1800_);
lean_dec_ref(v_acc_1800_);
return v_res_1801_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_all___redArg(lean_object* v_t_1802_, lean_object* v_p_1803_){
_start:
{
lean_object* v___y_1805_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___f_1813_; lean_object* v___x_1814_; lean_object* v_a_1815_; 
v___x_1810_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1811_ = lean_box(0);
v___x_1812_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1813_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1813_, 0, v_p_1803_);
lean_closure_set(v___f_1813_, 1, v___x_1811_);
lean_closure_set(v___f_1813_, 2, v___x_1812_);
v___x_1814_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1810_, v___f_1813_, v___x_1812_, v_t_1802_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___y_1805_ = v_a_1815_;
goto v___jp_1804_;
v___jp_1804_:
{
lean_object* v_fst_1806_; 
v_fst_1806_ = lean_ctor_get(v___y_1805_, 0);
lean_inc(v_fst_1806_);
lean_dec_ref(v___y_1805_);
if (lean_obj_tag(v_fst_1806_) == 0)
{
uint8_t v___x_1807_; 
v___x_1807_ = 1;
return v___x_1807_;
}
else
{
lean_object* v_val_1808_; uint8_t v___x_1809_; 
v_val_1808_ = lean_ctor_get(v_fst_1806_, 0);
lean_inc(v_val_1808_);
lean_dec_ref(v_fst_1806_);
v___x_1809_ = lean_unbox(v_val_1808_);
lean_dec(v_val_1808_);
return v___x_1809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___redArg___boxed(lean_object* v_t_1816_, lean_object* v_p_1817_){
_start:
{
uint8_t v_res_1818_; lean_object* v_r_1819_; 
v_res_1818_ = l_Std_TreeMap_Raw_all___redArg(v_t_1816_, v_p_1817_);
v_r_1819_ = lean_box(v_res_1818_);
return v_r_1819_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_all(lean_object* v_00_u03b1_1820_, lean_object* v_00_u03b2_1821_, lean_object* v_cmp_1822_, lean_object* v_t_1823_, lean_object* v_p_1824_){
_start:
{
lean_object* v___y_1826_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___f_1834_; lean_object* v___x_1835_; lean_object* v_a_1836_; 
v___x_1831_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1832_ = lean_box(0);
v___x_1833_ = ((lean_object*)(l_Std_TreeMap_Raw_any___redArg___closed__0));
v___f_1834_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1834_, 0, v_p_1824_);
lean_closure_set(v___f_1834_, 1, v___x_1832_);
lean_closure_set(v___f_1834_, 2, v___x_1833_);
v___x_1835_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1831_, v___f_1834_, v___x_1833_, v_t_1823_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___y_1826_ = v_a_1836_;
goto v___jp_1825_;
v___jp_1825_:
{
lean_object* v_fst_1827_; 
v_fst_1827_ = lean_ctor_get(v___y_1826_, 0);
lean_inc(v_fst_1827_);
lean_dec_ref(v___y_1826_);
if (lean_obj_tag(v_fst_1827_) == 0)
{
uint8_t v___x_1828_; 
v___x_1828_ = 1;
return v___x_1828_;
}
else
{
lean_object* v_val_1829_; uint8_t v___x_1830_; 
v_val_1829_ = lean_ctor_get(v_fst_1827_, 0);
lean_inc(v_val_1829_);
lean_dec_ref(v_fst_1827_);
v___x_1830_ = lean_unbox(v_val_1829_);
lean_dec(v_val_1829_);
return v___x_1830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_all___boxed(lean_object* v_00_u03b1_1837_, lean_object* v_00_u03b2_1838_, lean_object* v_cmp_1839_, lean_object* v_t_1840_, lean_object* v_p_1841_){
_start:
{
uint8_t v_res_1842_; lean_object* v_r_1843_; 
v_res_1842_ = l_Std_TreeMap_Raw_all(v_00_u03b1_1837_, v_00_u03b2_1838_, v_cmp_1839_, v_t_1840_, v_p_1841_);
lean_dec_ref(v_cmp_1839_);
v_r_1843_ = lean_box(v_res_1842_);
return v_r_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg___lam__0(lean_object* v_x1_1844_, lean_object* v_x2_1845_, lean_object* v_x3_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_x1_1844_);
lean_ctor_set(v___x_1847_, 1, v_x3_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_x1_1848_, lean_object* v_x2_1849_, lean_object* v_x3_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Std_TreeMap_Raw_keys___redArg___lam__0(v_x1_1848_, v_x2_1849_, v_x3_1850_);
lean_dec(v_x2_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___redArg(lean_object* v_t_1853_){
_start:
{
lean_object* v___f_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___f_1854_ = ((lean_object*)(l_Std_TreeMap_Raw_keys___redArg___closed__0));
v___x_1855_ = lean_box(0);
v___x_1856_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1856_, v___f_1854_, v___x_1855_, v_t_1853_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys(lean_object* v_00_u03b1_1858_, lean_object* v_00_u03b2_1859_, lean_object* v_cmp_1860_, lean_object* v_t_1861_){
_start:
{
lean_object* v___f_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___f_1862_ = ((lean_object*)(l_Std_TreeMap_Raw_keys___redArg___closed__0));
v___x_1863_ = lean_box(0);
v___x_1864_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1865_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1864_, v___f_1862_, v___x_1863_, v_t_1861_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keys___boxed(lean_object* v_00_u03b1_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_cmp_1868_, lean_object* v_t_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Std_TreeMap_Raw_keys(v_00_u03b1_1866_, v_00_u03b2_1867_, v_cmp_1868_, v_t_1869_);
lean_dec_ref(v_cmp_1868_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg___lam__0(lean_object* v_l_1871_, lean_object* v_k_1872_, lean_object* v_x_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_array_push(v_l_1871_, v_k_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_l_1875_, lean_object* v_k_1876_, lean_object* v_x_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Std_TreeMap_Raw_keysArray___redArg___lam__0(v_l_1875_, v_k_1876_, v_x_1877_);
lean_dec(v_x_1877_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___redArg(lean_object* v_t_1880_){
_start:
{
lean_object* v___f_1881_; lean_object* v___y_1883_; 
v___f_1881_ = ((lean_object*)(l_Std_TreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1880_) == 0)
{
lean_object* v_size_1886_; 
v_size_1886_ = lean_ctor_get(v_t_1880_, 0);
lean_inc(v_size_1886_);
v___y_1883_ = v_size_1886_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_unsigned_to_nat(0u);
v___y_1883_ = v___x_1887_;
goto v___jp_1882_;
}
v___jp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_mk_empty_array_with_capacity(v___y_1883_);
lean_dec(v___y_1883_);
v___x_1885_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1881_, v___x_1884_, v_t_1880_);
return v___x_1885_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray(lean_object* v_00_u03b1_1888_, lean_object* v_00_u03b2_1889_, lean_object* v_cmp_1890_, lean_object* v_t_1891_){
_start:
{
lean_object* v___f_1892_; lean_object* v___y_1894_; 
v___f_1892_ = ((lean_object*)(l_Std_TreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1891_) == 0)
{
lean_object* v_size_1897_; 
v_size_1897_ = lean_ctor_get(v_t_1891_, 0);
lean_inc(v_size_1897_);
v___y_1894_ = v_size_1897_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_unsigned_to_nat(0u);
v___y_1894_ = v___x_1898_;
goto v___jp_1893_;
}
v___jp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_mk_empty_array_with_capacity(v___y_1894_);
lean_dec(v___y_1894_);
v___x_1896_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1892_, v___x_1895_, v_t_1891_);
return v___x_1896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_keysArray___boxed(lean_object* v_00_u03b1_1899_, lean_object* v_00_u03b2_1900_, lean_object* v_cmp_1901_, lean_object* v_t_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Std_TreeMap_Raw_keysArray(v_00_u03b1_1899_, v_00_u03b2_1900_, v_cmp_1901_, v_t_1902_);
lean_dec_ref(v_cmp_1901_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg___lam__0(lean_object* v_x1_1904_, lean_object* v_x2_1905_, lean_object* v_x3_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1907_, 0, v_x2_1905_);
lean_ctor_set(v___x_1907_, 1, v_x3_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg___lam__0___boxed(lean_object* v_x1_1908_, lean_object* v_x2_1909_, lean_object* v_x3_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Std_TreeMap_Raw_values___redArg___lam__0(v_x1_1908_, v_x2_1909_, v_x3_1910_);
lean_dec(v_x1_1908_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___redArg(lean_object* v_t_1913_){
_start:
{
lean_object* v___f_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___f_1914_ = ((lean_object*)(l_Std_TreeMap_Raw_values___redArg___closed__0));
v___x_1915_ = lean_box(0);
v___x_1916_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1917_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1916_, v___f_1914_, v___x_1915_, v_t_1913_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values(lean_object* v_00_u03b1_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_cmp_1920_, lean_object* v_t_1921_){
_start:
{
lean_object* v___f_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___f_1922_ = ((lean_object*)(l_Std_TreeMap_Raw_values___redArg___closed__0));
v___x_1923_ = lean_box(0);
v___x_1924_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1925_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1924_, v___f_1922_, v___x_1923_, v_t_1921_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_values___boxed(lean_object* v_00_u03b1_1926_, lean_object* v_00_u03b2_1927_, lean_object* v_cmp_1928_, lean_object* v_t_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Std_TreeMap_Raw_values(v_00_u03b1_1926_, v_00_u03b2_1927_, v_cmp_1928_, v_t_1929_);
lean_dec_ref(v_cmp_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg___lam__0(lean_object* v_l_1931_, lean_object* v_x_1932_, lean_object* v_v_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_array_push(v_l_1931_, v_v_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_l_1935_, lean_object* v_x_1936_, lean_object* v_v_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Std_TreeMap_Raw_valuesArray___redArg___lam__0(v_l_1935_, v_x_1936_, v_v_1937_);
lean_dec(v_x_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___redArg(lean_object* v_t_1940_){
_start:
{
lean_object* v___f_1941_; lean_object* v___y_1943_; 
v___f_1941_ = ((lean_object*)(l_Std_TreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1940_) == 0)
{
lean_object* v_size_1946_; 
v_size_1946_ = lean_ctor_get(v_t_1940_, 0);
lean_inc(v_size_1946_);
v___y_1943_ = v_size_1946_;
goto v___jp_1942_;
}
else
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_unsigned_to_nat(0u);
v___y_1943_ = v___x_1947_;
goto v___jp_1942_;
}
v___jp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_mk_empty_array_with_capacity(v___y_1943_);
lean_dec(v___y_1943_);
v___x_1945_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1941_, v___x_1944_, v_t_1940_);
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray(lean_object* v_00_u03b1_1948_, lean_object* v_00_u03b2_1949_, lean_object* v_cmp_1950_, lean_object* v_t_1951_){
_start:
{
lean_object* v___f_1952_; lean_object* v___y_1954_; 
v___f_1952_ = ((lean_object*)(l_Std_TreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1951_) == 0)
{
lean_object* v_size_1957_; 
v_size_1957_ = lean_ctor_get(v_t_1951_, 0);
lean_inc(v_size_1957_);
v___y_1954_ = v_size_1957_;
goto v___jp_1953_;
}
else
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_unsigned_to_nat(0u);
v___y_1954_ = v___x_1958_;
goto v___jp_1953_;
}
v___jp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_mk_empty_array_with_capacity(v___y_1954_);
lean_dec(v___y_1954_);
v___x_1956_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1952_, v___x_1955_, v_t_1951_);
return v___x_1956_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_valuesArray___boxed(lean_object* v_00_u03b1_1959_, lean_object* v_00_u03b2_1960_, lean_object* v_cmp_1961_, lean_object* v_t_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Std_TreeMap_Raw_valuesArray(v_00_u03b1_1959_, v_00_u03b2_1960_, v_cmp_1961_, v_t_1962_);
lean_dec_ref(v_cmp_1961_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___redArg___lam__0(lean_object* v_x1_1964_, lean_object* v_x2_1965_, lean_object* v_x3_1966_){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_x1_1964_);
lean_ctor_set(v___x_1967_, 1, v_x2_1965_);
v___x_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v_x3_1966_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___redArg(lean_object* v_t_1970_){
_start:
{
lean_object* v___f_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___f_1971_ = ((lean_object*)(l_Std_TreeMap_Raw_toList___redArg___closed__0));
v___x_1972_ = lean_box(0);
v___x_1973_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1974_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1973_, v___f_1971_, v___x_1972_, v_t_1970_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList(lean_object* v_00_u03b1_1975_, lean_object* v_00_u03b2_1976_, lean_object* v_cmp_1977_, lean_object* v_t_1978_){
_start:
{
lean_object* v___f_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___f_1979_ = ((lean_object*)(l_Std_TreeMap_Raw_toList___redArg___closed__0));
v___x_1980_ = lean_box(0);
v___x_1981_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_1982_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1981_, v___f_1979_, v___x_1980_, v_t_1978_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList___boxed(lean_object* v_00_u03b1_1983_, lean_object* v_00_u03b2_1984_, lean_object* v_cmp_1985_, lean_object* v_t_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Std_TreeMap_Raw_toList(v_00_u03b1_1983_, v_00_u03b2_1984_, v_cmp_1985_, v_t_1986_);
lean_dec_ref(v_cmp_1985_);
return v_res_1987_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__26, &l_Std_TreeMap_Raw___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw___auto__1___closed__26);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___redArg___lam__0(lean_object* v_cmp_1989_, lean_object* v_a_1990_, lean_object* v_x_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_fst_1993_; lean_object* v_snd_1994_; lean_object* v_r_1995_; lean_object* v___x_1996_; 
v_fst_1993_ = lean_ctor_get(v_a_1990_, 0);
lean_inc(v_fst_1993_);
v_snd_1994_ = lean_ctor_get(v_a_1990_, 1);
lean_inc(v_snd_1994_);
lean_dec_ref(v_a_1990_);
v_r_1995_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1989_, v_fst_1993_, v_snd_1994_, v___y_1992_);
v___x_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1996_, 0, v_r_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList___redArg(lean_object* v_l_1997_, lean_object* v_cmp_1998_){
_start:
{
lean_object* v___f_1999_; lean_object* v___x_2000_; lean_object* v_r_2001_; lean_object* v___x_2002_; 
v___f_1999_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1999_, 0, v_cmp_1998_);
v___x_2000_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2001_ = lean_box(1);
v___x_2002_ = l_List_forIn_x27_loop___redArg(v___x_2000_, v___f_1999_, v_l_1997_, v_r_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofList(lean_object* v_00_u03b1_2003_, lean_object* v_00_u03b2_2004_, lean_object* v_l_2005_, lean_object* v_cmp_2006_){
_start:
{
lean_object* v___f_2007_; lean_object* v___x_2008_; lean_object* v_r_2009_; lean_object* v___x_2010_; 
v___f_2007_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2007_, 0, v_cmp_2006_);
v___x_2008_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2009_ = lean_box(1);
v___x_2010_ = l_List_forIn_x27_loop___redArg(v___x_2008_, v___f_2007_, v_l_2005_, v_r_2009_);
return v___x_2010_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__26, &l_Std_TreeMap_Raw___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw___auto__1___closed__26);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg___lam__0(lean_object* v_cmp_2012_, lean_object* v_a_2013_, lean_object* v_x_2014_, lean_object* v___y_2015_){
_start:
{
uint8_t v___x_2016_; 
lean_inc(v___y_2015_);
lean_inc(v_a_2013_);
lean_inc_ref(v_cmp_2012_);
v___x_2016_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2012_, v_a_2013_, v___y_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_box(0);
v___x_2018_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2012_, v_a_2013_, v___x_2017_, v___y_2015_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; 
lean_dec(v_a_2013_);
lean_dec_ref(v_cmp_2012_);
v___x_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___y_2015_);
return v___x_2020_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList___redArg(lean_object* v_l_2021_, lean_object* v_cmp_2022_){
_start:
{
lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v_r_2025_; lean_object* v___x_2026_; 
v___f_2023_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2023_, 0, v_cmp_2022_);
v___x_2024_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2025_ = lean_box(1);
v___x_2026_ = l_List_forIn_x27_loop___redArg(v___x_2024_, v___f_2023_, v_l_2021_, v_r_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfList(lean_object* v_00_u03b1_2027_, lean_object* v_l_2028_, lean_object* v_cmp_2029_){
_start:
{
lean_object* v___f_2030_; lean_object* v___x_2031_; lean_object* v_r_2032_; lean_object* v___x_2033_; 
v___f_2030_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2030_, 0, v_cmp_2029_);
v___x_2031_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2032_ = lean_box(1);
v___x_2033_ = l_List_forIn_x27_loop___redArg(v___x_2031_, v___f_2030_, v_l_2028_, v_r_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___redArg___lam__0(lean_object* v_l_2034_, lean_object* v_k_2035_, lean_object* v_v_2036_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v_k_2035_);
lean_ctor_set(v___x_2037_, 1, v_v_2036_);
v___x_2038_ = lean_array_push(v_l_2034_, v___x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___redArg(lean_object* v_t_2040_){
_start:
{
lean_object* v___f_2041_; lean_object* v___y_2043_; 
v___f_2041_ = ((lean_object*)(l_Std_TreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2040_) == 0)
{
lean_object* v_size_2046_; 
v_size_2046_ = lean_ctor_get(v_t_2040_, 0);
lean_inc(v_size_2046_);
v___y_2043_ = v_size_2046_;
goto v___jp_2042_;
}
else
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_unsigned_to_nat(0u);
v___y_2043_ = v___x_2047_;
goto v___jp_2042_;
}
v___jp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_mk_empty_array_with_capacity(v___y_2043_);
lean_dec(v___y_2043_);
v___x_2045_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2041_, v___x_2044_, v_t_2040_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray(lean_object* v_00_u03b1_2048_, lean_object* v_00_u03b2_2049_, lean_object* v_cmp_2050_, lean_object* v_t_2051_){
_start:
{
lean_object* v___f_2052_; lean_object* v___y_2054_; 
v___f_2052_ = ((lean_object*)(l_Std_TreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2051_) == 0)
{
lean_object* v_size_2057_; 
v_size_2057_ = lean_ctor_get(v_t_2051_, 0);
lean_inc(v_size_2057_);
v___y_2054_ = v_size_2057_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_unsigned_to_nat(0u);
v___y_2054_ = v___x_2058_;
goto v___jp_2053_;
}
v___jp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_mk_empty_array_with_capacity(v___y_2054_);
lean_dec(v___y_2054_);
v___x_2056_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2052_, v___x_2055_, v_t_2051_);
return v___x_2056_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toArray___boxed(lean_object* v_00_u03b1_2059_, lean_object* v_00_u03b2_2060_, lean_object* v_cmp_2061_, lean_object* v_t_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Std_TreeMap_Raw_toArray(v_00_u03b1_2059_, v_00_u03b2_2060_, v_cmp_2061_, v_t_2062_);
lean_dec_ref(v_cmp_2061_);
return v_res_2063_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__26, &l_Std_TreeMap_Raw___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw___auto__1___closed__26);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofArray___redArg(lean_object* v_a_2065_, lean_object* v_cmp_2066_){
_start:
{
lean_object* v___f_2067_; lean_object* v___x_2068_; lean_object* v_r_2069_; size_t v_sz_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
v___f_2067_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2067_, 0, v_cmp_2066_);
v___x_2068_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2069_ = lean_box(1);
v_sz_2070_ = lean_array_size(v_a_2065_);
v___x_2071_ = ((size_t)0ULL);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2068_, v_a_2065_, v___f_2067_, v_sz_2070_, v___x_2071_, v_r_2069_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_ofArray(lean_object* v_00_u03b1_2073_, lean_object* v_00_u03b2_2074_, lean_object* v_a_2075_, lean_object* v_cmp_2076_){
_start:
{
lean_object* v___f_2077_; lean_object* v___x_2078_; lean_object* v_r_2079_; size_t v_sz_2080_; size_t v___x_2081_; lean_object* v___x_2082_; 
v___f_2077_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2077_, 0, v_cmp_2076_);
v___x_2078_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2079_ = lean_box(1);
v_sz_2080_ = lean_array_size(v_a_2075_);
v___x_2081_ = ((size_t)0ULL);
v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2078_, v_a_2075_, v___f_2077_, v_sz_2080_, v___x_2081_, v_r_2079_);
return v___x_2082_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_obj_once(&l_Std_TreeMap_Raw___auto__1___closed__26, &l_Std_TreeMap_Raw___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw___auto__1___closed__26);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfArray___redArg(lean_object* v_a_2084_, lean_object* v_cmp_2085_){
_start:
{
lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v_r_2088_; size_t v_sz_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v___f_2086_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2086_, 0, v_cmp_2085_);
v___x_2087_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2088_ = lean_box(1);
v_sz_2089_ = lean_array_size(v_a_2084_);
v___x_2090_ = ((size_t)0ULL);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2087_, v_a_2084_, v___f_2086_, v_sz_2089_, v___x_2090_, v_r_2088_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_unitOfArray(lean_object* v_00_u03b1_2092_, lean_object* v_a_2093_, lean_object* v_cmp_2094_){
_start:
{
lean_object* v___f_2095_; lean_object* v___x_2096_; lean_object* v_r_2097_; size_t v_sz_2098_; size_t v___x_2099_; lean_object* v___x_2100_; 
v___f_2095_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2095_, 0, v_cmp_2094_);
v___x_2096_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v_r_2097_ = lean_box(1);
v_sz_2098_ = lean_array_size(v_a_2093_);
v___x_2099_ = ((size_t)0ULL);
v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2096_, v_a_2093_, v___f_2095_, v_sz_2098_, v___x_2099_, v_r_2097_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_modify___redArg(lean_object* v_cmp_2101_, lean_object* v_t_2102_, lean_object* v_a_2103_, lean_object* v_f_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2101_, v_a_2103_, v_f_2104_, v_t_2102_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_modify(lean_object* v_00_u03b1_2106_, lean_object* v_00_u03b2_2107_, lean_object* v_cmp_2108_, lean_object* v_t_2109_, lean_object* v_a_2110_, lean_object* v_f_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2108_, v_a_2110_, v_f_2111_, v_t_2109_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_alter___redArg(lean_object* v_cmp_2113_, lean_object* v_t_2114_, lean_object* v_a_2115_, lean_object* v_f_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2113_, v_a_2115_, v_f_2116_, v_t_2114_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_alter(lean_object* v_00_u03b1_2118_, lean_object* v_00_u03b2_2119_, lean_object* v_cmp_2120_, lean_object* v_t_2121_, lean_object* v_a_2122_, lean_object* v_f_2123_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2120_, v_a_2122_, v_f_2123_, v_t_2121_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2125_, lean_object* v_mergeFn_2126_, lean_object* v_a_2127_, lean_object* v_x_2128_){
_start:
{
if (lean_obj_tag(v_x_2128_) == 0)
{
lean_object* v___x_2129_; 
lean_dec(v_a_2127_);
lean_dec(v_mergeFn_2126_);
v___x_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2129_, 0, v_b_u2082_2125_);
return v___x_2129_;
}
else
{
lean_object* v_val_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2138_; 
v_val_2130_ = lean_ctor_get(v_x_2128_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_x_2128_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2132_ = v_x_2128_;
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_val_2130_);
lean_dec(v_x_2128_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = lean_apply_3(v_mergeFn_2126_, v_a_2127_, v_val_2130_, v_b_u2082_2125_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2134_);
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2139_, lean_object* v_cmp_2140_, lean_object* v_t_2141_, lean_object* v_a_2142_, lean_object* v_b_u2082_2143_){
_start:
{
lean_object* v___f_2144_; lean_object* v___x_2145_; 
lean_inc(v_a_2142_);
v___f_2144_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2144_, 0, v_b_u2082_2143_);
lean_closure_set(v___f_2144_, 1, v_mergeFn_2139_);
lean_closure_set(v___f_2144_, 2, v_a_2142_);
v___x_2145_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_2140_, v_a_2142_, v___f_2144_, v_t_2141_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith___redArg(lean_object* v_cmp_2146_, lean_object* v_mergeFn_2147_, lean_object* v_t_u2081_2148_, lean_object* v_t_u2082_2149_){
_start:
{
lean_object* v___f_2150_; lean_object* v___x_2151_; 
v___f_2150_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2150_, 0, v_mergeFn_2147_);
lean_closure_set(v___f_2150_, 1, v_cmp_2146_);
v___x_2151_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2150_, v_t_u2081_2148_, v_t_u2082_2149_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_mergeWith(lean_object* v_00_u03b1_2152_, lean_object* v_00_u03b2_2153_, lean_object* v_cmp_2154_, lean_object* v_mergeFn_2155_, lean_object* v_t_u2081_2156_, lean_object* v_t_u2082_2157_){
_start:
{
lean_object* v___f_2158_; lean_object* v___x_2159_; 
v___f_2158_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2158_, 0, v_mergeFn_2155_);
lean_closure_set(v___f_2158_, 1, v_cmp_2154_);
v___x_2159_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2158_, v_t_u2081_2156_, v_t_u2082_2157_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_2160_, lean_object* v_x_2161_, lean_object* v_____s_2162_){
_start:
{
lean_object* v_fst_2163_; lean_object* v_snd_2164_; lean_object* v_r_2165_; lean_object* v___x_2166_; 
v_fst_2163_ = lean_ctor_get(v_x_2161_, 0);
lean_inc(v_fst_2163_);
v_snd_2164_ = lean_ctor_get(v_x_2161_, 1);
lean_inc(v_snd_2164_);
lean_dec_ref(v_x_2161_);
v_r_2165_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2160_, v_fst_2163_, v_snd_2164_, v_____s_2162_);
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v_r_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany___redArg(lean_object* v_cmp_2167_, lean_object* v_inst_2168_, lean_object* v_t_2169_, lean_object* v_l_2170_){
_start:
{
lean_object* v___f_2171_; lean_object* v___x_2172_; 
v___f_2171_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2171_, 0, v_cmp_2167_);
v___x_2172_ = lean_apply_4(v_inst_2168_, lean_box(0), v_l_2170_, v_t_2169_, v___f_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertMany(lean_object* v_00_u03b1_2173_, lean_object* v_00_u03b2_2174_, lean_object* v_cmp_2175_, lean_object* v_00_u03c1_2176_, lean_object* v_inst_2177_, lean_object* v_t_2178_, lean_object* v_l_2179_){
_start:
{
lean_object* v___f_2180_; lean_object* v___x_2181_; 
v___f_2180_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2180_, 0, v_cmp_2175_);
v___x_2181_ = lean_apply_4(v_inst_2177_, lean_box(0), v_l_2179_, v_t_2178_, v___f_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_union___redArg(lean_object* v_cmp_2182_, lean_object* v_t_u2081_2183_, lean_object* v_t_u2082_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_2182_, v_t_u2081_2183_, v_t_u2082_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_union(lean_object* v_00_u03b1_2186_, lean_object* v_00_u03b2_2187_, lean_object* v_cmp_2188_, lean_object* v_t_u2081_2189_, lean_object* v_t_u2082_2190_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_2188_, v_t_u2081_2189_, v_t_u2082_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instUnion___redArg(lean_object* v_cmp_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_2193_, 0, lean_box(0));
lean_closure_set(v___x_2193_, 1, lean_box(0));
lean_closure_set(v___x_2193_, 2, v_cmp_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instUnion(lean_object* v_00_u03b1_2194_, lean_object* v_00_u03b2_2195_, lean_object* v_cmp_2196_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_2197_, 0, lean_box(0));
lean_closure_set(v___x_2197_, 1, lean_box(0));
lean_closure_set(v___x_2197_, 2, v_cmp_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_inter___redArg(lean_object* v_cmp_2198_, lean_object* v_t_u2081_2199_, lean_object* v_t_u2082_2200_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_2198_, v_t_u2081_2199_, v_t_u2082_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_inter(lean_object* v_00_u03b1_2202_, lean_object* v_00_u03b2_2203_, lean_object* v_cmp_2204_, lean_object* v_t_u2081_2205_, lean_object* v_t_u2082_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_2204_, v_t_u2081_2205_, v_t_u2082_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInter___redArg(lean_object* v_cmp_2208_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_2209_, 0, lean_box(0));
lean_closure_set(v___x_2209_, 1, lean_box(0));
lean_closure_set(v___x_2209_, 2, v_cmp_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instInter(lean_object* v_00_u03b1_2210_, lean_object* v_00_u03b2_2211_, lean_object* v_cmp_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_2213_, 0, lean_box(0));
lean_closure_set(v___x_2213_, 1, lean_box(0));
lean_closure_set(v___x_2213_, 2, v_cmp_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___redArg(lean_object* v_cmp_2214_, lean_object* v_inst_2215_, lean_object* v_t_u2081_2216_, lean_object* v_t_u2082_2217_){
_start:
{
uint8_t v___x_2218_; 
v___x_2218_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2214_, v_inst_2215_, v_t_u2081_2216_, v_t_u2082_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___redArg___boxed(lean_object* v_cmp_2219_, lean_object* v_inst_2220_, lean_object* v_t_u2081_2221_, lean_object* v_t_u2082_2222_){
_start:
{
uint8_t v_res_2223_; lean_object* v_r_2224_; 
v_res_2223_ = l_Std_TreeMap_Raw_beq___redArg(v_cmp_2219_, v_inst_2220_, v_t_u2081_2221_, v_t_u2082_2222_);
v_r_2224_ = lean_box(v_res_2223_);
return v_r_2224_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq(lean_object* v_00_u03b1_2225_, lean_object* v_00_u03b2_2226_, lean_object* v_cmp_2227_, lean_object* v_inst_2228_, lean_object* v_t_u2081_2229_, lean_object* v_t_u2082_2230_){
_start:
{
uint8_t v___x_2231_; 
v___x_2231_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2227_, v_inst_2228_, v_t_u2081_2229_, v_t_u2082_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___boxed(lean_object* v_00_u03b1_2232_, lean_object* v_00_u03b2_2233_, lean_object* v_cmp_2234_, lean_object* v_inst_2235_, lean_object* v_t_u2081_2236_, lean_object* v_t_u2082_2237_){
_start:
{
uint8_t v_res_2238_; lean_object* v_r_2239_; 
v_res_2238_ = l_Std_TreeMap_Raw_beq(v_00_u03b1_2232_, v_00_u03b2_2233_, v_cmp_2234_, v_inst_2235_, v_t_u2081_2236_, v_t_u2082_2237_);
v_r_2239_ = lean_box(v_res_2238_);
return v_r_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instBEq___redArg(lean_object* v_cmp_2240_, lean_object* v_inst_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_beq___boxed), 6, 4);
lean_closure_set(v___x_2242_, 0, lean_box(0));
lean_closure_set(v___x_2242_, 1, lean_box(0));
lean_closure_set(v___x_2242_, 2, v_cmp_2240_);
lean_closure_set(v___x_2242_, 3, v_inst_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instBEq(lean_object* v_00_u03b1_2243_, lean_object* v_00_u03b2_2244_, lean_object* v_cmp_2245_, lean_object* v_inst_2246_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_beq___boxed), 6, 4);
lean_closure_set(v___x_2247_, 0, lean_box(0));
lean_closure_set(v___x_2247_, 1, lean_box(0));
lean_closure_set(v___x_2247_, 2, v_cmp_2245_);
lean_closure_set(v___x_2247_, 3, v_inst_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_diff___redArg(lean_object* v_cmp_2248_, lean_object* v_t_u2081_2249_, lean_object* v_t_u2082_2250_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_2248_, v_t_u2081_2249_, v_t_u2082_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_diff(lean_object* v_00_u03b1_2252_, lean_object* v_00_u03b2_2253_, lean_object* v_cmp_2254_, lean_object* v_t_u2081_2255_, lean_object* v_t_u2082_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_2254_, v_t_u2081_2255_, v_t_u2082_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSDiff___redArg(lean_object* v_cmp_2258_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_2259_, 0, lean_box(0));
lean_closure_set(v___x_2259_, 1, lean_box(0));
lean_closure_set(v___x_2259_, 2, v_cmp_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSDiff(lean_object* v_00_u03b1_2260_, lean_object* v_00_u03b2_2261_, lean_object* v_cmp_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_2263_, 0, lean_box(0));
lean_closure_set(v___x_2263_, 1, lean_box(0));
lean_closure_set(v___x_2263_, 2, v_cmp_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_2264_, lean_object* v_a_2265_, lean_object* v_____s_2266_){
_start:
{
uint8_t v___x_2267_; 
lean_inc(v_____s_2266_);
lean_inc(v_a_2265_);
lean_inc_ref(v_cmp_2264_);
v___x_2267_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2264_, v_a_2265_, v_____s_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = lean_box(0);
v___x_2269_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2264_, v_a_2265_, v___x_2268_, v_____s_2266_);
v___x_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; 
lean_dec(v_a_2265_);
lean_dec_ref(v_cmp_2264_);
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v_____s_2266_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg(lean_object* v_cmp_2272_, lean_object* v_inst_2273_, lean_object* v_t_2274_, lean_object* v_l_2275_){
_start:
{
lean_object* v___f_2276_; lean_object* v___x_2277_; 
v___f_2276_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2276_, 0, v_cmp_2272_);
v___x_2277_ = lean_apply_4(v_inst_2273_, lean_box(0), v_l_2275_, v_t_2274_, v___f_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_insertManyIfNewUnit(lean_object* v_00_u03b1_2278_, lean_object* v_cmp_2279_, lean_object* v_00_u03c1_2280_, lean_object* v_inst_2281_, lean_object* v_t_2282_, lean_object* v_l_2283_){
_start:
{
lean_object* v___f_2284_; lean_object* v___x_2285_; 
v___f_2284_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2284_, 0, v_cmp_2279_);
v___x_2285_ = lean_apply_4(v_inst_2281_, lean_box(0), v_l_2283_, v_t_2282_, v___f_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_2286_, lean_object* v_a_2287_, lean_object* v_____s_2288_){
_start:
{
lean_object* v_r_2289_; lean_object* v___x_2290_; 
v_r_2289_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_2286_, v_a_2287_, v_____s_2288_);
v___x_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2290_, 0, v_r_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany___redArg(lean_object* v_cmp_2291_, lean_object* v_inst_2292_, lean_object* v_t_2293_, lean_object* v_l_2294_){
_start:
{
lean_object* v___f_2295_; lean_object* v___x_2296_; 
v___f_2295_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2295_, 0, v_cmp_2291_);
v___x_2296_ = lean_apply_4(v_inst_2292_, lean_box(0), v_l_2294_, v_t_2293_, v___f_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_eraseMany(lean_object* v_00_u03b1_2297_, lean_object* v_00_u03b2_2298_, lean_object* v_cmp_2299_, lean_object* v_00_u03c1_2300_, lean_object* v_inst_2301_, lean_object* v_t_2302_, lean_object* v_l_2303_){
_start:
{
lean_object* v___f_2304_; lean_object* v___x_2305_; 
v___f_2304_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2304_, 0, v_cmp_2299_);
v___x_2305_ = lean_apply_4(v_inst_2301_, lean_box(0), v_l_2303_, v_t_2302_, v___f_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg___lam__1(lean_object* v___f_2309_, lean_object* v___x_2310_, lean_object* v_m_2311_, lean_object* v_prec_2312_){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2313_ = ((lean_object*)(l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__1));
v___x_2314_ = lean_box(0);
v___x_2315_ = ((lean_object*)(l_Std_TreeMap_Raw_foldr___redArg___closed__9));
v___x_2316_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2315_, v___f_2309_, v___x_2314_, v_m_2311_);
v___x_2317_ = l_List_repr___redArg(v___x_2310_, v___x_2316_);
v___x_2318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2313_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = l_Repr_addAppParen(v___x_2318_, v_prec_2312_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_2320_, lean_object* v___x_2321_, lean_object* v_m_2322_, lean_object* v_prec_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Std_TreeMap_Raw_instRepr___redArg___lam__1(v___f_2320_, v___x_2321_, v_m_2322_, v_prec_2323_);
lean_dec(v_prec_2323_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___redArg(lean_object* v_inst_2325_, lean_object* v_inst_2326_){
_start:
{
lean_object* v___f_2327_; lean_object* v___f_2328_; lean_object* v___x_2329_; lean_object* v___f_2330_; 
v___f_2327_ = ((lean_object*)(l_Std_TreeMap_Raw_toList___redArg___closed__0));
v___f_2328_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2328_, 0, v_inst_2326_);
v___x_2329_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2329_, 0, lean_box(0));
lean_closure_set(v___x_2329_, 1, lean_box(0));
lean_closure_set(v___x_2329_, 2, v_inst_2325_);
lean_closure_set(v___x_2329_, 3, v___f_2328_);
v___f_2330_ = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2330_, 0, v___f_2327_);
lean_closure_set(v___f_2330_, 1, v___x_2329_);
return v___f_2330_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr(lean_object* v_00_u03b1_2331_, lean_object* v_00_u03b2_2332_, lean_object* v_cmp_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Std_TreeMap_Raw_instRepr___redArg(v_inst_2334_, v_inst_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instRepr___boxed(lean_object* v_00_u03b1_2337_, lean_object* v_00_u03b2_2338_, lean_object* v_cmp_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Std_TreeMap_Raw_instRepr(v_00_u03b1_2337_, v_00_u03b2_2338_, v_cmp_2339_, v_inst_2340_, v_inst_2341_);
lean_dec_ref(v_cmp_2339_);
return v_res_2342_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
