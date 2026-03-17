// Lean compiler output
// Module: Std.Data.TreeSet.Raw.Basic
// Imports: public import Std.Data.TreeMap.Raw.Basic public import Std.Data.TreeSet.Basic
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
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeSet_Raw___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__0_value;
static const lean_string_object l_Std_TreeSet_Raw___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__1 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__1_value;
static const lean_string_object l_Std_TreeSet_Raw___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__2 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__2_value;
static const lean_string_object l_Std_TreeSet_Raw___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__3 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__3_value;
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__4 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__4_value;
static const lean_array_object l_Std_TreeSet_Raw___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__5 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__5_value;
static const lean_string_object l_Std_TreeSet_Raw___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__6 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__6_value;
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__7 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__7_value;
static const lean_string_object l_Std_TreeSet_Raw___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__8 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__8_value;
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__9 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__9_value;
static const lean_string_object l_Std_TreeSet_Raw___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__10 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__10_value;
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__11 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__11_value;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__12;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__13;
static const lean_string_object l_Std_TreeSet_Raw___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__14 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__14_value;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__15;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__16;
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__17 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__17_value;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__18;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__19;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__20;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__21;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__22;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__23;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__24;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__25;
static lean_once_cell_t l_Std_TreeSet_Raw___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_TreeSet_Raw_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_TreeSet_Raw_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TreeSet"};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__1 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_TreeSet_Raw_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Raw"};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__2 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__2_value;
static const lean_string_object l_Std_TreeSet_Raw_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__3 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__3_value;
static const lean_ctor_object l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_0),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 231, 51, 117, 79, 92, 223, 2)}};
static const lean_ctor_object l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_1),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 13, 19, 93, 188, 109, 240, 135)}};
static const lean_ctor_object l_Std_TreeSet_Raw_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_2),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(79, 110, 249, 107, 190, 245, 21, 34)}};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__4 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__4_value;
static const lean_string_object l_Std_TreeSet_Raw_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__5 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__5_value;
static const lean_ctor_object l_Std_TreeSet_Raw_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__6 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__6_value;
static const lean_string_object l_Std_TreeSet_Raw_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__7 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__7_value;
static const lean_ctor_object l_Std_TreeSet_Raw_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__7_value)}};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__8 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__8_value;
static const lean_string_object l_Std_TreeSet_Raw_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__9 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_TreeSet_Raw_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__10 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_TreeSet_Raw_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__10_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__11 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_TreeSet_Raw_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__6_value),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__8_value),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__12 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__12_value;
static const lean_ctor_object l_Std_TreeSet_Raw_term___x7em___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__4_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__12_value)}};
static const lean_object* l_Std_TreeSet_Raw_term___x7em___00__closed__13 = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__13_value;
LEAN_EXPORT const lean_object* l_Std_TreeSet_Raw_term___x7em__ = (const lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__13_value;
static const lean_string_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1_value;
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_0),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_1),((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_2),((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value;
static lean_once_cell_t l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4;
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5_value;
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_0),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 231, 51, 117, 79, 92, 223, 2)}};
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_1),((lean_object*)&l_Std_TreeSet_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 13, 19, 93, 188, 109, 240, 135)}};
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_2),((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(14, 98, 184, 228, 233, 180, 84, 195)}};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value;
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value)}};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7_value),((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9_value)}};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1 = (const lean_object*)&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_contains(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0_value;
static const lean_string_object l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1 = (const lean_object*)&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1_value;
static const lean_string_object l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2 = (const lean_object*)&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_foldr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_foldr___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__0_value;
static const lean_closure_object l_Std_TreeSet_Raw_foldr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_foldr___redArg___closed__1 = (const lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__1_value;
static const lean_closure_object l_Std_TreeSet_Raw_foldr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_foldr___redArg___closed__2 = (const lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__2_value;
static const lean_closure_object l_Std_TreeSet_Raw_foldr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_foldr___redArg___closed__3 = (const lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__3_value;
static const lean_closure_object l_Std_TreeSet_Raw_foldr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_foldr___redArg___closed__4 = (const lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__4_value;
static const lean_closure_object l_Std_TreeSet_Raw_foldr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_foldr___redArg___closed__5 = (const lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__5_value;
static const lean_closure_object l_Std_TreeSet_Raw_foldr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_foldr___redArg___closed__6 = (const lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__6_value;
static const lean_ctor_object l_Std_TreeSet_Raw_foldr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__0_value),((lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__1_value)}};
static const lean_object* l_Std_TreeSet_Raw_foldr___redArg___closed__7 = (const lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__7_value;
static const lean_ctor_object l_Std_TreeSet_Raw_foldr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__7_value),((lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__2_value),((lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__3_value),((lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__4_value),((lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__5_value)}};
static const lean_object* l_Std_TreeSet_Raw_foldr___redArg___closed__8 = (const lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__8_value;
static const lean_ctor_object l_Std_TreeSet_Raw_foldr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__8_value),((lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__6_value)}};
static const lean_object* l_Std_TreeSet_Raw_foldr___redArg___closed__9 = (const lean_object*)&l_Std_TreeSet_Raw_foldr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_TreeSet_Raw_partition___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_Raw_partition___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_partition___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_TreeSet_Raw_any___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_Raw_any___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_any___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_Raw_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_toList___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_Raw_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_toArray___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_toArray___redArg___closed__0_value;
static const lean_array_object l_Std_TreeSet_Raw_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_TreeSet_Raw_toArray___redArg___closed__1 = (const lean_object*)&l_Std_TreeSet_Raw_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.TreeSet.Raw.ofList "};
static const lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__12, &l_Std_TreeSet_Raw___auto__1___closed__12_once, _init_l_Std_TreeSet_Raw___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__14));
v___x_34_ = lean_string_utf8_byte_size(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__16(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__15, &l_Std_TreeSet_Raw___auto__1___closed__15_once, _init_l_Std_TreeSet_Raw___auto__1___closed__15);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__14));
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_box(0);
v___x_42_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__17));
v___x_43_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__16, &l_Std_TreeSet_Raw___auto__1___closed__16_once, _init_l_Std_TreeSet_Raw___auto__1___closed__16);
v___x_44_ = lean_box(2);
v___x_45_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
lean_ctor_set(v___x_45_, 2, v___x_42_);
lean_ctor_set(v___x_45_, 3, v___x_41_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__18, &l_Std_TreeSet_Raw___auto__1___closed__18_once, _init_l_Std_TreeSet_Raw___auto__1___closed__18);
v___x_47_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__13, &l_Std_TreeSet_Raw___auto__1___closed__13_once, _init_l_Std_TreeSet_Raw___auto__1___closed__13);
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__19, &l_Std_TreeSet_Raw___auto__1___closed__19_once, _init_l_Std_TreeSet_Raw___auto__1___closed__19);
v___x_50_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__11));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__21(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__20, &l_Std_TreeSet_Raw___auto__1___closed__20_once, _init_l_Std_TreeSet_Raw___auto__1___closed__20);
v___x_54_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__5));
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__22(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__21, &l_Std_TreeSet_Raw___auto__1___closed__21_once, _init_l_Std_TreeSet_Raw___auto__1___closed__21);
v___x_57_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__9));
v___x_58_ = lean_box(2);
v___x_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__23(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__22, &l_Std_TreeSet_Raw___auto__1___closed__22_once, _init_l_Std_TreeSet_Raw___auto__1___closed__22);
v___x_61_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__24(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__23, &l_Std_TreeSet_Raw___auto__1___closed__23_once, _init_l_Std_TreeSet_Raw___auto__1___closed__23);
v___x_64_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__7));
v___x_65_ = lean_box(2);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__25(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__24, &l_Std_TreeSet_Raw___auto__1___closed__24_once, _init_l_Std_TreeSet_Raw___auto__1___closed__24);
v___x_68_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__5));
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__26(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__25, &l_Std_TreeSet_Raw___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw___auto__1___closed__25);
v___x_71_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__4));
v___x_72_ = lean_box(2);
v___x_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__26, &l_Std_TreeSet_Raw___auto__1___closed__26_once, _init_l_Std_TreeSet_Raw___auto__1___closed__26);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner(lean_object* v_00_u03b1_75_, lean_object* v_cmp_76_, lean_object* v_t_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(0);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___boxed(lean_object* v_00_u03b1_79_, lean_object* v_cmp_80_, lean_object* v_t_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_TreeSet_Raw_instCoeWFWFUnitInner(v_00_u03b1_79_, v_cmp_80_, v_t_81_);
lean_dec(v_t_81_);
lean_dec_ref(v_cmp_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty(lean_object* v_00_u03b1_83_, lean_object* v_cmp_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_box(1);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty___boxed(lean_object* v_00_u03b1_86_, lean_object* v_cmp_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_TreeSet_Raw_empty(v_00_u03b1_86_, v_cmp_87_);
lean_dec_ref(v_cmp_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection(lean_object* v_00_u03b1_89_, lean_object* v_cmp_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(1);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___boxed(lean_object* v_00_u03b1_92_, lean_object* v_cmp_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_TreeSet_Raw_instEmptyCollection(v_00_u03b1_92_, v_cmp_93_);
lean_dec_ref(v_cmp_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited(lean_object* v_00_u03b1_95_, lean_object* v_cmp_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_box(1);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___boxed(lean_object* v_00_u03b1_98_, lean_object* v_cmp_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_TreeSet_Raw_instInhabited(v_00_u03b1_98_, v_cmp_99_);
lean_dec_ref(v_cmp_99_);
return v_res_100_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3));
v___x_141_ = l_String_toRawSubstring_x27(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(lean_object* v_x_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__4));
lean_inc(v_x_160_);
v___x_164_ = l_Lean_Syntax_isOfKind(v_x_160_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec_ref(v_a_161_);
lean_dec(v_x_160_);
v___x_165_ = lean_box(1);
v___x_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v_a_162_);
return v___x_166_;
}
else
{
lean_object* v_quotContext_167_; lean_object* v_currMacroScope_168_; lean_object* v_ref_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_quotContext_167_ = lean_ctor_get(v_a_161_, 1);
lean_inc(v_quotContext_167_);
v_currMacroScope_168_ = lean_ctor_get(v_a_161_, 2);
lean_inc(v_currMacroScope_168_);
v_ref_169_ = lean_ctor_get(v_a_161_, 5);
lean_inc(v_ref_169_);
lean_dec_ref(v_a_161_);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = l_Lean_Syntax_getArg(v_x_160_, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(2u);
v___x_173_ = l_Lean_Syntax_getArg(v_x_160_, v___x_172_);
lean_dec(v_x_160_);
v___x_174_ = 0;
v___x_175_ = l_Lean_SourceInfo_fromRef(v_ref_169_, v___x_174_);
lean_dec(v_ref_169_);
v___x_176_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2));
v___x_177_ = lean_obj_once(&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4, &l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4_once, _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4);
v___x_178_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5));
v___x_179_ = l_Lean_addMacroScope(v_quotContext_167_, v___x_178_, v_currMacroScope_168_);
v___x_180_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10));
lean_inc(v___x_175_);
v___x_181_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_181_, 0, v___x_175_);
lean_ctor_set(v___x_181_, 1, v___x_177_);
lean_ctor_set(v___x_181_, 2, v___x_179_);
lean_ctor_set(v___x_181_, 3, v___x_180_);
v___x_182_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__9));
lean_inc(v___x_175_);
v___x_183_ = l_Lean_Syntax_node2(v___x_175_, v___x_182_, v___x_171_, v___x_173_);
v___x_184_ = l_Lean_Syntax_node2(v___x_175_, v___x_176_, v___x_181_, v___x_183_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_a_162_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(lean_object* v_x_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2));
lean_inc(v_x_189_);
v___x_193_ = l_Lean_Syntax_isOfKind(v_x_189_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v_x_189_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_a_191_);
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = l_Lean_Syntax_getArg(v_x_189_, v___x_196_);
v___x_198_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1));
lean_inc(v___x_197_);
v___x_199_ = l_Lean_Syntax_isOfKind(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v___x_197_);
lean_dec(v_x_189_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_a_191_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = l_Lean_Syntax_getArg(v_x_189_, v___x_202_);
lean_dec(v_x_189_);
v___x_204_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_203_);
v___x_205_ = l_Lean_Syntax_matchesNull(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v___x_203_);
lean_dec(v___x_197_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v_a_191_);
return v___x_207_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_ref_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_208_ = l_Lean_Syntax_getArg(v___x_203_, v___x_196_);
v___x_209_ = l_Lean_Syntax_getArg(v___x_203_, v___x_202_);
lean_dec(v___x_203_);
v_ref_210_ = l_Lean_replaceRef(v___x_197_, v_a_190_);
lean_dec(v___x_197_);
v___x_211_ = 0;
v___x_212_ = l_Lean_SourceInfo_fromRef(v_ref_210_, v___x_211_);
lean_dec(v_ref_210_);
v___x_213_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__4));
v___x_214_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__7));
lean_inc(v___x_212_);
v___x_215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_212_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = l_Lean_Syntax_node3(v___x_212_, v___x_213_, v___x_208_, v___x_215_, v___x_209_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v_a_191_);
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___boxed(lean_object* v_x_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(v_x_218_, v_a_219_, v_a_220_);
lean_dec(v_a_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert___redArg(lean_object* v_cmp_222_, lean_object* v_l_223_, lean_object* v_a_224_){
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
v___x_227_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_222_, v_a_224_, v___x_226_, v_l_223_);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert(lean_object* v_00_u03b1_228_, lean_object* v_cmp_229_, lean_object* v_l_230_, lean_object* v_a_231_){
_start:
{
uint8_t v___x_232_; 
lean_inc(v_l_230_);
lean_inc(v_a_231_);
lean_inc_ref(v_cmp_229_);
v___x_232_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_229_, v_a_231_, v_l_230_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_box(0);
v___x_234_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_229_, v_a_231_, v___x_233_, v_l_230_);
return v___x_234_;
}
else
{
lean_dec(v_a_231_);
lean_dec_ref(v_cmp_229_);
return v_l_230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg___lam__0(lean_object* v_cmp_235_, lean_object* v_e_236_){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_box(1);
lean_inc(v_e_236_);
lean_inc_ref(v_cmp_235_);
v___x_238_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_235_, v_e_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_box(0);
v___x_240_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_235_, v_e_236_, v___x_239_, v___x_237_);
return v___x_240_;
}
else
{
lean_dec(v_e_236_);
lean_dec_ref(v_cmp_235_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg(lean_object* v_cmp_241_){
_start:
{
lean_object* v___f_242_; 
v___f_242_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_242_, 0, v_cmp_241_);
return v___f_242_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton(lean_object* v_00_u03b1_243_, lean_object* v_cmp_244_){
_start:
{
lean_object* v___f_245_; 
v___f_245_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_245_, 0, v_cmp_244_);
return v___f_245_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg___lam__0(lean_object* v_cmp_246_, lean_object* v_e_247_, lean_object* v_s_248_){
_start:
{
uint8_t v___x_249_; 
lean_inc(v_s_248_);
lean_inc(v_e_247_);
lean_inc_ref(v_cmp_246_);
v___x_249_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_246_, v_e_247_, v_s_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_box(0);
v___x_251_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_246_, v_e_247_, v___x_250_, v_s_248_);
return v___x_251_;
}
else
{
lean_dec(v_e_247_);
lean_dec_ref(v_cmp_246_);
return v_s_248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg(lean_object* v_cmp_252_){
_start:
{
lean_object* v___f_253_; 
v___f_253_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_253_, 0, v_cmp_252_);
return v___f_253_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert(lean_object* v_00_u03b1_254_, lean_object* v_cmp_255_){
_start:
{
lean_object* v___f_256_; 
v___f_256_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_256_, 0, v_cmp_255_);
return v___f_256_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert___redArg(lean_object* v_cmp_257_, lean_object* v_t_258_, lean_object* v_a_259_){
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
v___x_262_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_257_, v_a_259_, v___x_261_, v_t_258_);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert(lean_object* v_00_u03b1_267_, lean_object* v_cmp_268_, lean_object* v_t_269_, lean_object* v_a_270_){
_start:
{
uint8_t v___x_271_; 
lean_inc(v_t_269_);
lean_inc(v_a_270_);
lean_inc_ref(v_cmp_268_);
v___x_271_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_268_, v_a_270_, v_t_269_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = lean_box(0);
v___x_273_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_268_, v_a_270_, v___x_272_, v_t_269_);
v___x_274_ = lean_box(v___x_271_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___x_273_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v_a_270_);
lean_dec_ref(v_cmp_268_);
v___x_276_ = lean_box(v___x_271_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_t_269_);
return v___x_277_;
}
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_contains___redArg(lean_object* v_cmp_278_, lean_object* v_l_279_, lean_object* v_a_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_278_, v_a_280_, v_l_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___redArg___boxed(lean_object* v_cmp_282_, lean_object* v_l_283_, lean_object* v_a_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Std_TreeSet_Raw_contains___redArg(v_cmp_282_, v_l_283_, v_a_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_contains(lean_object* v_00_u03b1_287_, lean_object* v_cmp_288_, lean_object* v_l_289_, lean_object* v_a_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_288_, v_a_290_, v_l_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___boxed(lean_object* v_00_u03b1_292_, lean_object* v_cmp_293_, lean_object* v_l_294_, lean_object* v_a_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Std_TreeSet_Raw_contains(v_00_u03b1_292_, v_cmp_293_, v_l_294_, v_a_295_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership(lean_object* v_00_u03b1_298_, lean_object* v_cmp_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = lean_box(0);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___boxed(lean_object* v_00_u03b1_301_, lean_object* v_cmp_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Std_TreeSet_Raw_instMembership(v_00_u03b1_301_, v_cmp_302_);
lean_dec_ref(v_cmp_302_);
return v_res_303_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableMem___redArg(lean_object* v_cmp_304_, lean_object* v_t_305_, lean_object* v_a_306_){
_start:
{
uint8_t v___x_307_; 
v___x_307_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_304_, v_a_306_, v_t_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_308_, lean_object* v_t_309_, lean_object* v_a_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_Std_TreeSet_Raw_instDecidableMem___redArg(v_cmp_308_, v_t_309_, v_a_310_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableMem(lean_object* v_00_u03b1_313_, lean_object* v_cmp_314_, lean_object* v_t_315_, lean_object* v_a_316_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_314_, v_a_316_, v_t_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_318_, lean_object* v_cmp_319_, lean_object* v_t_320_, lean_object* v_a_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_TreeSet_Raw_instDecidableMem(v_00_u03b1_318_, v_cmp_319_, v_t_320_, v_a_321_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg(lean_object* v_t_324_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg___boxed(lean_object* v_t_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_TreeSet_Raw_size___redArg(v_t_327_);
lean_dec(v_t_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size(lean_object* v_00_u03b1_329_, lean_object* v_cmp_330_, lean_object* v_t_331_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___boxed(lean_object* v_00_u03b1_334_, lean_object* v_cmp_335_, lean_object* v_t_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_TreeSet_Raw_size(v_00_u03b1_334_, v_cmp_335_, v_t_336_);
lean_dec(v_t_336_);
lean_dec_ref(v_cmp_335_);
return v_res_337_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_isEmpty___redArg(lean_object* v_t_338_){
_start:
{
if (lean_obj_tag(v_t_338_) == 0)
{
uint8_t v___x_339_; 
v___x_339_ = 0;
return v___x_339_;
}
else
{
uint8_t v___x_340_; 
v___x_340_ = 1;
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___redArg___boxed(lean_object* v_t_341_){
_start:
{
uint8_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = l_Std_TreeSet_Raw_isEmpty___redArg(v_t_341_);
lean_dec(v_t_341_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_isEmpty(lean_object* v_00_u03b1_344_, lean_object* v_cmp_345_, lean_object* v_t_346_){
_start:
{
if (lean_obj_tag(v_t_346_) == 0)
{
uint8_t v___x_347_; 
v___x_347_ = 0;
return v___x_347_;
}
else
{
uint8_t v___x_348_; 
v___x_348_ = 1;
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___boxed(lean_object* v_00_u03b1_349_, lean_object* v_cmp_350_, lean_object* v_t_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Std_TreeSet_Raw_isEmpty(v_00_u03b1_349_, v_cmp_350_, v_t_351_);
lean_dec(v_t_351_);
lean_dec_ref(v_cmp_350_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase___redArg(lean_object* v_cmp_354_, lean_object* v_t_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_354_, v_a_356_, v_t_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase(lean_object* v_00_u03b1_358_, lean_object* v_cmp_359_, lean_object* v_t_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_359_, v_a_361_, v_t_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f___redArg(lean_object* v_cmp_363_, lean_object* v_t_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_363_, v_t_364_, v_a_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f(lean_object* v_00_u03b1_367_, lean_object* v_cmp_368_, lean_object* v_t_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_368_, v_t_369_, v_a_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get___redArg(lean_object* v_cmp_372_, lean_object* v_t_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_372_, v_t_373_, v_a_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get(lean_object* v_00_u03b1_376_, lean_object* v_cmp_377_, lean_object* v_t_378_, lean_object* v_a_379_, lean_object* v_h_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_377_, v_t_378_, v_a_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___redArg(lean_object* v_cmp_382_, lean_object* v_inst_383_, lean_object* v_t_384_, lean_object* v_a_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_382_, v_t_384_, v_a_385_, v_inst_383_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21(lean_object* v_00_u03b1_387_, lean_object* v_cmp_388_, lean_object* v_inst_389_, lean_object* v_t_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_388_, v_t_390_, v_a_391_, v_inst_389_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg(lean_object* v_cmp_393_, lean_object* v_t_394_, lean_object* v_a_395_, lean_object* v_fallback_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_393_, v_t_394_, v_a_395_, v_fallback_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg___boxed(lean_object* v_cmp_398_, lean_object* v_t_399_, lean_object* v_a_400_, lean_object* v_fallback_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_TreeSet_Raw_getD___redArg(v_cmp_398_, v_t_399_, v_a_400_, v_fallback_401_);
lean_dec(v_fallback_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD(lean_object* v_00_u03b1_403_, lean_object* v_cmp_404_, lean_object* v_t_405_, lean_object* v_a_406_, lean_object* v_fallback_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_404_, v_t_405_, v_a_406_, v_fallback_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___boxed(lean_object* v_00_u03b1_409_, lean_object* v_cmp_410_, lean_object* v_t_411_, lean_object* v_a_412_, lean_object* v_fallback_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_TreeSet_Raw_getD(v_00_u03b1_409_, v_cmp_410_, v_t_411_, v_a_412_, v_fallback_413_);
lean_dec(v_fallback_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg(lean_object* v_t_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg___boxed(lean_object* v_t_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_TreeSet_Raw_min_x3f___redArg(v_t_417_);
lean_dec(v_t_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f(lean_object* v_00_u03b1_419_, lean_object* v_cmp_420_, lean_object* v_t_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___boxed(lean_object* v_00_u03b1_423_, lean_object* v_cmp_424_, lean_object* v_t_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_TreeSet_Raw_min_x3f(v_00_u03b1_423_, v_cmp_424_, v_t_425_);
lean_dec(v_t_425_);
lean_dec_ref(v_cmp_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg(lean_object* v_inst_427_, lean_object* v_t_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_427_, v_t_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg___boxed(lean_object* v_inst_430_, lean_object* v_t_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_TreeSet_Raw_min_x21___redArg(v_inst_430_, v_t_431_);
lean_dec(v_t_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21(lean_object* v_00_u03b1_433_, lean_object* v_cmp_434_, lean_object* v_inst_435_, lean_object* v_t_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_435_, v_t_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___boxed(lean_object* v_00_u03b1_438_, lean_object* v_cmp_439_, lean_object* v_inst_440_, lean_object* v_t_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_TreeSet_Raw_min_x21(v_00_u03b1_438_, v_cmp_439_, v_inst_440_, v_t_441_);
lean_dec(v_t_441_);
lean_dec_ref(v_cmp_439_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg(lean_object* v_t_443_, lean_object* v_fallback_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_443_, v_fallback_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg___boxed(lean_object* v_t_446_, lean_object* v_fallback_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_TreeSet_Raw_minD___redArg(v_t_446_, v_fallback_447_);
lean_dec(v_fallback_447_);
lean_dec(v_t_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD(lean_object* v_00_u03b1_449_, lean_object* v_cmp_450_, lean_object* v_t_451_, lean_object* v_fallback_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_451_, v_fallback_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___boxed(lean_object* v_00_u03b1_454_, lean_object* v_cmp_455_, lean_object* v_t_456_, lean_object* v_fallback_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_TreeSet_Raw_minD(v_00_u03b1_454_, v_cmp_455_, v_t_456_, v_fallback_457_);
lean_dec(v_fallback_457_);
lean_dec(v_t_456_);
lean_dec_ref(v_cmp_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg(lean_object* v_t_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg___boxed(lean_object* v_t_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_TreeSet_Raw_max_x3f___redArg(v_t_461_);
lean_dec(v_t_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f(lean_object* v_00_u03b1_463_, lean_object* v_cmp_464_, lean_object* v_t_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___boxed(lean_object* v_00_u03b1_467_, lean_object* v_cmp_468_, lean_object* v_t_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_TreeSet_Raw_max_x3f(v_00_u03b1_467_, v_cmp_468_, v_t_469_);
lean_dec(v_t_469_);
lean_dec_ref(v_cmp_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg(lean_object* v_inst_471_, lean_object* v_t_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_471_, v_t_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg___boxed(lean_object* v_inst_474_, lean_object* v_t_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_TreeSet_Raw_max_x21___redArg(v_inst_474_, v_t_475_);
lean_dec(v_t_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21(lean_object* v_00_u03b1_477_, lean_object* v_cmp_478_, lean_object* v_inst_479_, lean_object* v_t_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_479_, v_t_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___boxed(lean_object* v_00_u03b1_482_, lean_object* v_cmp_483_, lean_object* v_inst_484_, lean_object* v_t_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_TreeSet_Raw_max_x21(v_00_u03b1_482_, v_cmp_483_, v_inst_484_, v_t_485_);
lean_dec(v_t_485_);
lean_dec_ref(v_cmp_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg(lean_object* v_t_487_, lean_object* v_fallback_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_487_, v_fallback_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg___boxed(lean_object* v_t_490_, lean_object* v_fallback_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_TreeSet_Raw_maxD___redArg(v_t_490_, v_fallback_491_);
lean_dec(v_fallback_491_);
lean_dec(v_t_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD(lean_object* v_00_u03b1_493_, lean_object* v_cmp_494_, lean_object* v_t_495_, lean_object* v_fallback_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_495_, v_fallback_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___boxed(lean_object* v_00_u03b1_498_, lean_object* v_cmp_499_, lean_object* v_t_500_, lean_object* v_fallback_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_TreeSet_Raw_maxD(v_00_u03b1_498_, v_cmp_499_, v_t_500_, v_fallback_501_);
lean_dec(v_fallback_501_);
lean_dec(v_t_500_);
lean_dec_ref(v_cmp_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg(lean_object* v_t_503_, lean_object* v_n_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_503_, v_n_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg___boxed(lean_object* v_t_506_, lean_object* v_n_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_TreeSet_Raw_atIdx_x3f___redArg(v_t_506_, v_n_507_);
lean_dec(v_t_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f(lean_object* v_00_u03b1_509_, lean_object* v_cmp_510_, lean_object* v_t_511_, lean_object* v_n_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_511_, v_n_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___boxed(lean_object* v_00_u03b1_514_, lean_object* v_cmp_515_, lean_object* v_t_516_, lean_object* v_n_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_TreeSet_Raw_atIdx_x3f(v_00_u03b1_514_, v_cmp_515_, v_t_516_, v_n_517_);
lean_dec(v_t_516_);
lean_dec_ref(v_cmp_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg(lean_object* v_inst_519_, lean_object* v_t_520_, lean_object* v_n_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_519_, v_t_520_, v_n_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg___boxed(lean_object* v_inst_523_, lean_object* v_t_524_, lean_object* v_n_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_TreeSet_Raw_atIdx_x21___redArg(v_inst_523_, v_t_524_, v_n_525_);
lean_dec(v_t_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21(lean_object* v_00_u03b1_527_, lean_object* v_cmp_528_, lean_object* v_inst_529_, lean_object* v_t_530_, lean_object* v_n_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_529_, v_t_530_, v_n_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___boxed(lean_object* v_00_u03b1_533_, lean_object* v_cmp_534_, lean_object* v_inst_535_, lean_object* v_t_536_, lean_object* v_n_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_TreeSet_Raw_atIdx_x21(v_00_u03b1_533_, v_cmp_534_, v_inst_535_, v_t_536_, v_n_537_);
lean_dec(v_t_536_);
lean_dec_ref(v_cmp_534_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg(lean_object* v_t_539_, lean_object* v_n_540_, lean_object* v_fallback_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_539_, v_n_540_, v_fallback_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg___boxed(lean_object* v_t_543_, lean_object* v_n_544_, lean_object* v_fallback_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_TreeSet_Raw_atIdxD___redArg(v_t_543_, v_n_544_, v_fallback_545_);
lean_dec(v_fallback_545_);
lean_dec(v_t_543_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD(lean_object* v_00_u03b1_547_, lean_object* v_cmp_548_, lean_object* v_t_549_, lean_object* v_n_550_, lean_object* v_fallback_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_549_, v_n_550_, v_fallback_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___boxed(lean_object* v_00_u03b1_553_, lean_object* v_cmp_554_, lean_object* v_t_555_, lean_object* v_n_556_, lean_object* v_fallback_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_TreeSet_Raw_atIdxD(v_00_u03b1_553_, v_cmp_554_, v_t_555_, v_n_556_, v_fallback_557_);
lean_dec(v_fallback_557_);
lean_dec(v_t_555_);
lean_dec_ref(v_cmp_554_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f___redArg(lean_object* v_cmp_559_, lean_object* v_t_560_, lean_object* v_k_561_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_box(0);
v___x_563_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_559_, v_k_561_, v___x_562_, v_t_560_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f(lean_object* v_00_u03b1_564_, lean_object* v_cmp_565_, lean_object* v_t_566_, lean_object* v_k_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_box(0);
v___x_569_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_565_, v_k_567_, v___x_568_, v_t_566_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f___redArg(lean_object* v_cmp_570_, lean_object* v_t_571_, lean_object* v_k_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_box(0);
v___x_574_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_570_, v_k_572_, v___x_573_, v_t_571_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f(lean_object* v_00_u03b1_575_, lean_object* v_cmp_576_, lean_object* v_t_577_, lean_object* v_k_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_box(0);
v___x_580_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_576_, v_k_578_, v___x_579_, v_t_577_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f___redArg(lean_object* v_cmp_581_, lean_object* v_t_582_, lean_object* v_k_583_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_box(0);
v___x_585_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_581_, v_k_583_, v___x_584_, v_t_582_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f(lean_object* v_00_u03b1_586_, lean_object* v_cmp_587_, lean_object* v_t_588_, lean_object* v_k_589_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_box(0);
v___x_591_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_587_, v_k_589_, v___x_590_, v_t_588_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f___redArg(lean_object* v_cmp_592_, lean_object* v_t_593_, lean_object* v_k_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_box(0);
v___x_596_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_592_, v_k_594_, v___x_595_, v_t_593_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f(lean_object* v_00_u03b1_597_, lean_object* v_cmp_598_, lean_object* v_t_599_, lean_object* v_k_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_box(0);
v___x_602_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_598_, v_k_600_, v___x_601_, v_t_599_);
return v___x_602_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_606_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2));
v___x_607_ = lean_unsigned_to_nat(14u);
v___x_608_ = lean_unsigned_to_nat(22u);
v___x_609_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1));
v___x_610_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0));
v___x_611_ = l_mkPanicMessageWithDecl(v___x_610_, v___x_609_, v___x_608_, v___x_607_, v___x_606_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg(lean_object* v_cmp_612_, lean_object* v_inst_613_, lean_object* v_t_614_, lean_object* v_k_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_box(0);
v___x_617_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_612_, v_k_615_, v___x_616_, v_t_614_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_619_ = l_panic___redArg(v_inst_613_, v___x_618_);
return v___x_619_;
}
else
{
lean_object* v_val_620_; 
lean_dec(v_inst_613_);
v_val_620_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_val_620_);
lean_dec_ref(v___x_617_);
return v_val_620_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21(lean_object* v_00_u03b1_621_, lean_object* v_cmp_622_, lean_object* v_inst_623_, lean_object* v_t_624_, lean_object* v_k_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_box(0);
v___x_627_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_622_, v_k_625_, v___x_626_, v_t_624_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_629_ = l_panic___redArg(v_inst_623_, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v_val_630_; 
lean_dec(v_inst_623_);
v_val_630_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_val_630_);
lean_dec_ref(v___x_627_);
return v_val_630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg(lean_object* v_cmp_631_, lean_object* v_inst_632_, lean_object* v_t_633_, lean_object* v_k_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_box(0);
v___x_636_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_631_, v_k_634_, v___x_635_, v_t_633_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_638_ = l_panic___redArg(v_inst_632_, v___x_637_);
return v___x_638_;
}
else
{
lean_object* v_val_639_; 
lean_dec(v_inst_632_);
v_val_639_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_val_639_);
lean_dec_ref(v___x_636_);
return v_val_639_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21(lean_object* v_00_u03b1_640_, lean_object* v_cmp_641_, lean_object* v_inst_642_, lean_object* v_t_643_, lean_object* v_k_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box(0);
v___x_646_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_641_, v_k_644_, v___x_645_, v_t_643_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_648_ = l_panic___redArg(v_inst_642_, v___x_647_);
return v___x_648_;
}
else
{
lean_object* v_val_649_; 
lean_dec(v_inst_642_);
v_val_649_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_649_);
lean_dec_ref(v___x_646_);
return v_val_649_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg(lean_object* v_cmp_650_, lean_object* v_inst_651_, lean_object* v_t_652_, lean_object* v_k_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_box(0);
v___x_655_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_650_, v_k_653_, v___x_654_, v_t_652_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_657_ = l_panic___redArg(v_inst_651_, v___x_656_);
return v___x_657_;
}
else
{
lean_object* v_val_658_; 
lean_dec(v_inst_651_);
v_val_658_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_val_658_);
lean_dec_ref(v___x_655_);
return v_val_658_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21(lean_object* v_00_u03b1_659_, lean_object* v_cmp_660_, lean_object* v_inst_661_, lean_object* v_t_662_, lean_object* v_k_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_box(0);
v___x_665_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_660_, v_k_663_, v___x_664_, v_t_662_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_667_ = l_panic___redArg(v_inst_661_, v___x_666_);
return v___x_667_;
}
else
{
lean_object* v_val_668_; 
lean_dec(v_inst_661_);
v_val_668_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_668_);
lean_dec_ref(v___x_665_);
return v_val_668_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg(lean_object* v_cmp_669_, lean_object* v_inst_670_, lean_object* v_t_671_, lean_object* v_k_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_box(0);
v___x_674_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_669_, v_k_672_, v___x_673_, v_t_671_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_676_ = l_panic___redArg(v_inst_670_, v___x_675_);
return v___x_676_;
}
else
{
lean_object* v_val_677_; 
lean_dec(v_inst_670_);
v_val_677_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_val_677_);
lean_dec_ref(v___x_674_);
return v_val_677_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21(lean_object* v_00_u03b1_678_, lean_object* v_cmp_679_, lean_object* v_inst_680_, lean_object* v_t_681_, lean_object* v_k_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_box(0);
v___x_684_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_679_, v_k_682_, v___x_683_, v_t_681_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_686_ = l_panic___redArg(v_inst_680_, v___x_685_);
return v___x_686_;
}
else
{
lean_object* v_val_687_; 
lean_dec(v_inst_680_);
v_val_687_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_val_687_);
lean_dec_ref(v___x_684_);
return v_val_687_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg(lean_object* v_cmp_688_, lean_object* v_t_689_, lean_object* v_k_690_, lean_object* v_fallback_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_box(0);
v___x_693_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_688_, v_k_690_, v___x_692_, v_t_689_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_inc(v_fallback_691_);
return v_fallback_691_;
}
else
{
lean_object* v_val_694_; 
v_val_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_694_);
lean_dec_ref(v___x_693_);
return v_val_694_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg___boxed(lean_object* v_cmp_695_, lean_object* v_t_696_, lean_object* v_k_697_, lean_object* v_fallback_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_TreeSet_Raw_getGED___redArg(v_cmp_695_, v_t_696_, v_k_697_, v_fallback_698_);
lean_dec(v_fallback_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED(lean_object* v_00_u03b1_700_, lean_object* v_cmp_701_, lean_object* v_t_702_, lean_object* v_k_703_, lean_object* v_fallback_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_box(0);
v___x_706_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_701_, v_k_703_, v___x_705_, v_t_702_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_inc(v_fallback_704_);
return v_fallback_704_;
}
else
{
lean_object* v_val_707_; 
v_val_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_val_707_);
lean_dec_ref(v___x_706_);
return v_val_707_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___boxed(lean_object* v_00_u03b1_708_, lean_object* v_cmp_709_, lean_object* v_t_710_, lean_object* v_k_711_, lean_object* v_fallback_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std_TreeSet_Raw_getGED(v_00_u03b1_708_, v_cmp_709_, v_t_710_, v_k_711_, v_fallback_712_);
lean_dec(v_fallback_712_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg(lean_object* v_cmp_714_, lean_object* v_t_715_, lean_object* v_k_716_, lean_object* v_fallback_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_box(0);
v___x_719_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_714_, v_k_716_, v___x_718_, v_t_715_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_inc(v_fallback_717_);
return v_fallback_717_;
}
else
{
lean_object* v_val_720_; 
v_val_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_val_720_);
lean_dec_ref(v___x_719_);
return v_val_720_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg___boxed(lean_object* v_cmp_721_, lean_object* v_t_722_, lean_object* v_k_723_, lean_object* v_fallback_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_TreeSet_Raw_getGTD___redArg(v_cmp_721_, v_t_722_, v_k_723_, v_fallback_724_);
lean_dec(v_fallback_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD(lean_object* v_00_u03b1_726_, lean_object* v_cmp_727_, lean_object* v_t_728_, lean_object* v_k_729_, lean_object* v_fallback_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_box(0);
v___x_732_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_727_, v_k_729_, v___x_731_, v_t_728_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_inc(v_fallback_730_);
return v_fallback_730_;
}
else
{
lean_object* v_val_733_; 
v_val_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_val_733_);
lean_dec_ref(v___x_732_);
return v_val_733_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___boxed(lean_object* v_00_u03b1_734_, lean_object* v_cmp_735_, lean_object* v_t_736_, lean_object* v_k_737_, lean_object* v_fallback_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_TreeSet_Raw_getGTD(v_00_u03b1_734_, v_cmp_735_, v_t_736_, v_k_737_, v_fallback_738_);
lean_dec(v_fallback_738_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg(lean_object* v_cmp_740_, lean_object* v_t_741_, lean_object* v_k_742_, lean_object* v_fallback_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_box(0);
v___x_745_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_740_, v_k_742_, v___x_744_, v_t_741_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_inc(v_fallback_743_);
return v_fallback_743_;
}
else
{
lean_object* v_val_746_; 
v_val_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_746_);
lean_dec_ref(v___x_745_);
return v_val_746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg___boxed(lean_object* v_cmp_747_, lean_object* v_t_748_, lean_object* v_k_749_, lean_object* v_fallback_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_TreeSet_Raw_getLED___redArg(v_cmp_747_, v_t_748_, v_k_749_, v_fallback_750_);
lean_dec(v_fallback_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED(lean_object* v_00_u03b1_752_, lean_object* v_cmp_753_, lean_object* v_t_754_, lean_object* v_k_755_, lean_object* v_fallback_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_box(0);
v___x_758_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_753_, v_k_755_, v___x_757_, v_t_754_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_inc(v_fallback_756_);
return v_fallback_756_;
}
else
{
lean_object* v_val_759_; 
v_val_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref(v___x_758_);
return v_val_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___boxed(lean_object* v_00_u03b1_760_, lean_object* v_cmp_761_, lean_object* v_t_762_, lean_object* v_k_763_, lean_object* v_fallback_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_TreeSet_Raw_getLED(v_00_u03b1_760_, v_cmp_761_, v_t_762_, v_k_763_, v_fallback_764_);
lean_dec(v_fallback_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg(lean_object* v_cmp_766_, lean_object* v_t_767_, lean_object* v_k_768_, lean_object* v_fallback_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_box(0);
v___x_771_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_766_, v_k_768_, v___x_770_, v_t_767_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_inc(v_fallback_769_);
return v_fallback_769_;
}
else
{
lean_object* v_val_772_; 
v_val_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_val_772_);
lean_dec_ref(v___x_771_);
return v_val_772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg___boxed(lean_object* v_cmp_773_, lean_object* v_t_774_, lean_object* v_k_775_, lean_object* v_fallback_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_TreeSet_Raw_getLTD___redArg(v_cmp_773_, v_t_774_, v_k_775_, v_fallback_776_);
lean_dec(v_fallback_776_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD(lean_object* v_00_u03b1_778_, lean_object* v_cmp_779_, lean_object* v_t_780_, lean_object* v_k_781_, lean_object* v_fallback_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_box(0);
v___x_784_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_779_, v_k_781_, v___x_783_, v_t_780_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_inc(v_fallback_782_);
return v_fallback_782_;
}
else
{
lean_object* v_val_785_; 
v_val_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_val_785_);
lean_dec_ref(v___x_784_);
return v_val_785_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___boxed(lean_object* v_00_u03b1_786_, lean_object* v_cmp_787_, lean_object* v_t_788_, lean_object* v_k_789_, lean_object* v_fallback_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_TreeSet_Raw_getLTD(v_00_u03b1_786_, v_cmp_787_, v_t_788_, v_k_789_, v_fallback_790_);
lean_dec(v_fallback_790_);
return v_res_791_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_filter___redArg___lam__0(lean_object* v_f_792_, lean_object* v_a_793_, lean_object* v_x_794_){
_start:
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = lean_apply_1(v_f_792_, v_a_793_);
v___x_796_ = lean_unbox(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_797_, lean_object* v_a_798_, lean_object* v_x_799_){
_start:
{
uint8_t v_res_800_; lean_object* v_r_801_; 
v_res_800_ = l_Std_TreeSet_Raw_filter___redArg___lam__0(v_f_797_, v_a_798_, v_x_799_);
v_r_801_ = lean_box(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg(lean_object* v_f_802_, lean_object* v_t_803_){
_start:
{
lean_object* v___f_804_; lean_object* v___x_805_; 
v___f_804_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_804_, 0, v_f_802_);
v___x_805_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_804_, v_t_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter(lean_object* v_00_u03b1_806_, lean_object* v_cmp_807_, lean_object* v_f_808_, lean_object* v_t_809_){
_start:
{
lean_object* v___f_810_; lean_object* v___x_811_; 
v___f_810_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_810_, 0, v_f_808_);
v___x_811_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_810_, v_t_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___boxed(lean_object* v_00_u03b1_812_, lean_object* v_cmp_813_, lean_object* v_f_814_, lean_object* v_t_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_TreeSet_Raw_filter(v_00_u03b1_812_, v_cmp_813_, v_f_814_, v_t_815_);
lean_dec_ref(v_cmp_813_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg___lam__0(lean_object* v_f_817_, lean_object* v_c_818_, lean_object* v_a_819_, lean_object* v_x_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = lean_apply_2(v_f_817_, v_c_818_, v_a_819_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg(lean_object* v_inst_822_, lean_object* v_f_823_, lean_object* v_init_824_, lean_object* v_t_825_){
_start:
{
lean_object* v___f_826_; lean_object* v___x_827_; 
v___f_826_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_826_, 0, v_f_823_);
v___x_827_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_822_, v___f_826_, v_init_824_, v_t_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM(lean_object* v_00_u03b1_828_, lean_object* v_cmp_829_, lean_object* v_00_u03b4_830_, lean_object* v_m_831_, lean_object* v_inst_832_, lean_object* v_f_833_, lean_object* v_init_834_, lean_object* v_t_835_){
_start:
{
lean_object* v___f_836_; lean_object* v___x_837_; 
v___f_836_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_836_, 0, v_f_833_);
v___x_837_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_832_, v___f_836_, v_init_834_, v_t_835_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___boxed(lean_object* v_00_u03b1_838_, lean_object* v_cmp_839_, lean_object* v_00_u03b4_840_, lean_object* v_m_841_, lean_object* v_inst_842_, lean_object* v_f_843_, lean_object* v_init_844_, lean_object* v_t_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_TreeSet_Raw_foldlM(v_00_u03b1_838_, v_cmp_839_, v_00_u03b4_840_, v_m_841_, v_inst_842_, v_f_843_, v_init_844_, v_t_845_);
lean_dec_ref(v_cmp_839_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___redArg(lean_object* v_f_847_, lean_object* v_init_848_, lean_object* v_t_849_){
_start:
{
lean_object* v___f_850_; lean_object* v___x_851_; 
v___f_850_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_850_, 0, v_f_847_);
v___x_851_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_850_, v_init_848_, v_t_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl(lean_object* v_00_u03b1_852_, lean_object* v_cmp_853_, lean_object* v_00_u03b4_854_, lean_object* v_f_855_, lean_object* v_init_856_, lean_object* v_t_857_){
_start:
{
lean_object* v___f_858_; lean_object* v___x_859_; 
v___f_858_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_858_, 0, v_f_855_);
v___x_859_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_858_, v_init_856_, v_t_857_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___boxed(lean_object* v_00_u03b1_860_, lean_object* v_cmp_861_, lean_object* v_00_u03b4_862_, lean_object* v_f_863_, lean_object* v_init_864_, lean_object* v_t_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_TreeSet_Raw_foldl(v_00_u03b1_860_, v_cmp_861_, v_00_u03b4_862_, v_f_863_, v_init_864_, v_t_865_);
lean_dec_ref(v_cmp_861_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg___lam__0(lean_object* v_f_867_, lean_object* v_a_868_, lean_object* v_x_869_, lean_object* v_acc_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = lean_apply_2(v_f_867_, v_a_868_, v_acc_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg(lean_object* v_inst_872_, lean_object* v_f_873_, lean_object* v_init_874_, lean_object* v_t_875_){
_start:
{
lean_object* v___f_876_; lean_object* v___x_877_; 
v___f_876_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_876_, 0, v_f_873_);
v___x_877_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_872_, v___f_876_, v_init_874_, v_t_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM(lean_object* v_00_u03b1_878_, lean_object* v_cmp_879_, lean_object* v_00_u03b4_880_, lean_object* v_m_881_, lean_object* v_inst_882_, lean_object* v_f_883_, lean_object* v_init_884_, lean_object* v_t_885_){
_start:
{
lean_object* v___f_886_; lean_object* v___x_887_; 
v___f_886_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_886_, 0, v_f_883_);
v___x_887_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_882_, v___f_886_, v_init_884_, v_t_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___boxed(lean_object* v_00_u03b1_888_, lean_object* v_cmp_889_, lean_object* v_00_u03b4_890_, lean_object* v_m_891_, lean_object* v_inst_892_, lean_object* v_f_893_, lean_object* v_init_894_, lean_object* v_t_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Std_TreeSet_Raw_foldrM(v_00_u03b1_888_, v_cmp_889_, v_00_u03b4_890_, v_m_891_, v_inst_892_, v_f_893_, v_init_894_, v_t_895_);
lean_dec_ref(v_cmp_889_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg___lam__0(lean_object* v_f_897_, lean_object* v_x1_898_, lean_object* v_x2_899_, lean_object* v_x3_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_apply_2(v_f_897_, v_x1_898_, v_x3_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg(lean_object* v_f_921_, lean_object* v_init_922_, lean_object* v_t_923_){
_start:
{
lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___f_924_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_924_, 0, v_f_921_);
v___x_925_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_926_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_925_, v___f_924_, v_init_922_, v_t_923_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr(lean_object* v_00_u03b1_927_, lean_object* v_cmp_928_, lean_object* v_00_u03b4_929_, lean_object* v_f_930_, lean_object* v_init_931_, lean_object* v_t_932_){
_start:
{
lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___f_933_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_933_, 0, v_f_930_);
v___x_934_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_935_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_934_, v___f_933_, v_init_931_, v_t_932_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___boxed(lean_object* v_00_u03b1_936_, lean_object* v_cmp_937_, lean_object* v_00_u03b4_938_, lean_object* v_f_939_, lean_object* v_init_940_, lean_object* v_t_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_TreeSet_Raw_foldr(v_00_u03b1_936_, v_cmp_937_, v_00_u03b4_938_, v_f_939_, v_init_940_, v_t_941_);
lean_dec_ref(v_cmp_937_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg___lam__0(lean_object* v_f_943_, lean_object* v_cmp_944_, lean_object* v_x_945_, lean_object* v_a_946_, lean_object* v_b_947_){
_start:
{
lean_object* v_fst_948_; lean_object* v_snd_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_963_; 
v_fst_948_ = lean_ctor_get(v_x_945_, 0);
v_snd_949_ = lean_ctor_get(v_x_945_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_945_);
if (v_isSharedCheck_963_ == 0)
{
v___x_951_ = v_x_945_;
v_isShared_952_ = v_isSharedCheck_963_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_snd_949_);
lean_inc(v_fst_948_);
lean_dec(v_x_945_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_963_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; uint8_t v___x_954_; 
lean_inc(v_a_946_);
v___x_953_ = lean_apply_1(v_f_943_, v_a_946_);
v___x_954_ = lean_unbox(v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_944_, v_a_946_, v_b_947_, v_snd_949_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v___x_955_);
v___x_957_ = v___x_951_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_fst_948_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_944_, v_a_946_, v_b_947_, v_fst_948_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_959_);
v___x_961_ = v___x_951_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_snd_949_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg(lean_object* v_cmp_966_, lean_object* v_f_967_, lean_object* v_t_968_){
_start:
{
lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v_p_971_; lean_object* v_fst_972_; lean_object* v_snd_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v___f_969_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_969_, 0, v_f_967_);
lean_closure_set(v___f_969_, 1, v_cmp_966_);
v___x_970_ = ((lean_object*)(l_Std_TreeSet_Raw_partition___redArg___closed__0));
v_p_971_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_969_, v___x_970_, v_t_968_);
v_fst_972_ = lean_ctor_get(v_p_971_, 0);
v_snd_973_ = lean_ctor_get(v_p_971_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v_p_971_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v_p_971_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_snd_973_);
lean_inc(v_fst_972_);
lean_dec(v_p_971_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_fst_972_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_snd_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition(lean_object* v_00_u03b1_981_, lean_object* v_cmp_982_, lean_object* v_f_983_, lean_object* v_t_984_){
_start:
{
lean_object* v___f_985_; lean_object* v___x_986_; lean_object* v_p_987_; lean_object* v_fst_988_; lean_object* v_snd_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
v___f_985_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_985_, 0, v_f_983_);
lean_closure_set(v___f_985_, 1, v_cmp_982_);
v___x_986_ = ((lean_object*)(l_Std_TreeSet_Raw_partition___redArg___closed__0));
v_p_987_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_985_, v___x_986_, v_t_984_);
v_fst_988_ = lean_ctor_get(v_p_987_, 0);
v_snd_989_ = lean_ctor_get(v_p_987_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_p_987_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v_p_987_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_snd_989_);
lean_inc(v_fst_988_);
lean_dec(v_p_987_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_fst_988_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_snd_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg___lam__0(lean_object* v_f_997_, lean_object* v_x_998_, lean_object* v_k_999_, lean_object* v_v_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_apply_1(v_f_997_, v_k_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg(lean_object* v_inst_1002_, lean_object* v_f_1003_, lean_object* v_t_1004_){
_start:
{
lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___f_1005_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1005_, 0, v_f_1003_);
v___x_1006_ = lean_box(0);
v___x_1007_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1002_, v___f_1005_, v___x_1006_, v_t_1004_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM(lean_object* v_00_u03b1_1008_, lean_object* v_cmp_1009_, lean_object* v_m_1010_, lean_object* v_inst_1011_, lean_object* v_f_1012_, lean_object* v_t_1013_){
_start:
{
lean_object* v___f_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___f_1014_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1014_, 0, v_f_1012_);
v___x_1015_ = lean_box(0);
v___x_1016_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1011_, v___f_1014_, v___x_1015_, v_t_1013_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___boxed(lean_object* v_00_u03b1_1017_, lean_object* v_cmp_1018_, lean_object* v_m_1019_, lean_object* v_inst_1020_, lean_object* v_f_1021_, lean_object* v_t_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Std_TreeSet_Raw_forM(v_00_u03b1_1017_, v_cmp_1018_, v_m_1019_, v_inst_1020_, v_f_1021_, v_t_1022_);
lean_dec_ref(v_cmp_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__0(lean_object* v_f_1024_, lean_object* v_a_1025_, lean_object* v_b_1026_, lean_object* v_c_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_apply_2(v_f_1024_, v_a_1025_, v_c_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__1(lean_object* v_toPure_1029_, lean_object* v_____do__lift_1030_){
_start:
{
lean_object* v_a_1031_; lean_object* v___x_1032_; 
v_a_1031_ = lean_ctor_get(v_____do__lift_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref(v_____do__lift_1030_);
v___x_1032_ = lean_apply_2(v_toPure_1029_, lean_box(0), v_a_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg(lean_object* v_inst_1033_, lean_object* v_f_1034_, lean_object* v_init_1035_, lean_object* v_t_1036_){
_start:
{
lean_object* v_toApplicative_1037_; lean_object* v_toBind_1038_; lean_object* v_toPure_1039_; lean_object* v___f_1040_; lean_object* v___x_1041_; lean_object* v___f_1042_; lean_object* v___x_1043_; 
v_toApplicative_1037_ = lean_ctor_get(v_inst_1033_, 0);
v_toBind_1038_ = lean_ctor_get(v_inst_1033_, 1);
lean_inc(v_toBind_1038_);
v_toPure_1039_ = lean_ctor_get(v_toApplicative_1037_, 1);
lean_inc(v_toPure_1039_);
v___f_1040_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1040_, 0, v_f_1034_);
v___x_1041_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1033_, v___f_1040_, v_init_1035_, v_t_1036_);
v___f_1042_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1042_, 0, v_toPure_1039_);
v___x_1043_ = lean_apply_4(v_toBind_1038_, lean_box(0), lean_box(0), v___x_1041_, v___f_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn(lean_object* v_00_u03b1_1044_, lean_object* v_cmp_1045_, lean_object* v_00_u03b4_1046_, lean_object* v_m_1047_, lean_object* v_inst_1048_, lean_object* v_f_1049_, lean_object* v_init_1050_, lean_object* v_t_1051_){
_start:
{
lean_object* v_toApplicative_1052_; lean_object* v_toBind_1053_; lean_object* v_toPure_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___f_1057_; lean_object* v___x_1058_; 
v_toApplicative_1052_ = lean_ctor_get(v_inst_1048_, 0);
v_toBind_1053_ = lean_ctor_get(v_inst_1048_, 1);
lean_inc(v_toBind_1053_);
v_toPure_1054_ = lean_ctor_get(v_toApplicative_1052_, 1);
lean_inc(v_toPure_1054_);
v___f_1055_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1055_, 0, v_f_1049_);
v___x_1056_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1048_, v___f_1055_, v_init_1050_, v_t_1051_);
v___f_1057_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1057_, 0, v_toPure_1054_);
v___x_1058_ = lean_apply_4(v_toBind_1053_, lean_box(0), lean_box(0), v___x_1056_, v___f_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___boxed(lean_object* v_00_u03b1_1059_, lean_object* v_cmp_1060_, lean_object* v_00_u03b4_1061_, lean_object* v_m_1062_, lean_object* v_inst_1063_, lean_object* v_f_1064_, lean_object* v_init_1065_, lean_object* v_t_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Std_TreeSet_Raw_forIn(v_00_u03b1_1059_, v_cmp_1060_, v_00_u03b4_1061_, v_m_1062_, v_inst_1063_, v_f_1064_, v_init_1065_, v_t_1066_);
lean_dec_ref(v_cmp_1060_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1(lean_object* v_inst_1068_, lean_object* v_t_1069_, lean_object* v_f_1070_){
_start:
{
lean_object* v___f_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___f_1071_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1071_, 0, v_f_1070_);
v___x_1072_ = lean_box(0);
v___x_1073_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1068_, v___f_1071_, v___x_1072_, v_t_1069_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_1074_){
_start:
{
lean_object* v___f_1075_; 
v___f_1075_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1075_, 0, v_inst_1074_);
return v___f_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_1076_, lean_object* v_cmp_1077_, lean_object* v_m_1078_, lean_object* v_inst_1079_){
_start:
{
lean_object* v___f_1080_; 
v___f_1080_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1080_, 0, v_inst_1079_);
return v___f_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___boxed(lean_object* v_00_u03b1_1081_, lean_object* v_cmp_1082_, lean_object* v_m_1083_, lean_object* v_inst_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Std_TreeSet_Raw_instForMOfMonad(v_00_u03b1_1081_, v_cmp_1082_, v_m_1083_, v_inst_1084_);
lean_dec_ref(v_cmp_1082_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2(lean_object* v_inst_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_t_1088_, lean_object* v_init_1089_, lean_object* v_f_1090_){
_start:
{
lean_object* v_toApplicative_1091_; lean_object* v_toBind_1092_; lean_object* v_toPure_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; 
v_toApplicative_1091_ = lean_ctor_get(v_inst_1086_, 0);
v_toBind_1092_ = lean_ctor_get(v_inst_1086_, 1);
lean_inc(v_toBind_1092_);
v_toPure_1093_ = lean_ctor_get(v_toApplicative_1091_, 1);
lean_inc(v_toPure_1093_);
v___f_1094_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1094_, 0, v_f_1090_);
v___x_1095_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1086_, v___f_1094_, v_init_1089_, v_t_1088_);
v___f_1096_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1096_, 0, v_toPure_1093_);
v___x_1097_ = lean_apply_4(v_toBind_1092_, lean_box(0), lean_box(0), v___x_1095_, v___f_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_1098_){
_start:
{
lean_object* v___f_1099_; 
v___f_1099_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1099_, 0, v_inst_1098_);
return v___f_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_1100_, lean_object* v_cmp_1101_, lean_object* v_m_1102_, lean_object* v_inst_1103_){
_start:
{
lean_object* v___f_1104_; 
v___f_1104_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1104_, 0, v_inst_1103_);
return v___f_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___boxed(lean_object* v_00_u03b1_1105_, lean_object* v_cmp_1106_, lean_object* v_m_1107_, lean_object* v_inst_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_TreeSet_Raw_instForInOfMonad(v_00_u03b1_1105_, v_cmp_1106_, v_m_1107_, v_inst_1108_);
lean_dec_ref(v_cmp_1106_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0(lean_object* v_p_1110_, lean_object* v___x_1111_, lean_object* v___x_1112_, lean_object* v_a_1113_, lean_object* v_b_1114_, lean_object* v_acc_1115_){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_apply_1(v_p_1110_, v_a_1113_);
v___x_1117_ = lean_unbox(v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1111_);
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec_ref(v___x_1111_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1116_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1112_);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1122_, lean_object* v___x_1123_, lean_object* v___x_1124_, lean_object* v_a_1125_, lean_object* v_b_1126_, lean_object* v_acc_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Std_TreeSet_Raw_any___redArg___lam__0(v_p_1122_, v___x_1123_, v___x_1124_, v_a_1125_, v_b_1126_, v_acc_1127_);
lean_dec_ref(v_acc_1127_);
return v_res_1128_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_any___redArg(lean_object* v_t_1132_, lean_object* v_p_1133_){
_start:
{
lean_object* v___y_1135_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___f_1143_; lean_object* v___x_1144_; lean_object* v_a_1145_; 
v___x_1140_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1141_ = lean_box(0);
v___x_1142_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1143_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1143_, 0, v_p_1133_);
lean_closure_set(v___f_1143_, 1, v___x_1142_);
lean_closure_set(v___f_1143_, 2, v___x_1141_);
v___x_1144_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1140_, v___f_1143_, v___x_1142_, v_t_1132_);
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___y_1135_ = v_a_1145_;
goto v___jp_1134_;
v___jp_1134_:
{
lean_object* v_fst_1136_; 
v_fst_1136_ = lean_ctor_get(v___y_1135_, 0);
lean_inc(v_fst_1136_);
lean_dec_ref(v___y_1135_);
if (lean_obj_tag(v_fst_1136_) == 0)
{
uint8_t v___x_1137_; 
v___x_1137_ = 0;
return v___x_1137_;
}
else
{
lean_object* v_val_1138_; uint8_t v___x_1139_; 
v_val_1138_ = lean_ctor_get(v_fst_1136_, 0);
lean_inc(v_val_1138_);
lean_dec_ref(v_fst_1136_);
v___x_1139_ = lean_unbox(v_val_1138_);
lean_dec(v_val_1138_);
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___boxed(lean_object* v_t_1146_, lean_object* v_p_1147_){
_start:
{
uint8_t v_res_1148_; lean_object* v_r_1149_; 
v_res_1148_ = l_Std_TreeSet_Raw_any___redArg(v_t_1146_, v_p_1147_);
v_r_1149_ = lean_box(v_res_1148_);
return v_r_1149_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_any(lean_object* v_00_u03b1_1150_, lean_object* v_cmp_1151_, lean_object* v_t_1152_, lean_object* v_p_1153_){
_start:
{
lean_object* v___y_1155_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; lean_object* v_a_1165_; 
v___x_1160_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1161_ = lean_box(0);
v___x_1162_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1163_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1163_, 0, v_p_1153_);
lean_closure_set(v___f_1163_, 1, v___x_1162_);
lean_closure_set(v___f_1163_, 2, v___x_1161_);
v___x_1164_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1160_, v___f_1163_, v___x_1162_, v_t_1152_);
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___y_1155_ = v_a_1165_;
goto v___jp_1154_;
v___jp_1154_:
{
lean_object* v_fst_1156_; 
v_fst_1156_ = lean_ctor_get(v___y_1155_, 0);
lean_inc(v_fst_1156_);
lean_dec_ref(v___y_1155_);
if (lean_obj_tag(v_fst_1156_) == 0)
{
uint8_t v___x_1157_; 
v___x_1157_ = 0;
return v___x_1157_;
}
else
{
lean_object* v_val_1158_; uint8_t v___x_1159_; 
v_val_1158_ = lean_ctor_get(v_fst_1156_, 0);
lean_inc(v_val_1158_);
lean_dec_ref(v_fst_1156_);
v___x_1159_ = lean_unbox(v_val_1158_);
lean_dec(v_val_1158_);
return v___x_1159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___boxed(lean_object* v_00_u03b1_1166_, lean_object* v_cmp_1167_, lean_object* v_t_1168_, lean_object* v_p_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Std_TreeSet_Raw_any(v_00_u03b1_1166_, v_cmp_1167_, v_t_1168_, v_p_1169_);
lean_dec_ref(v_cmp_1167_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0(lean_object* v_p_1172_, lean_object* v___x_1173_, lean_object* v___x_1174_, lean_object* v_a_1175_, lean_object* v_b_1176_, lean_object* v_acc_1177_){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_apply_1(v_p_1172_, v_a_1175_);
v___x_1179_ = lean_unbox(v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec_ref(v___x_1174_);
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v___x_1173_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1174_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1184_, lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v_a_1187_, lean_object* v_b_1188_, lean_object* v_acc_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Std_TreeSet_Raw_all___redArg___lam__0(v_p_1184_, v___x_1185_, v___x_1186_, v_a_1187_, v_b_1188_, v_acc_1189_);
lean_dec_ref(v_acc_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_all___redArg(lean_object* v_t_1191_, lean_object* v_p_1192_){
_start:
{
lean_object* v___y_1194_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v_a_1204_; 
v___x_1199_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1200_ = lean_box(0);
v___x_1201_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1202_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1202_, 0, v_p_1192_);
lean_closure_set(v___f_1202_, 1, v___x_1200_);
lean_closure_set(v___f_1202_, 2, v___x_1201_);
v___x_1203_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1199_, v___f_1202_, v___x_1201_, v_t_1191_);
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___y_1194_ = v_a_1204_;
goto v___jp_1193_;
v___jp_1193_:
{
lean_object* v_fst_1195_; 
v_fst_1195_ = lean_ctor_get(v___y_1194_, 0);
lean_inc(v_fst_1195_);
lean_dec_ref(v___y_1194_);
if (lean_obj_tag(v_fst_1195_) == 0)
{
uint8_t v___x_1196_; 
v___x_1196_ = 1;
return v___x_1196_;
}
else
{
lean_object* v_val_1197_; uint8_t v___x_1198_; 
v_val_1197_ = lean_ctor_get(v_fst_1195_, 0);
lean_inc(v_val_1197_);
lean_dec_ref(v_fst_1195_);
v___x_1198_ = lean_unbox(v_val_1197_);
lean_dec(v_val_1197_);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___boxed(lean_object* v_t_1205_, lean_object* v_p_1206_){
_start:
{
uint8_t v_res_1207_; lean_object* v_r_1208_; 
v_res_1207_ = l_Std_TreeSet_Raw_all___redArg(v_t_1205_, v_p_1206_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_all(lean_object* v_00_u03b1_1209_, lean_object* v_cmp_1210_, lean_object* v_t_1211_, lean_object* v_p_1212_){
_start:
{
lean_object* v___y_1214_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v_a_1224_; 
v___x_1219_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1220_ = lean_box(0);
v___x_1221_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1222_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1222_, 0, v_p_1212_);
lean_closure_set(v___f_1222_, 1, v___x_1220_);
lean_closure_set(v___f_1222_, 2, v___x_1221_);
v___x_1223_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1219_, v___f_1222_, v___x_1221_, v_t_1211_);
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___y_1214_ = v_a_1224_;
goto v___jp_1213_;
v___jp_1213_:
{
lean_object* v_fst_1215_; 
v_fst_1215_ = lean_ctor_get(v___y_1214_, 0);
lean_inc(v_fst_1215_);
lean_dec_ref(v___y_1214_);
if (lean_obj_tag(v_fst_1215_) == 0)
{
uint8_t v___x_1216_; 
v___x_1216_ = 1;
return v___x_1216_;
}
else
{
lean_object* v_val_1217_; uint8_t v___x_1218_; 
v_val_1217_ = lean_ctor_get(v_fst_1215_, 0);
lean_inc(v_val_1217_);
lean_dec_ref(v_fst_1215_);
v___x_1218_ = lean_unbox(v_val_1217_);
lean_dec(v_val_1217_);
return v___x_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___boxed(lean_object* v_00_u03b1_1225_, lean_object* v_cmp_1226_, lean_object* v_t_1227_, lean_object* v_p_1228_){
_start:
{
uint8_t v_res_1229_; lean_object* v_r_1230_; 
v_res_1229_ = l_Std_TreeSet_Raw_all(v_00_u03b1_1225_, v_cmp_1226_, v_t_1227_, v_p_1228_);
lean_dec_ref(v_cmp_1226_);
v_r_1230_ = lean_box(v_res_1229_);
return v_r_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg___lam__0(lean_object* v_x1_1231_, lean_object* v_x2_1232_, lean_object* v_x3_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1234_, 0, v_x1_1231_);
lean_ctor_set(v___x_1234_, 1, v_x3_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg(lean_object* v_t_1236_){
_start:
{
lean_object* v___f_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___f_1237_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___x_1238_ = lean_box(0);
v___x_1239_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1240_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1239_, v___f_1237_, v___x_1238_, v_t_1236_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList(lean_object* v_00_u03b1_1241_, lean_object* v_cmp_1242_, lean_object* v_t_1243_){
_start:
{
lean_object* v___f_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___f_1244_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___x_1245_ = lean_box(0);
v___x_1246_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1247_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1246_, v___f_1244_, v___x_1245_, v_t_1243_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_cmp_1249_, lean_object* v_t_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_TreeSet_Raw_toList(v_00_u03b1_1248_, v_cmp_1249_, v_t_1250_);
lean_dec_ref(v_cmp_1249_);
return v_res_1251_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__26, &l_Std_TreeSet_Raw___auto__1___closed__26_once, _init_l_Std_TreeSet_Raw___auto__1___closed__26);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg___lam__0(lean_object* v_cmp_1253_, lean_object* v_a_1254_, lean_object* v_x_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v___x_1257_; 
lean_inc(v___y_1256_);
lean_inc(v_a_1254_);
lean_inc_ref(v_cmp_1253_);
v___x_1257_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1253_, v_a_1254_, v___y_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_box(0);
v___x_1259_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1253_, v_a_1254_, v___x_1258_, v___y_1256_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_a_1254_);
lean_dec_ref(v_cmp_1253_);
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___y_1256_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg(lean_object* v_l_1262_, lean_object* v_cmp_1263_){
_start:
{
lean_object* v___f_1264_; lean_object* v___x_1265_; lean_object* v_r_1266_; lean_object* v___x_1267_; 
v___f_1264_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1264_, 0, v_cmp_1263_);
v___x_1265_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1266_ = lean_box(1);
v___x_1267_ = l_List_forIn_x27_loop___redArg(v___x_1265_, v___f_1264_, v_l_1262_, v_r_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList(lean_object* v_00_u03b1_1268_, lean_object* v_l_1269_, lean_object* v_cmp_1270_){
_start:
{
lean_object* v___f_1271_; lean_object* v___x_1272_; lean_object* v_r_1273_; lean_object* v___x_1274_; 
v___f_1271_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1271_, 0, v_cmp_1270_);
v___x_1272_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1273_ = lean_box(1);
v___x_1274_ = l_List_forIn_x27_loop___redArg(v___x_1272_, v___f_1271_, v_l_1269_, v_r_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg___lam__0(lean_object* v_c_1275_, lean_object* v_a_1276_, lean_object* v_x_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_array_push(v_c_1275_, v_a_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg(lean_object* v_t_1282_){
_start:
{
lean_object* v___f_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___f_1283_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__0));
v___x_1284_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__1));
v___x_1285_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1283_, v___x_1284_, v_t_1282_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray(lean_object* v_00_u03b1_1286_, lean_object* v_cmp_1287_, lean_object* v_t_1288_){
_start:
{
lean_object* v___f_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___f_1289_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__0));
v___x_1290_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__1));
v___x_1291_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1289_, v___x_1290_, v_t_1288_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_cmp_1293_, lean_object* v_t_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Std_TreeSet_Raw_toArray(v_00_u03b1_1292_, v_cmp_1293_, v_t_1294_);
lean_dec_ref(v_cmp_1293_);
return v_res_1295_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__26, &l_Std_TreeSet_Raw___auto__1___closed__26_once, _init_l_Std_TreeSet_Raw___auto__1___closed__26);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray___redArg(lean_object* v_a_1297_, lean_object* v_cmp_1298_){
_start:
{
lean_object* v___f_1299_; lean_object* v___x_1300_; lean_object* v_r_1301_; size_t v_sz_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
v___f_1299_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1299_, 0, v_cmp_1298_);
v___x_1300_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1301_ = lean_box(1);
v_sz_1302_ = lean_array_size(v_a_1297_);
v___x_1303_ = ((size_t)0ULL);
v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1300_, v_a_1297_, v___f_1299_, v_sz_1302_, v___x_1303_, v_r_1301_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray(lean_object* v_00_u03b1_1305_, lean_object* v_a_1306_, lean_object* v_cmp_1307_){
_start:
{
lean_object* v___f_1308_; lean_object* v___x_1309_; lean_object* v_r_1310_; size_t v_sz_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___f_1308_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1308_, 0, v_cmp_1307_);
v___x_1309_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1310_ = lean_box(1);
v_sz_1311_ = lean_array_size(v_a_1306_);
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1309_, v_a_1306_, v___f_1308_, v_sz_1311_, v___x_1312_, v_r_1310_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0(lean_object* v_b_u2082_1316_, lean_object* v_x_1317_){
_start:
{
if (lean_obj_tag(v_x_1317_) == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_b_u2082_1316_);
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; 
v___x_1319_ = ((lean_object*)(l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0));
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1320_, lean_object* v_x_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_TreeSet_Raw_merge___redArg___lam__0(v_b_u2082_1320_, v_x_1321_);
lean_dec(v_x_1321_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__1(lean_object* v_cmp_1323_, lean_object* v_t_1324_, lean_object* v_a_1325_, lean_object* v_b_u2082_1326_){
_start:
{
lean_object* v___f_1327_; lean_object* v___x_1328_; 
v___f_1327_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1327_, 0, v_b_u2082_1326_);
v___x_1328_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_1323_, v_a_1325_, v___f_1327_, v_t_1324_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg(lean_object* v_cmp_1329_, lean_object* v_t_u2081_1330_, lean_object* v_t_u2082_1331_){
_start:
{
lean_object* v___f_1332_; lean_object* v___x_1333_; 
v___f_1332_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1332_, 0, v_cmp_1329_);
v___x_1333_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1332_, v_t_u2081_1330_, v_t_u2082_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge(lean_object* v_00_u03b1_1334_, lean_object* v_cmp_1335_, lean_object* v_t_u2081_1336_, lean_object* v_t_u2082_1337_){
_start:
{
lean_object* v___f_1338_; lean_object* v___x_1339_; 
v___f_1338_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1338_, 0, v_cmp_1335_);
v___x_1339_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1338_, v_t_u2081_1336_, v_t_u2082_1337_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_1340_, lean_object* v_a_1341_, lean_object* v_____s_1342_){
_start:
{
uint8_t v___x_1343_; 
lean_inc(v_____s_1342_);
lean_inc(v_a_1341_);
lean_inc_ref(v_cmp_1340_);
v___x_1343_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1340_, v_a_1341_, v_____s_1342_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_box(0);
v___x_1345_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1340_, v_a_1341_, v___x_1344_, v_____s_1342_);
v___x_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; 
lean_dec(v_a_1341_);
lean_dec_ref(v_cmp_1340_);
v___x_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1347_, 0, v_____s_1342_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg(lean_object* v_cmp_1348_, lean_object* v_inst_1349_, lean_object* v_t_1350_, lean_object* v_l_1351_){
_start:
{
lean_object* v___f_1352_; lean_object* v___x_1353_; 
v___f_1352_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1352_, 0, v_cmp_1348_);
v___x_1353_ = lean_apply_4(v_inst_1349_, lean_box(0), v_l_1351_, v_t_1350_, v___f_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany(lean_object* v_00_u03b1_1354_, lean_object* v_cmp_1355_, lean_object* v_00_u03c1_1356_, lean_object* v_inst_1357_, lean_object* v_t_1358_, lean_object* v_l_1359_){
_start:
{
lean_object* v___f_1360_; lean_object* v___x_1361_; 
v___f_1360_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1360_, 0, v_cmp_1355_);
v___x_1361_ = lean_apply_4(v_inst_1357_, lean_box(0), v_l_1359_, v_t_1358_, v___f_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union___redArg(lean_object* v_cmp_1362_, lean_object* v_t_u2081_1363_, lean_object* v_t_u2082_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_1362_, v_t_u2081_1363_, v_t_u2082_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union(lean_object* v_00_u03b1_1366_, lean_object* v_cmp_1367_, lean_object* v_t_u2081_1368_, lean_object* v_t_u2082_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_1367_, v_t_u2081_1368_, v_t_u2082_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion___redArg(lean_object* v_cmp_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_union), 4, 2);
lean_closure_set(v___x_1372_, 0, lean_box(0));
lean_closure_set(v___x_1372_, 1, v_cmp_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion(lean_object* v_00_u03b1_1373_, lean_object* v_cmp_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_union), 4, 2);
lean_closure_set(v___x_1375_, 0, lean_box(0));
lean_closure_set(v___x_1375_, 1, v_cmp_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter___redArg(lean_object* v_cmp_1376_, lean_object* v_t_u2081_1377_, lean_object* v_t_u2082_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_1376_, v_t_u2081_1377_, v_t_u2082_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter(lean_object* v_00_u03b1_1380_, lean_object* v_cmp_1381_, lean_object* v_t_u2081_1382_, lean_object* v_t_u2082_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_1381_, v_t_u2081_1382_, v_t_u2082_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter___redArg(lean_object* v_cmp_1385_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_inter), 4, 2);
lean_closure_set(v___x_1386_, 0, lean_box(0));
lean_closure_set(v___x_1386_, 1, v_cmp_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter(lean_object* v_00_u03b1_1387_, lean_object* v_cmp_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_inter), 4, 2);
lean_closure_set(v___x_1389_, 0, lean_box(0));
lean_closure_set(v___x_1389_, 1, v_cmp_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
if (lean_obj_tag(v_x_1390_) == 0)
{
if (lean_obj_tag(v_x_1391_) == 0)
{
uint8_t v___x_1392_; 
v___x_1392_ = 1;
return v___x_1392_;
}
else
{
uint8_t v___x_1393_; 
v___x_1393_ = 0;
return v___x_1393_;
}
}
else
{
if (lean_obj_tag(v_x_1391_) == 0)
{
uint8_t v___x_1394_; 
v___x_1394_ = 0;
return v___x_1394_;
}
else
{
uint8_t v___x_1395_; 
v___x_1395_ = 1;
return v___x_1395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1396_, lean_object* v_x_1397_){
_start:
{
uint8_t v_res_1398_; lean_object* v_r_1399_; 
v_res_1398_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v_x_1396_, v_x_1397_);
lean_dec(v_x_1397_);
lean_dec(v_x_1396_);
v_r_1399_ = lean_box(v_res_1398_);
return v_r_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_cmp_1400_, lean_object* v_t_1401_, lean_object* v_k_1402_){
_start:
{
if (lean_obj_tag(v_t_1401_) == 0)
{
lean_object* v_k_1403_; lean_object* v_v_1404_; lean_object* v_l_1405_; lean_object* v_r_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v_k_1403_ = lean_ctor_get(v_t_1401_, 1);
lean_inc(v_k_1403_);
v_v_1404_ = lean_ctor_get(v_t_1401_, 2);
lean_inc(v_v_1404_);
v_l_1405_ = lean_ctor_get(v_t_1401_, 3);
lean_inc(v_l_1405_);
v_r_1406_ = lean_ctor_get(v_t_1401_, 4);
lean_inc(v_r_1406_);
lean_dec_ref(v_t_1401_);
lean_inc_ref(v_cmp_1400_);
lean_inc(v_k_1402_);
v___x_1407_ = lean_apply_2(v_cmp_1400_, v_k_1402_, v_k_1403_);
v___x_1408_ = lean_unbox(v___x_1407_);
switch(v___x_1408_)
{
case 0:
{
lean_dec(v_r_1406_);
lean_dec(v_v_1404_);
v_t_1401_ = v_l_1405_;
goto _start;
}
case 1:
{
lean_object* v___x_1410_; 
lean_dec(v_r_1406_);
lean_dec(v_l_1405_);
lean_dec(v_k_1402_);
lean_dec_ref(v_cmp_1400_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v_v_1404_);
return v___x_1410_;
}
default: 
{
lean_dec(v_l_1405_);
lean_dec(v_v_1404_);
v_t_1401_ = v_r_1406_;
goto _start;
}
}
}
else
{
lean_object* v___x_1412_; 
lean_dec(v_k_1402_);
lean_dec_ref(v_cmp_1400_);
v___x_1412_ = lean_box(0);
return v___x_1412_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_cmp_1413_, lean_object* v_t_u2082_1414_, lean_object* v_init_1415_, lean_object* v_x_1416_){
_start:
{
if (lean_obj_tag(v_x_1416_) == 0)
{
lean_object* v_k_1417_; lean_object* v_v_1418_; lean_object* v_l_1419_; lean_object* v_r_1420_; lean_object* v___x_1421_; 
v_k_1417_ = lean_ctor_get(v_x_1416_, 1);
lean_inc(v_k_1417_);
v_v_1418_ = lean_ctor_get(v_x_1416_, 2);
lean_inc(v_v_1418_);
v_l_1419_ = lean_ctor_get(v_x_1416_, 3);
lean_inc(v_l_1419_);
v_r_1420_ = lean_ctor_get(v_x_1416_, 4);
lean_inc(v_r_1420_);
lean_dec_ref(v_x_1416_);
lean_inc(v_t_u2082_1414_);
lean_inc_ref(v_cmp_1413_);
v___x_1421_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_1413_, v_t_u2082_1414_, v_init_1415_, v_l_1419_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_dec(v_r_1420_);
lean_dec(v_v_1418_);
lean_dec(v_k_1417_);
lean_dec(v_t_u2082_1414_);
lean_dec_ref(v_cmp_1413_);
return v___x_1421_;
}
else
{
lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1437_; 
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v___x_1421_, 0);
lean_dec(v_unused_1438_);
v___x_1423_ = v___x_1421_;
v_isShared_1424_ = v_isSharedCheck_1437_;
goto v_resetjp_1422_;
}
else
{
lean_dec(v___x_1421_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1437_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1425_ = lean_box(0);
lean_inc(v_t_u2082_1414_);
lean_inc_ref(v_cmp_1413_);
v___x_1426_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1413_, v_t_u2082_1414_, v_k_1417_);
v___x_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_v_1418_);
v___x_1428_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v___x_1426_, v___x_1427_);
lean_dec_ref(v___x_1427_);
lean_dec(v___x_1426_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
lean_dec(v_r_1420_);
lean_dec(v_t_u2082_1414_);
lean_dec_ref(v_cmp_1413_);
v___x_1429_ = lean_box(v___x_1428_);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1425_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set_tag(v___x_1423_, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1431_);
v___x_1433_ = v___x_1423_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
else
{
lean_object* v___x_1435_; 
lean_del_object(v___x_1423_);
v___x_1435_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v_init_1415_ = v___x_1435_;
v_x_1416_ = v_r_1420_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1439_; 
lean_dec(v_t_u2082_1414_);
lean_dec_ref(v_cmp_1413_);
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v_init_1415_);
return v___x_1439_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_1440_, lean_object* v_t_u2081_1441_, lean_object* v_t_u2082_1442_){
_start:
{
lean_object* v___y_1444_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1457_; 
if (lean_obj_tag(v_t_u2081_1441_) == 0)
{
lean_object* v_size_1460_; 
v_size_1460_ = lean_ctor_get(v_t_u2081_1441_, 0);
lean_inc(v_size_1460_);
v___y_1457_ = v_size_1460_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_unsigned_to_nat(0u);
v___y_1457_ = v___x_1461_;
goto v___jp_1456_;
}
v___jp_1443_:
{
lean_object* v_fst_1445_; 
v_fst_1445_ = lean_ctor_get(v___y_1444_, 0);
lean_inc(v_fst_1445_);
lean_dec_ref(v___y_1444_);
if (lean_obj_tag(v_fst_1445_) == 0)
{
uint8_t v___x_1446_; 
v___x_1446_ = 1;
return v___x_1446_;
}
else
{
lean_object* v_val_1447_; uint8_t v___x_1448_; 
v_val_1447_ = lean_ctor_get(v_fst_1445_, 0);
lean_inc(v_val_1447_);
lean_dec_ref(v_fst_1445_);
v___x_1448_ = lean_unbox(v_val_1447_);
lean_dec(v_val_1447_);
return v___x_1448_;
}
}
v___jp_1449_:
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_nat_dec_eq(v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec(v___y_1450_);
if (v___x_1452_ == 0)
{
lean_dec(v_t_u2082_1442_);
lean_dec(v_t_u2081_1441_);
lean_dec_ref(v_cmp_1440_);
return v___x_1452_;
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_a_1455_; 
v___x_1453_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___x_1454_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_1440_, v_t_u2082_1442_, v___x_1453_, v_t_u2081_1441_);
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref(v___x_1454_);
v___y_1444_ = v_a_1455_;
goto v___jp_1443_;
}
}
v___jp_1456_:
{
if (lean_obj_tag(v_t_u2082_1442_) == 0)
{
lean_object* v_size_1458_; 
v_size_1458_ = lean_ctor_get(v_t_u2082_1442_, 0);
lean_inc(v_size_1458_);
v___y_1450_ = v___y_1457_;
v___y_1451_ = v_size_1458_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_unsigned_to_nat(0u);
v___y_1450_ = v___y_1457_;
v___y_1451_ = v___x_1459_;
goto v___jp_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_1462_, lean_object* v_t_u2081_1463_, lean_object* v_t_u2082_1464_){
_start:
{
uint8_t v_res_1465_; lean_object* v_r_1466_; 
v_res_1465_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1462_, v_t_u2081_1463_, v_t_u2082_1464_);
v_r_1466_ = lean_box(v_res_1465_);
return v_r_1466_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_beq___redArg(lean_object* v_cmp_1467_, lean_object* v_t_u2081_1468_, lean_object* v_t_u2082_1469_){
_start:
{
uint8_t v___x_1470_; 
v___x_1470_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1467_, v_t_u2081_1468_, v_t_u2082_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___redArg___boxed(lean_object* v_cmp_1471_, lean_object* v_t_u2081_1472_, lean_object* v_t_u2082_1473_){
_start:
{
uint8_t v_res_1474_; lean_object* v_r_1475_; 
v_res_1474_ = l_Std_TreeSet_Raw_beq___redArg(v_cmp_1471_, v_t_u2081_1472_, v_t_u2082_1473_);
v_r_1475_ = lean_box(v_res_1474_);
return v_r_1475_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_beq(lean_object* v_00_u03b1_1476_, lean_object* v_cmp_1477_, lean_object* v_t_u2081_1478_, lean_object* v_t_u2082_1479_){
_start:
{
uint8_t v___x_1480_; 
v___x_1480_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1477_, v_t_u2081_1478_, v_t_u2082_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___boxed(lean_object* v_00_u03b1_1481_, lean_object* v_cmp_1482_, lean_object* v_t_u2081_1483_, lean_object* v_t_u2082_1484_){
_start:
{
uint8_t v_res_1485_; lean_object* v_r_1486_; 
v_res_1485_ = l_Std_TreeSet_Raw_beq(v_00_u03b1_1481_, v_cmp_1482_, v_t_u2081_1483_, v_t_u2082_1484_);
v_r_1486_ = lean_box(v_res_1485_);
return v_r_1486_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(lean_object* v_cmp_1487_, lean_object* v_t_u2081_1488_, lean_object* v_t_u2082_1489_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1487_, v_t_u2081_1488_, v_t_u2082_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg___boxed(lean_object* v_cmp_1491_, lean_object* v_t_u2081_1492_, lean_object* v_t_u2082_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(v_cmp_1491_, v_t_u2081_1492_, v_t_u2082_1493_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(lean_object* v_00_u03b1_1496_, lean_object* v_cmp_1497_, lean_object* v_t_u2081_1498_, lean_object* v_t_u2082_1499_){
_start:
{
uint8_t v___x_1500_; 
v___x_1500_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1497_, v_t_u2081_1498_, v_t_u2082_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___boxed(lean_object* v_00_u03b1_1501_, lean_object* v_cmp_1502_, lean_object* v_t_u2081_1503_, lean_object* v_t_u2082_1504_){
_start:
{
uint8_t v_res_1505_; lean_object* v_r_1506_; 
v_res_1505_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(v_00_u03b1_1501_, v_cmp_1502_, v_t_u2081_1503_, v_t_u2082_1504_);
v_r_1506_ = lean_box(v_res_1505_);
return v_r_1506_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(lean_object* v_cmp_1507_, lean_object* v_t_u2081_1508_, lean_object* v_t_u2082_1509_){
_start:
{
uint8_t v___x_1510_; 
v___x_1510_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1507_, v_t_u2081_1508_, v_t_u2082_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_1511_, lean_object* v_t_u2081_1512_, lean_object* v_t_u2082_1513_){
_start:
{
uint8_t v_res_1514_; lean_object* v_r_1515_; 
v_res_1514_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(v_cmp_1511_, v_t_u2081_1512_, v_t_u2082_1513_);
v_r_1515_ = lean_box(v_res_1514_);
return v_r_1515_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(lean_object* v_00_u03b1_1516_, lean_object* v_cmp_1517_, lean_object* v_t_u2081_1518_, lean_object* v_t_u2082_1519_){
_start:
{
uint8_t v___x_1520_; 
v___x_1520_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1517_, v_t_u2081_1518_, v_t_u2082_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1521_, lean_object* v_cmp_1522_, lean_object* v_t_u2081_1523_, lean_object* v_t_u2082_1524_){
_start:
{
uint8_t v_res_1525_; lean_object* v_r_1526_; 
v_res_1525_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(v_00_u03b1_1521_, v_cmp_1522_, v_t_u2081_1523_, v_t_u2082_1524_);
v_r_1526_ = lean_box(v_res_1525_);
return v_r_1526_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1527_, lean_object* v_cmp_1528_, lean_object* v_t_u2081_1529_, lean_object* v_t_u2082_1530_){
_start:
{
uint8_t v___x_1531_; 
v___x_1531_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1528_, v_t_u2081_1529_, v_t_u2082_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1532_, lean_object* v_cmp_1533_, lean_object* v_t_u2081_1534_, lean_object* v_t_u2082_1535_){
_start:
{
uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_res_1536_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(v_00_u03b1_1532_, v_cmp_1533_, v_t_u2081_1534_, v_t_u2082_1535_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1538_, lean_object* v_cmp_1539_, lean_object* v_00_u03b4_1540_, lean_object* v_t_1541_, lean_object* v_k_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1539_, v_t_1541_, v_k_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1544_, lean_object* v_cmp_1545_, lean_object* v_t_u2082_1546_, lean_object* v_init_1547_, lean_object* v_x_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_1545_, v_t_u2082_1546_, v_init_1547_, v_x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq___redArg(lean_object* v_cmp_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_beq___boxed), 4, 2);
lean_closure_set(v___x_1551_, 0, lean_box(0));
lean_closure_set(v___x_1551_, 1, v_cmp_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq(lean_object* v_00_u03b1_1552_, lean_object* v_cmp_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_beq___boxed), 4, 2);
lean_closure_set(v___x_1554_, 0, lean_box(0));
lean_closure_set(v___x_1554_, 1, v_cmp_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff___redArg(lean_object* v_cmp_1555_, lean_object* v_t_u2081_1556_, lean_object* v_t_u2082_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_1555_, v_t_u2081_1556_, v_t_u2082_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff(lean_object* v_00_u03b1_1559_, lean_object* v_cmp_1560_, lean_object* v_t_u2081_1561_, lean_object* v_t_u2082_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_1560_, v_t_u2081_1561_, v_t_u2082_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff___redArg(lean_object* v_cmp_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_diff), 4, 2);
lean_closure_set(v___x_1565_, 0, lean_box(0));
lean_closure_set(v___x_1565_, 1, v_cmp_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff(lean_object* v_00_u03b1_1566_, lean_object* v_cmp_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_diff), 4, 2);
lean_closure_set(v___x_1568_, 0, lean_box(0));
lean_closure_set(v___x_1568_, 1, v_cmp_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_1569_, lean_object* v_a_1570_, lean_object* v_____s_1571_){
_start:
{
lean_object* v_r_1572_; lean_object* v___x_1573_; 
v_r_1572_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_1569_, v_a_1570_, v_____s_1571_);
v___x_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_r_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg(lean_object* v_cmp_1574_, lean_object* v_inst_1575_, lean_object* v_t_1576_, lean_object* v_l_1577_){
_start:
{
lean_object* v___f_1578_; lean_object* v___x_1579_; 
v___f_1578_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1578_, 0, v_cmp_1574_);
v___x_1579_ = lean_apply_4(v_inst_1575_, lean_box(0), v_l_1577_, v_t_1576_, v___f_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany(lean_object* v_00_u03b1_1580_, lean_object* v_cmp_1581_, lean_object* v_00_u03c1_1582_, lean_object* v_inst_1583_, lean_object* v_t_1584_, lean_object* v_l_1585_){
_start:
{
lean_object* v___f_1586_; lean_object* v___x_1587_; 
v___f_1586_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1586_, 0, v_cmp_1581_);
v___x_1587_ = lean_apply_4(v_inst_1583_, lean_box(0), v_l_1585_, v_t_1584_, v___f_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1(lean_object* v___f_1591_, lean_object* v_inst_1592_, lean_object* v_m_1593_, lean_object* v_prec_1594_){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1595_ = ((lean_object*)(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1));
v___x_1596_ = lean_box(0);
v___x_1597_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1598_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1597_, v___f_1591_, v___x_1596_, v_m_1593_);
v___x_1599_ = l_List_repr___redArg(v_inst_1592_, v___x_1598_);
v___x_1600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1595_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = l_Repr_addAppParen(v___x_1600_, v_prec_1594_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_1602_, lean_object* v_inst_1603_, lean_object* v_m_1604_, lean_object* v_prec_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Std_TreeSet_Raw_instRepr___redArg___lam__1(v___f_1602_, v_inst_1603_, v_m_1604_, v_prec_1605_);
lean_dec(v_prec_1605_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg(lean_object* v_inst_1607_){
_start:
{
lean_object* v___f_1608_; lean_object* v___f_1609_; 
v___f_1608_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___f_1609_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1609_, 0, v___f_1608_);
lean_closure_set(v___f_1609_, 1, v_inst_1607_);
return v___f_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr(lean_object* v_00_u03b1_1610_, lean_object* v_cmp_1611_, lean_object* v_inst_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Std_TreeSet_Raw_instRepr___redArg(v_inst_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___boxed(lean_object* v_00_u03b1_1614_, lean_object* v_cmp_1615_, lean_object* v_inst_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Std_TreeSet_Raw_instRepr(v_00_u03b1_1614_, v_cmp_1615_, v_inst_1616_);
lean_dec_ref(v_cmp_1615_);
return v_res_1617_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_TreeSet_Raw___auto__1 = _init_l_Std_TreeSet_Raw___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw___auto__1);
l_Std_TreeSet_Raw_ofList___auto__1 = _init_l_Std_TreeSet_Raw_ofList___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_ofList___auto__1);
l_Std_TreeSet_Raw_ofArray___auto__1 = _init_l_Std_TreeSet_Raw_ofArray___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_ofArray___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeSet_Raw_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
