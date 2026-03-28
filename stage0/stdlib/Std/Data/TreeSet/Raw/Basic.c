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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_currMacroScope_168_ = lean_ctor_get(v_a_161_, 2);
v_ref_169_ = lean_ctor_get(v_a_161_, 5);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = l_Lean_Syntax_getArg(v_x_160_, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(2u);
v___x_173_ = l_Lean_Syntax_getArg(v_x_160_, v___x_172_);
lean_dec(v_x_160_);
v___x_174_ = 0;
v___x_175_ = l_Lean_SourceInfo_fromRef(v_ref_169_, v___x_174_);
v___x_176_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2));
v___x_177_ = lean_obj_once(&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4, &l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4_once, _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4);
v___x_178_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_168_);
lean_inc(v_quotContext_167_);
v___x_179_ = l_Lean_addMacroScope(v_quotContext_167_, v___x_178_, v_currMacroScope_168_);
v___x_180_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10));
lean_inc_n(v___x_175_, 2);
v___x_181_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_181_, 0, v___x_175_);
lean_ctor_set(v___x_181_, 1, v___x_177_);
lean_ctor_set(v___x_181_, 2, v___x_179_);
lean_ctor_set(v___x_181_, 3, v___x_180_);
v___x_182_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__9));
v___x_183_ = l_Lean_Syntax_node2(v___x_175_, v___x_182_, v___x_171_, v___x_173_);
v___x_184_ = l_Lean_Syntax_node2(v___x_175_, v___x_176_, v___x_181_, v___x_183_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_a_162_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___boxed(lean_object* v_x_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(v_x_186_, v_a_187_, v_a_188_);
lean_dec_ref(v_a_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(lean_object* v_x_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2));
lean_inc(v_x_193_);
v___x_197_ = l_Lean_Syntax_isOfKind(v_x_193_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v_x_193_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v_a_195_);
return v___x_199_;
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = l_Lean_Syntax_getArg(v_x_193_, v___x_200_);
v___x_202_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1));
lean_inc(v___x_201_);
v___x_203_ = l_Lean_Syntax_isOfKind(v___x_201_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v___x_201_);
lean_dec(v_x_193_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v_a_195_);
return v___x_205_;
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = l_Lean_Syntax_getArg(v_x_193_, v___x_206_);
lean_dec(v_x_193_);
v___x_208_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_207_);
v___x_209_ = l_Lean_Syntax_matchesNull(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v___x_207_);
lean_dec(v___x_201_);
v___x_210_ = lean_box(0);
v___x_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v_a_195_);
return v___x_211_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_ref_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_212_ = l_Lean_Syntax_getArg(v___x_207_, v___x_200_);
v___x_213_ = l_Lean_Syntax_getArg(v___x_207_, v___x_206_);
lean_dec(v___x_207_);
v_ref_214_ = l_Lean_replaceRef(v___x_201_, v_a_194_);
lean_dec(v___x_201_);
v___x_215_ = 0;
v___x_216_ = l_Lean_SourceInfo_fromRef(v_ref_214_, v___x_215_);
lean_dec(v_ref_214_);
v___x_217_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__4));
v___x_218_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__7));
lean_inc(v___x_216_);
v___x_219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_216_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = l_Lean_Syntax_node3(v___x_216_, v___x_217_, v___x_212_, v___x_219_, v___x_213_);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v_a_195_);
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___boxed(lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(v_x_222_, v_a_223_, v_a_224_);
lean_dec(v_a_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert___redArg(lean_object* v_cmp_226_, lean_object* v_l_227_, lean_object* v_a_228_){
_start:
{
uint8_t v___x_229_; 
lean_inc(v_l_227_);
lean_inc(v_a_228_);
lean_inc_ref(v_cmp_226_);
v___x_229_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_226_, v_a_228_, v_l_227_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_box(0);
v___x_231_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_226_, v_a_228_, v___x_230_, v_l_227_);
return v___x_231_;
}
else
{
lean_dec(v_a_228_);
lean_dec_ref(v_cmp_226_);
return v_l_227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert(lean_object* v_00_u03b1_232_, lean_object* v_cmp_233_, lean_object* v_l_234_, lean_object* v_a_235_){
_start:
{
uint8_t v___x_236_; 
lean_inc(v_l_234_);
lean_inc(v_a_235_);
lean_inc_ref(v_cmp_233_);
v___x_236_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_233_, v_a_235_, v_l_234_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_box(0);
v___x_238_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_233_, v_a_235_, v___x_237_, v_l_234_);
return v___x_238_;
}
else
{
lean_dec(v_a_235_);
lean_dec_ref(v_cmp_233_);
return v_l_234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg___lam__0(lean_object* v_cmp_239_, lean_object* v_e_240_){
_start:
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_box(1);
lean_inc(v_e_240_);
lean_inc_ref(v_cmp_239_);
v___x_242_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_239_, v_e_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_box(0);
v___x_244_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_239_, v_e_240_, v___x_243_, v___x_241_);
return v___x_244_;
}
else
{
lean_dec(v_e_240_);
lean_dec_ref(v_cmp_239_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg(lean_object* v_cmp_245_){
_start:
{
lean_object* v___f_246_; 
v___f_246_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_246_, 0, v_cmp_245_);
return v___f_246_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton(lean_object* v_00_u03b1_247_, lean_object* v_cmp_248_){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_249_, 0, v_cmp_248_);
return v___f_249_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg___lam__0(lean_object* v_cmp_250_, lean_object* v_e_251_, lean_object* v_s_252_){
_start:
{
uint8_t v___x_253_; 
lean_inc(v_s_252_);
lean_inc(v_e_251_);
lean_inc_ref(v_cmp_250_);
v___x_253_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_250_, v_e_251_, v_s_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_box(0);
v___x_255_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_250_, v_e_251_, v___x_254_, v_s_252_);
return v___x_255_;
}
else
{
lean_dec(v_e_251_);
lean_dec_ref(v_cmp_250_);
return v_s_252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg(lean_object* v_cmp_256_){
_start:
{
lean_object* v___f_257_; 
v___f_257_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_257_, 0, v_cmp_256_);
return v___f_257_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert(lean_object* v_00_u03b1_258_, lean_object* v_cmp_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_260_, 0, v_cmp_259_);
return v___f_260_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert___redArg(lean_object* v_cmp_261_, lean_object* v_t_262_, lean_object* v_a_263_){
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
v___x_266_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_261_, v_a_263_, v___x_265_, v_t_262_);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert(lean_object* v_00_u03b1_271_, lean_object* v_cmp_272_, lean_object* v_t_273_, lean_object* v_a_274_){
_start:
{
uint8_t v___x_275_; 
lean_inc(v_t_273_);
lean_inc(v_a_274_);
lean_inc_ref(v_cmp_272_);
v___x_275_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_272_, v_a_274_, v_t_273_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_276_ = lean_box(0);
v___x_277_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_272_, v_a_274_, v___x_276_, v_t_273_);
v___x_278_ = lean_box(v___x_275_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_277_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v_a_274_);
lean_dec_ref(v_cmp_272_);
v___x_280_ = lean_box(v___x_275_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v_t_273_);
return v___x_281_;
}
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_contains___redArg(lean_object* v_cmp_282_, lean_object* v_l_283_, lean_object* v_a_284_){
_start:
{
uint8_t v___x_285_; 
v___x_285_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_282_, v_a_284_, v_l_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___redArg___boxed(lean_object* v_cmp_286_, lean_object* v_l_287_, lean_object* v_a_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Std_TreeSet_Raw_contains___redArg(v_cmp_286_, v_l_287_, v_a_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_contains(lean_object* v_00_u03b1_291_, lean_object* v_cmp_292_, lean_object* v_l_293_, lean_object* v_a_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_292_, v_a_294_, v_l_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___boxed(lean_object* v_00_u03b1_296_, lean_object* v_cmp_297_, lean_object* v_l_298_, lean_object* v_a_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_TreeSet_Raw_contains(v_00_u03b1_296_, v_cmp_297_, v_l_298_, v_a_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership(lean_object* v_00_u03b1_302_, lean_object* v_cmp_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lean_box(0);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___boxed(lean_object* v_00_u03b1_305_, lean_object* v_cmp_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_TreeSet_Raw_instMembership(v_00_u03b1_305_, v_cmp_306_);
lean_dec_ref(v_cmp_306_);
return v_res_307_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableMem___redArg(lean_object* v_cmp_308_, lean_object* v_t_309_, lean_object* v_a_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_308_, v_a_310_, v_t_309_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_312_, lean_object* v_t_313_, lean_object* v_a_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Std_TreeSet_Raw_instDecidableMem___redArg(v_cmp_312_, v_t_313_, v_a_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableMem(lean_object* v_00_u03b1_317_, lean_object* v_cmp_318_, lean_object* v_t_319_, lean_object* v_a_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_318_, v_a_320_, v_t_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_322_, lean_object* v_cmp_323_, lean_object* v_t_324_, lean_object* v_a_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Std_TreeSet_Raw_instDecidableMem(v_00_u03b1_322_, v_cmp_323_, v_t_324_, v_a_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg(lean_object* v_t_328_){
_start:
{
if (lean_obj_tag(v_t_328_) == 0)
{
lean_object* v_size_329_; 
v_size_329_ = lean_ctor_get(v_t_328_, 0);
lean_inc(v_size_329_);
return v_size_329_;
}
else
{
lean_object* v___x_330_; 
v___x_330_ = lean_unsigned_to_nat(0u);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg___boxed(lean_object* v_t_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_TreeSet_Raw_size___redArg(v_t_331_);
lean_dec(v_t_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size(lean_object* v_00_u03b1_333_, lean_object* v_cmp_334_, lean_object* v_t_335_){
_start:
{
if (lean_obj_tag(v_t_335_) == 0)
{
lean_object* v_size_336_; 
v_size_336_ = lean_ctor_get(v_t_335_, 0);
lean_inc(v_size_336_);
return v_size_336_;
}
else
{
lean_object* v___x_337_; 
v___x_337_ = lean_unsigned_to_nat(0u);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___boxed(lean_object* v_00_u03b1_338_, lean_object* v_cmp_339_, lean_object* v_t_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_TreeSet_Raw_size(v_00_u03b1_338_, v_cmp_339_, v_t_340_);
lean_dec(v_t_340_);
lean_dec_ref(v_cmp_339_);
return v_res_341_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_isEmpty___redArg(lean_object* v_t_342_){
_start:
{
if (lean_obj_tag(v_t_342_) == 0)
{
uint8_t v___x_343_; 
v___x_343_ = 0;
return v___x_343_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = 1;
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___redArg___boxed(lean_object* v_t_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Std_TreeSet_Raw_isEmpty___redArg(v_t_345_);
lean_dec(v_t_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_isEmpty(lean_object* v_00_u03b1_348_, lean_object* v_cmp_349_, lean_object* v_t_350_){
_start:
{
if (lean_obj_tag(v_t_350_) == 0)
{
uint8_t v___x_351_; 
v___x_351_ = 0;
return v___x_351_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = 1;
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___boxed(lean_object* v_00_u03b1_353_, lean_object* v_cmp_354_, lean_object* v_t_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Std_TreeSet_Raw_isEmpty(v_00_u03b1_353_, v_cmp_354_, v_t_355_);
lean_dec(v_t_355_);
lean_dec_ref(v_cmp_354_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase___redArg(lean_object* v_cmp_358_, lean_object* v_t_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_358_, v_a_360_, v_t_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase(lean_object* v_00_u03b1_362_, lean_object* v_cmp_363_, lean_object* v_t_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_363_, v_a_365_, v_t_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f___redArg(lean_object* v_cmp_367_, lean_object* v_t_368_, lean_object* v_a_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_367_, v_t_368_, v_a_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f(lean_object* v_00_u03b1_371_, lean_object* v_cmp_372_, lean_object* v_t_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_372_, v_t_373_, v_a_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get___redArg(lean_object* v_cmp_376_, lean_object* v_t_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_376_, v_t_377_, v_a_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get(lean_object* v_00_u03b1_380_, lean_object* v_cmp_381_, lean_object* v_t_382_, lean_object* v_a_383_, lean_object* v_h_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_381_, v_t_382_, v_a_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___redArg(lean_object* v_cmp_386_, lean_object* v_inst_387_, lean_object* v_t_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_386_, v_t_388_, v_a_389_, v_inst_387_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___redArg___boxed(lean_object* v_cmp_391_, lean_object* v_inst_392_, lean_object* v_t_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_TreeSet_Raw_get_x21___redArg(v_cmp_391_, v_inst_392_, v_t_393_, v_a_394_);
lean_dec(v_inst_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21(lean_object* v_00_u03b1_396_, lean_object* v_cmp_397_, lean_object* v_inst_398_, lean_object* v_t_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_397_, v_t_399_, v_a_400_, v_inst_398_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___boxed(lean_object* v_00_u03b1_402_, lean_object* v_cmp_403_, lean_object* v_inst_404_, lean_object* v_t_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_TreeSet_Raw_get_x21(v_00_u03b1_402_, v_cmp_403_, v_inst_404_, v_t_405_, v_a_406_);
lean_dec(v_inst_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg(lean_object* v_cmp_408_, lean_object* v_t_409_, lean_object* v_a_410_, lean_object* v_fallback_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_408_, v_t_409_, v_a_410_, v_fallback_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg___boxed(lean_object* v_cmp_413_, lean_object* v_t_414_, lean_object* v_a_415_, lean_object* v_fallback_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_TreeSet_Raw_getD___redArg(v_cmp_413_, v_t_414_, v_a_415_, v_fallback_416_);
lean_dec(v_fallback_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD(lean_object* v_00_u03b1_418_, lean_object* v_cmp_419_, lean_object* v_t_420_, lean_object* v_a_421_, lean_object* v_fallback_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_419_, v_t_420_, v_a_421_, v_fallback_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___boxed(lean_object* v_00_u03b1_424_, lean_object* v_cmp_425_, lean_object* v_t_426_, lean_object* v_a_427_, lean_object* v_fallback_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_TreeSet_Raw_getD(v_00_u03b1_424_, v_cmp_425_, v_t_426_, v_a_427_, v_fallback_428_);
lean_dec(v_fallback_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg(lean_object* v_t_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg___boxed(lean_object* v_t_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_TreeSet_Raw_min_x3f___redArg(v_t_432_);
lean_dec(v_t_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f(lean_object* v_00_u03b1_434_, lean_object* v_cmp_435_, lean_object* v_t_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___boxed(lean_object* v_00_u03b1_438_, lean_object* v_cmp_439_, lean_object* v_t_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_TreeSet_Raw_min_x3f(v_00_u03b1_438_, v_cmp_439_, v_t_440_);
lean_dec(v_t_440_);
lean_dec_ref(v_cmp_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg(lean_object* v_inst_442_, lean_object* v_t_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_442_, v_t_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg___boxed(lean_object* v_inst_445_, lean_object* v_t_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_TreeSet_Raw_min_x21___redArg(v_inst_445_, v_t_446_);
lean_dec(v_t_446_);
lean_dec(v_inst_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21(lean_object* v_00_u03b1_448_, lean_object* v_cmp_449_, lean_object* v_inst_450_, lean_object* v_t_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_450_, v_t_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___boxed(lean_object* v_00_u03b1_453_, lean_object* v_cmp_454_, lean_object* v_inst_455_, lean_object* v_t_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_TreeSet_Raw_min_x21(v_00_u03b1_453_, v_cmp_454_, v_inst_455_, v_t_456_);
lean_dec(v_t_456_);
lean_dec(v_inst_455_);
lean_dec_ref(v_cmp_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg(lean_object* v_t_458_, lean_object* v_fallback_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_458_, v_fallback_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg___boxed(lean_object* v_t_461_, lean_object* v_fallback_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Std_TreeSet_Raw_minD___redArg(v_t_461_, v_fallback_462_);
lean_dec(v_fallback_462_);
lean_dec(v_t_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD(lean_object* v_00_u03b1_464_, lean_object* v_cmp_465_, lean_object* v_t_466_, lean_object* v_fallback_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_466_, v_fallback_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___boxed(lean_object* v_00_u03b1_469_, lean_object* v_cmp_470_, lean_object* v_t_471_, lean_object* v_fallback_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_TreeSet_Raw_minD(v_00_u03b1_469_, v_cmp_470_, v_t_471_, v_fallback_472_);
lean_dec(v_fallback_472_);
lean_dec(v_t_471_);
lean_dec_ref(v_cmp_470_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg(lean_object* v_t_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg___boxed(lean_object* v_t_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_TreeSet_Raw_max_x3f___redArg(v_t_476_);
lean_dec(v_t_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f(lean_object* v_00_u03b1_478_, lean_object* v_cmp_479_, lean_object* v_t_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___boxed(lean_object* v_00_u03b1_482_, lean_object* v_cmp_483_, lean_object* v_t_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_TreeSet_Raw_max_x3f(v_00_u03b1_482_, v_cmp_483_, v_t_484_);
lean_dec(v_t_484_);
lean_dec_ref(v_cmp_483_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg(lean_object* v_inst_486_, lean_object* v_t_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_486_, v_t_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg___boxed(lean_object* v_inst_489_, lean_object* v_t_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_TreeSet_Raw_max_x21___redArg(v_inst_489_, v_t_490_);
lean_dec(v_t_490_);
lean_dec(v_inst_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21(lean_object* v_00_u03b1_492_, lean_object* v_cmp_493_, lean_object* v_inst_494_, lean_object* v_t_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_494_, v_t_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___boxed(lean_object* v_00_u03b1_497_, lean_object* v_cmp_498_, lean_object* v_inst_499_, lean_object* v_t_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_TreeSet_Raw_max_x21(v_00_u03b1_497_, v_cmp_498_, v_inst_499_, v_t_500_);
lean_dec(v_t_500_);
lean_dec(v_inst_499_);
lean_dec_ref(v_cmp_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg(lean_object* v_t_502_, lean_object* v_fallback_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_502_, v_fallback_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg___boxed(lean_object* v_t_505_, lean_object* v_fallback_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_TreeSet_Raw_maxD___redArg(v_t_505_, v_fallback_506_);
lean_dec(v_fallback_506_);
lean_dec(v_t_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD(lean_object* v_00_u03b1_508_, lean_object* v_cmp_509_, lean_object* v_t_510_, lean_object* v_fallback_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_510_, v_fallback_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___boxed(lean_object* v_00_u03b1_513_, lean_object* v_cmp_514_, lean_object* v_t_515_, lean_object* v_fallback_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_TreeSet_Raw_maxD(v_00_u03b1_513_, v_cmp_514_, v_t_515_, v_fallback_516_);
lean_dec(v_fallback_516_);
lean_dec(v_t_515_);
lean_dec_ref(v_cmp_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg(lean_object* v_t_518_, lean_object* v_n_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_518_, v_n_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg___boxed(lean_object* v_t_521_, lean_object* v_n_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_TreeSet_Raw_atIdx_x3f___redArg(v_t_521_, v_n_522_);
lean_dec(v_t_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f(lean_object* v_00_u03b1_524_, lean_object* v_cmp_525_, lean_object* v_t_526_, lean_object* v_n_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_526_, v_n_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___boxed(lean_object* v_00_u03b1_529_, lean_object* v_cmp_530_, lean_object* v_t_531_, lean_object* v_n_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_TreeSet_Raw_atIdx_x3f(v_00_u03b1_529_, v_cmp_530_, v_t_531_, v_n_532_);
lean_dec(v_t_531_);
lean_dec_ref(v_cmp_530_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg(lean_object* v_inst_534_, lean_object* v_t_535_, lean_object* v_n_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_534_, v_t_535_, v_n_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg___boxed(lean_object* v_inst_538_, lean_object* v_t_539_, lean_object* v_n_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_TreeSet_Raw_atIdx_x21___redArg(v_inst_538_, v_t_539_, v_n_540_);
lean_dec(v_t_539_);
lean_dec(v_inst_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21(lean_object* v_00_u03b1_542_, lean_object* v_cmp_543_, lean_object* v_inst_544_, lean_object* v_t_545_, lean_object* v_n_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_544_, v_t_545_, v_n_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___boxed(lean_object* v_00_u03b1_548_, lean_object* v_cmp_549_, lean_object* v_inst_550_, lean_object* v_t_551_, lean_object* v_n_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_TreeSet_Raw_atIdx_x21(v_00_u03b1_548_, v_cmp_549_, v_inst_550_, v_t_551_, v_n_552_);
lean_dec(v_t_551_);
lean_dec(v_inst_550_);
lean_dec_ref(v_cmp_549_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg(lean_object* v_t_554_, lean_object* v_n_555_, lean_object* v_fallback_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_554_, v_n_555_, v_fallback_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg___boxed(lean_object* v_t_558_, lean_object* v_n_559_, lean_object* v_fallback_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_TreeSet_Raw_atIdxD___redArg(v_t_558_, v_n_559_, v_fallback_560_);
lean_dec(v_fallback_560_);
lean_dec(v_t_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD(lean_object* v_00_u03b1_562_, lean_object* v_cmp_563_, lean_object* v_t_564_, lean_object* v_n_565_, lean_object* v_fallback_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_564_, v_n_565_, v_fallback_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___boxed(lean_object* v_00_u03b1_568_, lean_object* v_cmp_569_, lean_object* v_t_570_, lean_object* v_n_571_, lean_object* v_fallback_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_TreeSet_Raw_atIdxD(v_00_u03b1_568_, v_cmp_569_, v_t_570_, v_n_571_, v_fallback_572_);
lean_dec(v_fallback_572_);
lean_dec(v_t_570_);
lean_dec_ref(v_cmp_569_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f___redArg(lean_object* v_cmp_574_, lean_object* v_t_575_, lean_object* v_k_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_box(0);
v___x_578_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_574_, v_k_576_, v___x_577_, v_t_575_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f(lean_object* v_00_u03b1_579_, lean_object* v_cmp_580_, lean_object* v_t_581_, lean_object* v_k_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_box(0);
v___x_584_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_580_, v_k_582_, v___x_583_, v_t_581_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f___redArg(lean_object* v_cmp_585_, lean_object* v_t_586_, lean_object* v_k_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_box(0);
v___x_589_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_585_, v_k_587_, v___x_588_, v_t_586_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f(lean_object* v_00_u03b1_590_, lean_object* v_cmp_591_, lean_object* v_t_592_, lean_object* v_k_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_box(0);
v___x_595_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_591_, v_k_593_, v___x_594_, v_t_592_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f___redArg(lean_object* v_cmp_596_, lean_object* v_t_597_, lean_object* v_k_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_box(0);
v___x_600_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_596_, v_k_598_, v___x_599_, v_t_597_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f(lean_object* v_00_u03b1_601_, lean_object* v_cmp_602_, lean_object* v_t_603_, lean_object* v_k_604_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_box(0);
v___x_606_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_602_, v_k_604_, v___x_605_, v_t_603_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f___redArg(lean_object* v_cmp_607_, lean_object* v_t_608_, lean_object* v_k_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_box(0);
v___x_611_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_607_, v_k_609_, v___x_610_, v_t_608_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f(lean_object* v_00_u03b1_612_, lean_object* v_cmp_613_, lean_object* v_t_614_, lean_object* v_k_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_box(0);
v___x_617_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_613_, v_k_615_, v___x_616_, v_t_614_);
return v___x_617_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_621_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2));
v___x_622_ = lean_unsigned_to_nat(14u);
v___x_623_ = lean_unsigned_to_nat(22u);
v___x_624_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1));
v___x_625_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0));
v___x_626_ = l_mkPanicMessageWithDecl(v___x_625_, v___x_624_, v___x_623_, v___x_622_, v___x_621_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg(lean_object* v_cmp_627_, lean_object* v_inst_628_, lean_object* v_t_629_, lean_object* v_k_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_box(0);
v___x_632_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_627_, v_k_630_, v___x_631_, v_t_629_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_634_ = l_panic___redArg(v_inst_628_, v___x_633_);
return v___x_634_;
}
else
{
lean_object* v_val_635_; 
v_val_635_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_val_635_);
lean_dec_ref(v___x_632_);
return v_val_635_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg___boxed(lean_object* v_cmp_636_, lean_object* v_inst_637_, lean_object* v_t_638_, lean_object* v_k_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_TreeSet_Raw_getGE_x21___redArg(v_cmp_636_, v_inst_637_, v_t_638_, v_k_639_);
lean_dec(v_inst_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21(lean_object* v_00_u03b1_641_, lean_object* v_cmp_642_, lean_object* v_inst_643_, lean_object* v_t_644_, lean_object* v_k_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_box(0);
v___x_647_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_642_, v_k_645_, v___x_646_, v_t_644_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_649_ = l_panic___redArg(v_inst_643_, v___x_648_);
return v___x_649_;
}
else
{
lean_object* v_val_650_; 
v_val_650_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_val_650_);
lean_dec_ref(v___x_647_);
return v_val_650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___boxed(lean_object* v_00_u03b1_651_, lean_object* v_cmp_652_, lean_object* v_inst_653_, lean_object* v_t_654_, lean_object* v_k_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Std_TreeSet_Raw_getGE_x21(v_00_u03b1_651_, v_cmp_652_, v_inst_653_, v_t_654_, v_k_655_);
lean_dec(v_inst_653_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg(lean_object* v_cmp_657_, lean_object* v_inst_658_, lean_object* v_t_659_, lean_object* v_k_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_box(0);
v___x_662_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_657_, v_k_660_, v___x_661_, v_t_659_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_664_ = l_panic___redArg(v_inst_658_, v___x_663_);
return v___x_664_;
}
else
{
lean_object* v_val_665_; 
v_val_665_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_val_665_);
lean_dec_ref(v___x_662_);
return v_val_665_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg___boxed(lean_object* v_cmp_666_, lean_object* v_inst_667_, lean_object* v_t_668_, lean_object* v_k_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_TreeSet_Raw_getGT_x21___redArg(v_cmp_666_, v_inst_667_, v_t_668_, v_k_669_);
lean_dec(v_inst_667_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21(lean_object* v_00_u03b1_671_, lean_object* v_cmp_672_, lean_object* v_inst_673_, lean_object* v_t_674_, lean_object* v_k_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_box(0);
v___x_677_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_672_, v_k_675_, v___x_676_, v_t_674_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_679_ = l_panic___redArg(v_inst_673_, v___x_678_);
return v___x_679_;
}
else
{
lean_object* v_val_680_; 
v_val_680_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_val_680_);
lean_dec_ref(v___x_677_);
return v_val_680_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___boxed(lean_object* v_00_u03b1_681_, lean_object* v_cmp_682_, lean_object* v_inst_683_, lean_object* v_t_684_, lean_object* v_k_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Std_TreeSet_Raw_getGT_x21(v_00_u03b1_681_, v_cmp_682_, v_inst_683_, v_t_684_, v_k_685_);
lean_dec(v_inst_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg(lean_object* v_cmp_687_, lean_object* v_inst_688_, lean_object* v_t_689_, lean_object* v_k_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_box(0);
v___x_692_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_687_, v_k_690_, v___x_691_, v_t_689_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_694_ = l_panic___redArg(v_inst_688_, v___x_693_);
return v___x_694_;
}
else
{
lean_object* v_val_695_; 
v_val_695_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_val_695_);
lean_dec_ref(v___x_692_);
return v_val_695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg___boxed(lean_object* v_cmp_696_, lean_object* v_inst_697_, lean_object* v_t_698_, lean_object* v_k_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Std_TreeSet_Raw_getLE_x21___redArg(v_cmp_696_, v_inst_697_, v_t_698_, v_k_699_);
lean_dec(v_inst_697_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21(lean_object* v_00_u03b1_701_, lean_object* v_cmp_702_, lean_object* v_inst_703_, lean_object* v_t_704_, lean_object* v_k_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_box(0);
v___x_707_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_702_, v_k_705_, v___x_706_, v_t_704_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_709_ = l_panic___redArg(v_inst_703_, v___x_708_);
return v___x_709_;
}
else
{
lean_object* v_val_710_; 
v_val_710_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_val_710_);
lean_dec_ref(v___x_707_);
return v_val_710_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___boxed(lean_object* v_00_u03b1_711_, lean_object* v_cmp_712_, lean_object* v_inst_713_, lean_object* v_t_714_, lean_object* v_k_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_TreeSet_Raw_getLE_x21(v_00_u03b1_711_, v_cmp_712_, v_inst_713_, v_t_714_, v_k_715_);
lean_dec(v_inst_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg(lean_object* v_cmp_717_, lean_object* v_inst_718_, lean_object* v_t_719_, lean_object* v_k_720_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_box(0);
v___x_722_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_717_, v_k_720_, v___x_721_, v_t_719_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_724_ = l_panic___redArg(v_inst_718_, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v_val_725_; 
v_val_725_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_val_725_);
lean_dec_ref(v___x_722_);
return v_val_725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg___boxed(lean_object* v_cmp_726_, lean_object* v_inst_727_, lean_object* v_t_728_, lean_object* v_k_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_TreeSet_Raw_getLT_x21___redArg(v_cmp_726_, v_inst_727_, v_t_728_, v_k_729_);
lean_dec(v_inst_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21(lean_object* v_00_u03b1_731_, lean_object* v_cmp_732_, lean_object* v_inst_733_, lean_object* v_t_734_, lean_object* v_k_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_box(0);
v___x_737_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_732_, v_k_735_, v___x_736_, v_t_734_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_739_ = l_panic___redArg(v_inst_733_, v___x_738_);
return v___x_739_;
}
else
{
lean_object* v_val_740_; 
v_val_740_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_val_740_);
lean_dec_ref(v___x_737_);
return v_val_740_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___boxed(lean_object* v_00_u03b1_741_, lean_object* v_cmp_742_, lean_object* v_inst_743_, lean_object* v_t_744_, lean_object* v_k_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Std_TreeSet_Raw_getLT_x21(v_00_u03b1_741_, v_cmp_742_, v_inst_743_, v_t_744_, v_k_745_);
lean_dec(v_inst_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg(lean_object* v_cmp_747_, lean_object* v_t_748_, lean_object* v_k_749_, lean_object* v_fallback_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_box(0);
v___x_752_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_747_, v_k_749_, v___x_751_, v_t_748_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_inc(v_fallback_750_);
return v_fallback_750_;
}
else
{
lean_object* v_val_753_; 
v_val_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_val_753_);
lean_dec_ref(v___x_752_);
return v_val_753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg___boxed(lean_object* v_cmp_754_, lean_object* v_t_755_, lean_object* v_k_756_, lean_object* v_fallback_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_TreeSet_Raw_getGED___redArg(v_cmp_754_, v_t_755_, v_k_756_, v_fallback_757_);
lean_dec(v_fallback_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED(lean_object* v_00_u03b1_759_, lean_object* v_cmp_760_, lean_object* v_t_761_, lean_object* v_k_762_, lean_object* v_fallback_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_box(0);
v___x_765_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_760_, v_k_762_, v___x_764_, v_t_761_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_inc(v_fallback_763_);
return v_fallback_763_;
}
else
{
lean_object* v_val_766_; 
v_val_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_val_766_);
lean_dec_ref(v___x_765_);
return v_val_766_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___boxed(lean_object* v_00_u03b1_767_, lean_object* v_cmp_768_, lean_object* v_t_769_, lean_object* v_k_770_, lean_object* v_fallback_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_TreeSet_Raw_getGED(v_00_u03b1_767_, v_cmp_768_, v_t_769_, v_k_770_, v_fallback_771_);
lean_dec(v_fallback_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg(lean_object* v_cmp_773_, lean_object* v_t_774_, lean_object* v_k_775_, lean_object* v_fallback_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_box(0);
v___x_778_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_773_, v_k_775_, v___x_777_, v_t_774_);
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
lean_dec_ref(v___x_778_);
return v_val_779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg___boxed(lean_object* v_cmp_780_, lean_object* v_t_781_, lean_object* v_k_782_, lean_object* v_fallback_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_TreeSet_Raw_getGTD___redArg(v_cmp_780_, v_t_781_, v_k_782_, v_fallback_783_);
lean_dec(v_fallback_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD(lean_object* v_00_u03b1_785_, lean_object* v_cmp_786_, lean_object* v_t_787_, lean_object* v_k_788_, lean_object* v_fallback_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_box(0);
v___x_791_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_786_, v_k_788_, v___x_790_, v_t_787_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_inc(v_fallback_789_);
return v_fallback_789_;
}
else
{
lean_object* v_val_792_; 
v_val_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_val_792_);
lean_dec_ref(v___x_791_);
return v_val_792_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___boxed(lean_object* v_00_u03b1_793_, lean_object* v_cmp_794_, lean_object* v_t_795_, lean_object* v_k_796_, lean_object* v_fallback_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_TreeSet_Raw_getGTD(v_00_u03b1_793_, v_cmp_794_, v_t_795_, v_k_796_, v_fallback_797_);
lean_dec(v_fallback_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg(lean_object* v_cmp_799_, lean_object* v_t_800_, lean_object* v_k_801_, lean_object* v_fallback_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_box(0);
v___x_804_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_799_, v_k_801_, v___x_803_, v_t_800_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_inc(v_fallback_802_);
return v_fallback_802_;
}
else
{
lean_object* v_val_805_; 
v_val_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_val_805_);
lean_dec_ref(v___x_804_);
return v_val_805_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg___boxed(lean_object* v_cmp_806_, lean_object* v_t_807_, lean_object* v_k_808_, lean_object* v_fallback_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_TreeSet_Raw_getLED___redArg(v_cmp_806_, v_t_807_, v_k_808_, v_fallback_809_);
lean_dec(v_fallback_809_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED(lean_object* v_00_u03b1_811_, lean_object* v_cmp_812_, lean_object* v_t_813_, lean_object* v_k_814_, lean_object* v_fallback_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_box(0);
v___x_817_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_812_, v_k_814_, v___x_816_, v_t_813_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_inc(v_fallback_815_);
return v_fallback_815_;
}
else
{
lean_object* v_val_818_; 
v_val_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_val_818_);
lean_dec_ref(v___x_817_);
return v_val_818_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___boxed(lean_object* v_00_u03b1_819_, lean_object* v_cmp_820_, lean_object* v_t_821_, lean_object* v_k_822_, lean_object* v_fallback_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_TreeSet_Raw_getLED(v_00_u03b1_819_, v_cmp_820_, v_t_821_, v_k_822_, v_fallback_823_);
lean_dec(v_fallback_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg(lean_object* v_cmp_825_, lean_object* v_t_826_, lean_object* v_k_827_, lean_object* v_fallback_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_box(0);
v___x_830_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_825_, v_k_827_, v___x_829_, v_t_826_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_inc(v_fallback_828_);
return v_fallback_828_;
}
else
{
lean_object* v_val_831_; 
v_val_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_831_);
lean_dec_ref(v___x_830_);
return v_val_831_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg___boxed(lean_object* v_cmp_832_, lean_object* v_t_833_, lean_object* v_k_834_, lean_object* v_fallback_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_TreeSet_Raw_getLTD___redArg(v_cmp_832_, v_t_833_, v_k_834_, v_fallback_835_);
lean_dec(v_fallback_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD(lean_object* v_00_u03b1_837_, lean_object* v_cmp_838_, lean_object* v_t_839_, lean_object* v_k_840_, lean_object* v_fallback_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_box(0);
v___x_843_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_838_, v_k_840_, v___x_842_, v_t_839_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_inc(v_fallback_841_);
return v_fallback_841_;
}
else
{
lean_object* v_val_844_; 
v_val_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_val_844_);
lean_dec_ref(v___x_843_);
return v_val_844_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___boxed(lean_object* v_00_u03b1_845_, lean_object* v_cmp_846_, lean_object* v_t_847_, lean_object* v_k_848_, lean_object* v_fallback_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_TreeSet_Raw_getLTD(v_00_u03b1_845_, v_cmp_846_, v_t_847_, v_k_848_, v_fallback_849_);
lean_dec(v_fallback_849_);
return v_res_850_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_filter___redArg___lam__0(lean_object* v_f_851_, lean_object* v_a_852_, lean_object* v_x_853_){
_start:
{
lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_854_ = lean_apply_1(v_f_851_, v_a_852_);
v___x_855_ = lean_unbox(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_856_, lean_object* v_a_857_, lean_object* v_x_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Std_TreeSet_Raw_filter___redArg___lam__0(v_f_856_, v_a_857_, v_x_858_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg(lean_object* v_f_861_, lean_object* v_t_862_){
_start:
{
lean_object* v___f_863_; lean_object* v___x_864_; 
v___f_863_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_863_, 0, v_f_861_);
v___x_864_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_863_, v_t_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter(lean_object* v_00_u03b1_865_, lean_object* v_cmp_866_, lean_object* v_f_867_, lean_object* v_t_868_){
_start:
{
lean_object* v___f_869_; lean_object* v___x_870_; 
v___f_869_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_869_, 0, v_f_867_);
v___x_870_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_869_, v_t_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___boxed(lean_object* v_00_u03b1_871_, lean_object* v_cmp_872_, lean_object* v_f_873_, lean_object* v_t_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_TreeSet_Raw_filter(v_00_u03b1_871_, v_cmp_872_, v_f_873_, v_t_874_);
lean_dec_ref(v_cmp_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg___lam__0(lean_object* v_f_876_, lean_object* v_c_877_, lean_object* v_a_878_, lean_object* v_x_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = lean_apply_2(v_f_876_, v_c_877_, v_a_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg(lean_object* v_inst_881_, lean_object* v_f_882_, lean_object* v_init_883_, lean_object* v_t_884_){
_start:
{
lean_object* v___f_885_; lean_object* v___x_886_; 
v___f_885_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_885_, 0, v_f_882_);
v___x_886_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_881_, v___f_885_, v_init_883_, v_t_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM(lean_object* v_00_u03b1_887_, lean_object* v_cmp_888_, lean_object* v_00_u03b4_889_, lean_object* v_m_890_, lean_object* v_inst_891_, lean_object* v_f_892_, lean_object* v_init_893_, lean_object* v_t_894_){
_start:
{
lean_object* v___f_895_; lean_object* v___x_896_; 
v___f_895_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_895_, 0, v_f_892_);
v___x_896_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_891_, v___f_895_, v_init_893_, v_t_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___boxed(lean_object* v_00_u03b1_897_, lean_object* v_cmp_898_, lean_object* v_00_u03b4_899_, lean_object* v_m_900_, lean_object* v_inst_901_, lean_object* v_f_902_, lean_object* v_init_903_, lean_object* v_t_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_TreeSet_Raw_foldlM(v_00_u03b1_897_, v_cmp_898_, v_00_u03b4_899_, v_m_900_, v_inst_901_, v_f_902_, v_init_903_, v_t_904_);
lean_dec_ref(v_cmp_898_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___redArg(lean_object* v_f_906_, lean_object* v_init_907_, lean_object* v_t_908_){
_start:
{
lean_object* v___f_909_; lean_object* v___x_910_; 
v___f_909_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_909_, 0, v_f_906_);
v___x_910_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_909_, v_init_907_, v_t_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl(lean_object* v_00_u03b1_911_, lean_object* v_cmp_912_, lean_object* v_00_u03b4_913_, lean_object* v_f_914_, lean_object* v_init_915_, lean_object* v_t_916_){
_start:
{
lean_object* v___f_917_; lean_object* v___x_918_; 
v___f_917_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_917_, 0, v_f_914_);
v___x_918_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_917_, v_init_915_, v_t_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___boxed(lean_object* v_00_u03b1_919_, lean_object* v_cmp_920_, lean_object* v_00_u03b4_921_, lean_object* v_f_922_, lean_object* v_init_923_, lean_object* v_t_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_TreeSet_Raw_foldl(v_00_u03b1_919_, v_cmp_920_, v_00_u03b4_921_, v_f_922_, v_init_923_, v_t_924_);
lean_dec_ref(v_cmp_920_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg___lam__0(lean_object* v_f_926_, lean_object* v_a_927_, lean_object* v_x_928_, lean_object* v_acc_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = lean_apply_2(v_f_926_, v_a_927_, v_acc_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg(lean_object* v_inst_931_, lean_object* v_f_932_, lean_object* v_init_933_, lean_object* v_t_934_){
_start:
{
lean_object* v___f_935_; lean_object* v___x_936_; 
v___f_935_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_935_, 0, v_f_932_);
v___x_936_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_931_, v___f_935_, v_init_933_, v_t_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM(lean_object* v_00_u03b1_937_, lean_object* v_cmp_938_, lean_object* v_00_u03b4_939_, lean_object* v_m_940_, lean_object* v_inst_941_, lean_object* v_f_942_, lean_object* v_init_943_, lean_object* v_t_944_){
_start:
{
lean_object* v___f_945_; lean_object* v___x_946_; 
v___f_945_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_945_, 0, v_f_942_);
v___x_946_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_941_, v___f_945_, v_init_943_, v_t_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___boxed(lean_object* v_00_u03b1_947_, lean_object* v_cmp_948_, lean_object* v_00_u03b4_949_, lean_object* v_m_950_, lean_object* v_inst_951_, lean_object* v_f_952_, lean_object* v_init_953_, lean_object* v_t_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Std_TreeSet_Raw_foldrM(v_00_u03b1_947_, v_cmp_948_, v_00_u03b4_949_, v_m_950_, v_inst_951_, v_f_952_, v_init_953_, v_t_954_);
lean_dec_ref(v_cmp_948_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg___lam__0(lean_object* v_f_956_, lean_object* v_x1_957_, lean_object* v_x2_958_, lean_object* v_x3_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = lean_apply_2(v_f_956_, v_x1_957_, v_x3_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg(lean_object* v_f_980_, lean_object* v_init_981_, lean_object* v_t_982_){
_start:
{
lean_object* v___f_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___f_983_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_983_, 0, v_f_980_);
v___x_984_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_985_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_984_, v___f_983_, v_init_981_, v_t_982_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr(lean_object* v_00_u03b1_986_, lean_object* v_cmp_987_, lean_object* v_00_u03b4_988_, lean_object* v_f_989_, lean_object* v_init_990_, lean_object* v_t_991_){
_start:
{
lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___f_992_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_992_, 0, v_f_989_);
v___x_993_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_994_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_993_, v___f_992_, v_init_990_, v_t_991_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___boxed(lean_object* v_00_u03b1_995_, lean_object* v_cmp_996_, lean_object* v_00_u03b4_997_, lean_object* v_f_998_, lean_object* v_init_999_, lean_object* v_t_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_TreeSet_Raw_foldr(v_00_u03b1_995_, v_cmp_996_, v_00_u03b4_997_, v_f_998_, v_init_999_, v_t_1000_);
lean_dec_ref(v_cmp_996_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg___lam__0(lean_object* v_f_1002_, lean_object* v_cmp_1003_, lean_object* v_x_1004_, lean_object* v_a_1005_, lean_object* v_b_1006_){
_start:
{
lean_object* v_fst_1007_; lean_object* v_snd_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1022_; 
v_fst_1007_ = lean_ctor_get(v_x_1004_, 0);
v_snd_1008_ = lean_ctor_get(v_x_1004_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_x_1004_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1010_ = v_x_1004_;
v_isShared_1011_ = v_isSharedCheck_1022_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_snd_1008_);
lean_inc(v_fst_1007_);
lean_dec(v_x_1004_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1022_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; 
lean_inc(v_a_1005_);
v___x_1012_ = lean_apply_1(v_f_1002_, v_a_1005_);
v___x_1013_ = lean_unbox(v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1014_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1003_, v_a_1005_, v_b_1006_, v_snd_1008_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 1, v___x_1014_);
v___x_1016_ = v___x_1010_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_fst_1007_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1003_, v_a_1005_, v_b_1006_, v_fst_1007_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1018_);
v___x_1020_ = v___x_1010_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_snd_1008_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg(lean_object* v_cmp_1025_, lean_object* v_f_1026_, lean_object* v_t_1027_){
_start:
{
lean_object* v___f_1028_; lean_object* v___x_1029_; lean_object* v_p_1030_; lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v___f_1028_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1028_, 0, v_f_1026_);
lean_closure_set(v___f_1028_, 1, v_cmp_1025_);
v___x_1029_ = ((lean_object*)(l_Std_TreeSet_Raw_partition___redArg___closed__0));
v_p_1030_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1028_, v___x_1029_, v_t_1027_);
v_fst_1031_ = lean_ctor_get(v_p_1030_, 0);
v_snd_1032_ = lean_ctor_get(v_p_1030_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_p_1030_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v_p_1030_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_snd_1032_);
lean_inc(v_fst_1031_);
lean_dec(v_p_1030_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_fst_1031_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_snd_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition(lean_object* v_00_u03b1_1040_, lean_object* v_cmp_1041_, lean_object* v_f_1042_, lean_object* v_t_1043_){
_start:
{
lean_object* v___f_1044_; lean_object* v___x_1045_; lean_object* v_p_1046_; lean_object* v_fst_1047_; lean_object* v_snd_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
v___f_1044_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1044_, 0, v_f_1042_);
lean_closure_set(v___f_1044_, 1, v_cmp_1041_);
v___x_1045_ = ((lean_object*)(l_Std_TreeSet_Raw_partition___redArg___closed__0));
v_p_1046_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1044_, v___x_1045_, v_t_1043_);
v_fst_1047_ = lean_ctor_get(v_p_1046_, 0);
v_snd_1048_ = lean_ctor_get(v_p_1046_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_p_1046_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v_p_1046_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_snd_1048_);
lean_inc(v_fst_1047_);
lean_dec(v_p_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_fst_1047_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_snd_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg___lam__0(lean_object* v_f_1056_, lean_object* v_x_1057_, lean_object* v_k_1058_, lean_object* v_v_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_apply_1(v_f_1056_, v_k_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg(lean_object* v_inst_1061_, lean_object* v_f_1062_, lean_object* v_t_1063_){
_start:
{
lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___f_1064_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1064_, 0, v_f_1062_);
v___x_1065_ = lean_box(0);
v___x_1066_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1061_, v___f_1064_, v___x_1065_, v_t_1063_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM(lean_object* v_00_u03b1_1067_, lean_object* v_cmp_1068_, lean_object* v_m_1069_, lean_object* v_inst_1070_, lean_object* v_f_1071_, lean_object* v_t_1072_){
_start:
{
lean_object* v___f_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___f_1073_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1073_, 0, v_f_1071_);
v___x_1074_ = lean_box(0);
v___x_1075_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1070_, v___f_1073_, v___x_1074_, v_t_1072_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___boxed(lean_object* v_00_u03b1_1076_, lean_object* v_cmp_1077_, lean_object* v_m_1078_, lean_object* v_inst_1079_, lean_object* v_f_1080_, lean_object* v_t_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Std_TreeSet_Raw_forM(v_00_u03b1_1076_, v_cmp_1077_, v_m_1078_, v_inst_1079_, v_f_1080_, v_t_1081_);
lean_dec_ref(v_cmp_1077_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__0(lean_object* v_f_1083_, lean_object* v_a_1084_, lean_object* v_b_1085_, lean_object* v_c_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_apply_2(v_f_1083_, v_a_1084_, v_c_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__1(lean_object* v_toPure_1088_, lean_object* v_____do__lift_1089_){
_start:
{
lean_object* v_a_1090_; lean_object* v___x_1091_; 
v_a_1090_ = lean_ctor_get(v_____do__lift_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref(v_____do__lift_1089_);
v___x_1091_ = lean_apply_2(v_toPure_1088_, lean_box(0), v_a_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg(lean_object* v_inst_1092_, lean_object* v_f_1093_, lean_object* v_init_1094_, lean_object* v_t_1095_){
_start:
{
lean_object* v_toApplicative_1096_; lean_object* v_toBind_1097_; lean_object* v_toPure_1098_; lean_object* v___f_1099_; lean_object* v___x_1100_; lean_object* v___f_1101_; lean_object* v___x_1102_; 
v_toApplicative_1096_ = lean_ctor_get(v_inst_1092_, 0);
v_toBind_1097_ = lean_ctor_get(v_inst_1092_, 1);
lean_inc(v_toBind_1097_);
v_toPure_1098_ = lean_ctor_get(v_toApplicative_1096_, 1);
lean_inc(v_toPure_1098_);
v___f_1099_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1099_, 0, v_f_1093_);
v___x_1100_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1092_, v___f_1099_, v_init_1094_, v_t_1095_);
v___f_1101_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1101_, 0, v_toPure_1098_);
v___x_1102_ = lean_apply_4(v_toBind_1097_, lean_box(0), lean_box(0), v___x_1100_, v___f_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn(lean_object* v_00_u03b1_1103_, lean_object* v_cmp_1104_, lean_object* v_00_u03b4_1105_, lean_object* v_m_1106_, lean_object* v_inst_1107_, lean_object* v_f_1108_, lean_object* v_init_1109_, lean_object* v_t_1110_){
_start:
{
lean_object* v_toApplicative_1111_; lean_object* v_toBind_1112_; lean_object* v_toPure_1113_; lean_object* v___f_1114_; lean_object* v___x_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; 
v_toApplicative_1111_ = lean_ctor_get(v_inst_1107_, 0);
v_toBind_1112_ = lean_ctor_get(v_inst_1107_, 1);
lean_inc(v_toBind_1112_);
v_toPure_1113_ = lean_ctor_get(v_toApplicative_1111_, 1);
lean_inc(v_toPure_1113_);
v___f_1114_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1114_, 0, v_f_1108_);
v___x_1115_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1107_, v___f_1114_, v_init_1109_, v_t_1110_);
v___f_1116_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1116_, 0, v_toPure_1113_);
v___x_1117_ = lean_apply_4(v_toBind_1112_, lean_box(0), lean_box(0), v___x_1115_, v___f_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_cmp_1119_, lean_object* v_00_u03b4_1120_, lean_object* v_m_1121_, lean_object* v_inst_1122_, lean_object* v_f_1123_, lean_object* v_init_1124_, lean_object* v_t_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Std_TreeSet_Raw_forIn(v_00_u03b1_1118_, v_cmp_1119_, v_00_u03b4_1120_, v_m_1121_, v_inst_1122_, v_f_1123_, v_init_1124_, v_t_1125_);
lean_dec_ref(v_cmp_1119_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1(lean_object* v_inst_1127_, lean_object* v_t_1128_, lean_object* v_f_1129_){
_start:
{
lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___f_1130_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1130_, 0, v_f_1129_);
v___x_1131_ = lean_box(0);
v___x_1132_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1127_, v___f_1130_, v___x_1131_, v_t_1128_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_1133_){
_start:
{
lean_object* v___f_1134_; 
v___f_1134_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1134_, 0, v_inst_1133_);
return v___f_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_1135_, lean_object* v_cmp_1136_, lean_object* v_m_1137_, lean_object* v_inst_1138_){
_start:
{
lean_object* v___f_1139_; 
v___f_1139_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1139_, 0, v_inst_1138_);
return v___f_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___boxed(lean_object* v_00_u03b1_1140_, lean_object* v_cmp_1141_, lean_object* v_m_1142_, lean_object* v_inst_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_TreeSet_Raw_instForMOfMonad(v_00_u03b1_1140_, v_cmp_1141_, v_m_1142_, v_inst_1143_);
lean_dec_ref(v_cmp_1141_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2(lean_object* v_inst_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_t_1147_, lean_object* v_init_1148_, lean_object* v_f_1149_){
_start:
{
lean_object* v_toApplicative_1150_; lean_object* v_toBind_1151_; lean_object* v_toPure_1152_; lean_object* v___f_1153_; lean_object* v___x_1154_; lean_object* v___f_1155_; lean_object* v___x_1156_; 
v_toApplicative_1150_ = lean_ctor_get(v_inst_1145_, 0);
v_toBind_1151_ = lean_ctor_get(v_inst_1145_, 1);
lean_inc(v_toBind_1151_);
v_toPure_1152_ = lean_ctor_get(v_toApplicative_1150_, 1);
lean_inc(v_toPure_1152_);
v___f_1153_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1153_, 0, v_f_1149_);
v___x_1154_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1145_, v___f_1153_, v_init_1148_, v_t_1147_);
v___f_1155_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1155_, 0, v_toPure_1152_);
v___x_1156_ = lean_apply_4(v_toBind_1151_, lean_box(0), lean_box(0), v___x_1154_, v___f_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_1157_){
_start:
{
lean_object* v___f_1158_; 
v___f_1158_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1158_, 0, v_inst_1157_);
return v___f_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_1159_, lean_object* v_cmp_1160_, lean_object* v_m_1161_, lean_object* v_inst_1162_){
_start:
{
lean_object* v___f_1163_; 
v___f_1163_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1163_, 0, v_inst_1162_);
return v___f_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___boxed(lean_object* v_00_u03b1_1164_, lean_object* v_cmp_1165_, lean_object* v_m_1166_, lean_object* v_inst_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_TreeSet_Raw_instForInOfMonad(v_00_u03b1_1164_, v_cmp_1165_, v_m_1166_, v_inst_1167_);
lean_dec_ref(v_cmp_1165_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0(lean_object* v_p_1169_, lean_object* v___x_1170_, lean_object* v___x_1171_, lean_object* v_a_1172_, lean_object* v_b_1173_, lean_object* v_acc_1174_){
_start:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_apply_1(v_p_1169_, v_a_1172_);
v___x_1176_ = lean_unbox(v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1170_);
return v___x_1177_;
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v___x_1170_);
v___x_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1175_);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v___x_1171_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1181_, lean_object* v___x_1182_, lean_object* v___x_1183_, lean_object* v_a_1184_, lean_object* v_b_1185_, lean_object* v_acc_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Std_TreeSet_Raw_any___redArg___lam__0(v_p_1181_, v___x_1182_, v___x_1183_, v_a_1184_, v_b_1185_, v_acc_1186_);
lean_dec_ref(v_acc_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_any___redArg(lean_object* v_t_1191_, lean_object* v_p_1192_){
_start:
{
lean_object* v___y_1194_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v_a_1204_; 
v___x_1199_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1200_ = lean_box(0);
v___x_1201_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1202_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1202_, 0, v_p_1192_);
lean_closure_set(v___f_1202_, 1, v___x_1201_);
lean_closure_set(v___f_1202_, 2, v___x_1200_);
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
v___x_1196_ = 0;
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___boxed(lean_object* v_t_1205_, lean_object* v_p_1206_){
_start:
{
uint8_t v_res_1207_; lean_object* v_r_1208_; 
v_res_1207_ = l_Std_TreeSet_Raw_any___redArg(v_t_1205_, v_p_1206_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_any(lean_object* v_00_u03b1_1209_, lean_object* v_cmp_1210_, lean_object* v_t_1211_, lean_object* v_p_1212_){
_start:
{
lean_object* v___y_1214_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v_a_1224_; 
v___x_1219_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1220_ = lean_box(0);
v___x_1221_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1222_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1222_, 0, v_p_1212_);
lean_closure_set(v___f_1222_, 1, v___x_1221_);
lean_closure_set(v___f_1222_, 2, v___x_1220_);
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
v___x_1216_ = 0;
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___boxed(lean_object* v_00_u03b1_1225_, lean_object* v_cmp_1226_, lean_object* v_t_1227_, lean_object* v_p_1228_){
_start:
{
uint8_t v_res_1229_; lean_object* v_r_1230_; 
v_res_1229_ = l_Std_TreeSet_Raw_any(v_00_u03b1_1225_, v_cmp_1226_, v_t_1227_, v_p_1228_);
lean_dec_ref(v_cmp_1226_);
v_r_1230_ = lean_box(v_res_1229_);
return v_r_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0(lean_object* v_p_1231_, lean_object* v___x_1232_, lean_object* v___x_1233_, lean_object* v_a_1234_, lean_object* v_b_1235_, lean_object* v_acc_1236_){
_start:
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = lean_apply_1(v_p_1231_, v_a_1234_);
v___x_1238_ = lean_unbox(v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec_ref(v___x_1233_);
v___x_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___x_1232_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1233_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1243_, lean_object* v___x_1244_, lean_object* v___x_1245_, lean_object* v_a_1246_, lean_object* v_b_1247_, lean_object* v_acc_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_TreeSet_Raw_all___redArg___lam__0(v_p_1243_, v___x_1244_, v___x_1245_, v_a_1246_, v_b_1247_, v_acc_1248_);
lean_dec_ref(v_acc_1248_);
return v_res_1249_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_all___redArg(lean_object* v_t_1250_, lean_object* v_p_1251_){
_start:
{
lean_object* v___y_1253_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v_a_1263_; 
v___x_1258_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1259_ = lean_box(0);
v___x_1260_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1261_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1261_, 0, v_p_1251_);
lean_closure_set(v___f_1261_, 1, v___x_1259_);
lean_closure_set(v___f_1261_, 2, v___x_1260_);
v___x_1262_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1258_, v___f_1261_, v___x_1260_, v_t_1250_);
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___y_1253_ = v_a_1263_;
goto v___jp_1252_;
v___jp_1252_:
{
lean_object* v_fst_1254_; 
v_fst_1254_ = lean_ctor_get(v___y_1253_, 0);
lean_inc(v_fst_1254_);
lean_dec_ref(v___y_1253_);
if (lean_obj_tag(v_fst_1254_) == 0)
{
uint8_t v___x_1255_; 
v___x_1255_ = 1;
return v___x_1255_;
}
else
{
lean_object* v_val_1256_; uint8_t v___x_1257_; 
v_val_1256_ = lean_ctor_get(v_fst_1254_, 0);
lean_inc(v_val_1256_);
lean_dec_ref(v_fst_1254_);
v___x_1257_ = lean_unbox(v_val_1256_);
lean_dec(v_val_1256_);
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___boxed(lean_object* v_t_1264_, lean_object* v_p_1265_){
_start:
{
uint8_t v_res_1266_; lean_object* v_r_1267_; 
v_res_1266_ = l_Std_TreeSet_Raw_all___redArg(v_t_1264_, v_p_1265_);
v_r_1267_ = lean_box(v_res_1266_);
return v_r_1267_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_all(lean_object* v_00_u03b1_1268_, lean_object* v_cmp_1269_, lean_object* v_t_1270_, lean_object* v_p_1271_){
_start:
{
lean_object* v___y_1273_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___f_1281_; lean_object* v___x_1282_; lean_object* v_a_1283_; 
v___x_1278_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1279_ = lean_box(0);
v___x_1280_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1281_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1281_, 0, v_p_1271_);
lean_closure_set(v___f_1281_, 1, v___x_1279_);
lean_closure_set(v___f_1281_, 2, v___x_1280_);
v___x_1282_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1278_, v___f_1281_, v___x_1280_, v_t_1270_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___y_1273_ = v_a_1283_;
goto v___jp_1272_;
v___jp_1272_:
{
lean_object* v_fst_1274_; 
v_fst_1274_ = lean_ctor_get(v___y_1273_, 0);
lean_inc(v_fst_1274_);
lean_dec_ref(v___y_1273_);
if (lean_obj_tag(v_fst_1274_) == 0)
{
uint8_t v___x_1275_; 
v___x_1275_ = 1;
return v___x_1275_;
}
else
{
lean_object* v_val_1276_; uint8_t v___x_1277_; 
v_val_1276_ = lean_ctor_get(v_fst_1274_, 0);
lean_inc(v_val_1276_);
lean_dec_ref(v_fst_1274_);
v___x_1277_ = lean_unbox(v_val_1276_);
lean_dec(v_val_1276_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_cmp_1285_, lean_object* v_t_1286_, lean_object* v_p_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Std_TreeSet_Raw_all(v_00_u03b1_1284_, v_cmp_1285_, v_t_1286_, v_p_1287_);
lean_dec_ref(v_cmp_1285_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg___lam__0(lean_object* v_x1_1290_, lean_object* v_x2_1291_, lean_object* v_x3_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1293_, 0, v_x1_1290_);
lean_ctor_set(v___x_1293_, 1, v_x3_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg(lean_object* v_t_1295_){
_start:
{
lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___f_1296_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___x_1297_ = lean_box(0);
v___x_1298_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1299_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1298_, v___f_1296_, v___x_1297_, v_t_1295_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList(lean_object* v_00_u03b1_1300_, lean_object* v_cmp_1301_, lean_object* v_t_1302_){
_start:
{
lean_object* v___f_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___f_1303_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___x_1304_ = lean_box(0);
v___x_1305_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1306_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1305_, v___f_1303_, v___x_1304_, v_t_1302_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_cmp_1308_, lean_object* v_t_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Std_TreeSet_Raw_toList(v_00_u03b1_1307_, v_cmp_1308_, v_t_1309_);
lean_dec_ref(v_cmp_1308_);
return v_res_1310_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__26, &l_Std_TreeSet_Raw___auto__1___closed__26_once, _init_l_Std_TreeSet_Raw___auto__1___closed__26);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg___lam__0(lean_object* v_cmp_1312_, lean_object* v_a_1313_, lean_object* v_x_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v___x_1316_; 
lean_inc(v___y_1315_);
lean_inc(v_a_1313_);
lean_inc_ref(v_cmp_1312_);
v___x_1316_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1312_, v_a_1313_, v___y_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_box(0);
v___x_1318_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1312_, v_a_1313_, v___x_1317_, v___y_1315_);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; 
lean_dec(v_a_1313_);
lean_dec_ref(v_cmp_1312_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___y_1315_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg(lean_object* v_l_1321_, lean_object* v_cmp_1322_){
_start:
{
lean_object* v___f_1323_; lean_object* v___x_1324_; lean_object* v_r_1325_; lean_object* v___x_1326_; 
v___f_1323_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1323_, 0, v_cmp_1322_);
v___x_1324_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1325_ = lean_box(1);
v___x_1326_ = l_List_forIn_x27_loop___redArg(v___x_1324_, v___f_1323_, v_l_1321_, v_r_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList(lean_object* v_00_u03b1_1327_, lean_object* v_l_1328_, lean_object* v_cmp_1329_){
_start:
{
lean_object* v___f_1330_; lean_object* v___x_1331_; lean_object* v_r_1332_; lean_object* v___x_1333_; 
v___f_1330_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1330_, 0, v_cmp_1329_);
v___x_1331_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1332_ = lean_box(1);
v___x_1333_ = l_List_forIn_x27_loop___redArg(v___x_1331_, v___f_1330_, v_l_1328_, v_r_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg___lam__0(lean_object* v_c_1334_, lean_object* v_a_1335_, lean_object* v_x_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_array_push(v_c_1334_, v_a_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg(lean_object* v_t_1341_){
_start:
{
lean_object* v___f_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___f_1342_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__0));
v___x_1343_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__1));
v___x_1344_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1342_, v___x_1343_, v_t_1341_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray(lean_object* v_00_u03b1_1345_, lean_object* v_cmp_1346_, lean_object* v_t_1347_){
_start:
{
lean_object* v___f_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___f_1348_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__0));
v___x_1349_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__1));
v___x_1350_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1348_, v___x_1349_, v_t_1347_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___boxed(lean_object* v_00_u03b1_1351_, lean_object* v_cmp_1352_, lean_object* v_t_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Std_TreeSet_Raw_toArray(v_00_u03b1_1351_, v_cmp_1352_, v_t_1353_);
lean_dec_ref(v_cmp_1352_);
return v_res_1354_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__26, &l_Std_TreeSet_Raw___auto__1___closed__26_once, _init_l_Std_TreeSet_Raw___auto__1___closed__26);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray___redArg(lean_object* v_a_1356_, lean_object* v_cmp_1357_){
_start:
{
lean_object* v___f_1358_; lean_object* v___x_1359_; lean_object* v_r_1360_; size_t v_sz_1361_; size_t v___x_1362_; lean_object* v___x_1363_; 
v___f_1358_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1358_, 0, v_cmp_1357_);
v___x_1359_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1360_ = lean_box(1);
v_sz_1361_ = lean_array_size(v_a_1356_);
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1359_, v_a_1356_, v___f_1358_, v_sz_1361_, v___x_1362_, v_r_1360_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray(lean_object* v_00_u03b1_1364_, lean_object* v_a_1365_, lean_object* v_cmp_1366_){
_start:
{
lean_object* v___f_1367_; lean_object* v___x_1368_; lean_object* v_r_1369_; size_t v_sz_1370_; size_t v___x_1371_; lean_object* v___x_1372_; 
v___f_1367_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1367_, 0, v_cmp_1366_);
v___x_1368_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1369_ = lean_box(1);
v_sz_1370_ = lean_array_size(v_a_1365_);
v___x_1371_ = ((size_t)0ULL);
v___x_1372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1368_, v_a_1365_, v___f_1367_, v_sz_1370_, v___x_1371_, v_r_1369_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0(lean_object* v_b_u2082_1375_, lean_object* v_x_1376_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1377_, 0, v_b_u2082_1375_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; 
v___x_1378_ = ((lean_object*)(l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0));
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1379_, lean_object* v_x_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_TreeSet_Raw_merge___redArg___lam__0(v_b_u2082_1379_, v_x_1380_);
lean_dec(v_x_1380_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__1(lean_object* v_cmp_1382_, lean_object* v_t_1383_, lean_object* v_a_1384_, lean_object* v_b_u2082_1385_){
_start:
{
lean_object* v___f_1386_; lean_object* v___x_1387_; 
v___f_1386_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1386_, 0, v_b_u2082_1385_);
v___x_1387_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_1382_, v_a_1384_, v___f_1386_, v_t_1383_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg(lean_object* v_cmp_1388_, lean_object* v_t_u2081_1389_, lean_object* v_t_u2082_1390_){
_start:
{
lean_object* v___f_1391_; lean_object* v___x_1392_; 
v___f_1391_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1391_, 0, v_cmp_1388_);
v___x_1392_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1391_, v_t_u2081_1389_, v_t_u2082_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge(lean_object* v_00_u03b1_1393_, lean_object* v_cmp_1394_, lean_object* v_t_u2081_1395_, lean_object* v_t_u2082_1396_){
_start:
{
lean_object* v___f_1397_; lean_object* v___x_1398_; 
v___f_1397_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1397_, 0, v_cmp_1394_);
v___x_1398_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1397_, v_t_u2081_1395_, v_t_u2082_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_1399_, lean_object* v_a_1400_, lean_object* v_____s_1401_){
_start:
{
uint8_t v___x_1402_; 
lean_inc(v_____s_1401_);
lean_inc(v_a_1400_);
lean_inc_ref(v_cmp_1399_);
v___x_1402_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1399_, v_a_1400_, v_____s_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_box(0);
v___x_1404_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1399_, v_a_1400_, v___x_1403_, v_____s_1401_);
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; 
lean_dec(v_a_1400_);
lean_dec_ref(v_cmp_1399_);
v___x_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_____s_1401_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg(lean_object* v_cmp_1407_, lean_object* v_inst_1408_, lean_object* v_t_1409_, lean_object* v_l_1410_){
_start:
{
lean_object* v___f_1411_; lean_object* v___x_1412_; 
v___f_1411_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1411_, 0, v_cmp_1407_);
v___x_1412_ = lean_apply_4(v_inst_1408_, lean_box(0), v_l_1410_, v_t_1409_, v___f_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany(lean_object* v_00_u03b1_1413_, lean_object* v_cmp_1414_, lean_object* v_00_u03c1_1415_, lean_object* v_inst_1416_, lean_object* v_t_1417_, lean_object* v_l_1418_){
_start:
{
lean_object* v___f_1419_; lean_object* v___x_1420_; 
v___f_1419_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1419_, 0, v_cmp_1414_);
v___x_1420_ = lean_apply_4(v_inst_1416_, lean_box(0), v_l_1418_, v_t_1417_, v___f_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union___redArg(lean_object* v_cmp_1421_, lean_object* v_t_u2081_1422_, lean_object* v_t_u2082_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_1421_, v_t_u2081_1422_, v_t_u2082_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union(lean_object* v_00_u03b1_1425_, lean_object* v_cmp_1426_, lean_object* v_t_u2081_1427_, lean_object* v_t_u2082_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_1426_, v_t_u2081_1427_, v_t_u2082_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion___redArg(lean_object* v_cmp_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_union), 4, 2);
lean_closure_set(v___x_1431_, 0, lean_box(0));
lean_closure_set(v___x_1431_, 1, v_cmp_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion(lean_object* v_00_u03b1_1432_, lean_object* v_cmp_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_union), 4, 2);
lean_closure_set(v___x_1434_, 0, lean_box(0));
lean_closure_set(v___x_1434_, 1, v_cmp_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter___redArg(lean_object* v_cmp_1435_, lean_object* v_t_u2081_1436_, lean_object* v_t_u2082_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_1435_, v_t_u2081_1436_, v_t_u2082_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter(lean_object* v_00_u03b1_1439_, lean_object* v_cmp_1440_, lean_object* v_t_u2081_1441_, lean_object* v_t_u2082_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_1440_, v_t_u2081_1441_, v_t_u2082_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter___redArg(lean_object* v_cmp_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_inter), 4, 2);
lean_closure_set(v___x_1445_, 0, lean_box(0));
lean_closure_set(v___x_1445_, 1, v_cmp_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter(lean_object* v_00_u03b1_1446_, lean_object* v_cmp_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_inter), 4, 2);
lean_closure_set(v___x_1448_, 0, lean_box(0));
lean_closure_set(v___x_1448_, 1, v_cmp_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1449_, lean_object* v_x_1450_){
_start:
{
if (lean_obj_tag(v_x_1449_) == 0)
{
if (lean_obj_tag(v_x_1450_) == 0)
{
uint8_t v___x_1451_; 
v___x_1451_ = 1;
return v___x_1451_;
}
else
{
uint8_t v___x_1452_; 
v___x_1452_ = 0;
return v___x_1452_;
}
}
else
{
if (lean_obj_tag(v_x_1450_) == 0)
{
uint8_t v___x_1453_; 
v___x_1453_ = 0;
return v___x_1453_;
}
else
{
uint8_t v___x_1454_; 
v___x_1454_ = 1;
return v___x_1454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1455_, lean_object* v_x_1456_){
_start:
{
uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v_x_1455_, v_x_1456_);
lean_dec(v_x_1456_);
lean_dec(v_x_1455_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_cmp_1459_, lean_object* v_t_1460_, lean_object* v_k_1461_){
_start:
{
if (lean_obj_tag(v_t_1460_) == 0)
{
lean_object* v_k_1462_; lean_object* v_v_1463_; lean_object* v_l_1464_; lean_object* v_r_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v_k_1462_ = lean_ctor_get(v_t_1460_, 1);
lean_inc(v_k_1462_);
v_v_1463_ = lean_ctor_get(v_t_1460_, 2);
lean_inc(v_v_1463_);
v_l_1464_ = lean_ctor_get(v_t_1460_, 3);
lean_inc(v_l_1464_);
v_r_1465_ = lean_ctor_get(v_t_1460_, 4);
lean_inc(v_r_1465_);
lean_dec_ref(v_t_1460_);
lean_inc_ref(v_cmp_1459_);
lean_inc(v_k_1461_);
v___x_1466_ = lean_apply_2(v_cmp_1459_, v_k_1461_, v_k_1462_);
v___x_1467_ = lean_unbox(v___x_1466_);
switch(v___x_1467_)
{
case 0:
{
lean_dec(v_r_1465_);
lean_dec(v_v_1463_);
v_t_1460_ = v_l_1464_;
goto _start;
}
case 1:
{
lean_object* v___x_1469_; 
lean_dec(v_r_1465_);
lean_dec(v_l_1464_);
lean_dec(v_k_1461_);
lean_dec_ref(v_cmp_1459_);
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_v_1463_);
return v___x_1469_;
}
default: 
{
lean_dec(v_l_1464_);
lean_dec(v_v_1463_);
v_t_1460_ = v_r_1465_;
goto _start;
}
}
}
else
{
lean_object* v___x_1471_; 
lean_dec(v_k_1461_);
lean_dec_ref(v_cmp_1459_);
v___x_1471_ = lean_box(0);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_cmp_1472_, lean_object* v_t_u2082_1473_, lean_object* v_init_1474_, lean_object* v_x_1475_){
_start:
{
if (lean_obj_tag(v_x_1475_) == 0)
{
lean_object* v_k_1476_; lean_object* v_v_1477_; lean_object* v_l_1478_; lean_object* v_r_1479_; lean_object* v___x_1480_; 
v_k_1476_ = lean_ctor_get(v_x_1475_, 1);
lean_inc(v_k_1476_);
v_v_1477_ = lean_ctor_get(v_x_1475_, 2);
lean_inc(v_v_1477_);
v_l_1478_ = lean_ctor_get(v_x_1475_, 3);
lean_inc(v_l_1478_);
v_r_1479_ = lean_ctor_get(v_x_1475_, 4);
lean_inc(v_r_1479_);
lean_dec_ref(v_x_1475_);
lean_inc(v_t_u2082_1473_);
lean_inc_ref(v_cmp_1472_);
v___x_1480_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_1472_, v_t_u2082_1473_, v_init_1474_, v_l_1478_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_dec(v_r_1479_);
lean_dec(v_v_1477_);
lean_dec(v_k_1476_);
lean_dec(v_t_u2082_1473_);
lean_dec_ref(v_cmp_1472_);
return v___x_1480_;
}
else
{
lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1496_; 
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v___x_1480_, 0);
lean_dec(v_unused_1497_);
v___x_1482_ = v___x_1480_;
v_isShared_1483_ = v_isSharedCheck_1496_;
goto v_resetjp_1481_;
}
else
{
lean_dec(v___x_1480_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1496_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1484_ = lean_box(0);
lean_inc(v_t_u2082_1473_);
lean_inc_ref(v_cmp_1472_);
v___x_1485_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1472_, v_t_u2082_1473_, v_k_1476_);
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_v_1477_);
v___x_1487_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v___x_1485_, v___x_1486_);
lean_dec_ref(v___x_1486_);
lean_dec(v___x_1485_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_dec(v_r_1479_);
lean_dec(v_t_u2082_1473_);
lean_dec_ref(v_cmp_1472_);
v___x_1488_ = lean_box(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
lean_ctor_set(v___x_1490_, 1, v___x_1484_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set_tag(v___x_1482_, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1490_);
v___x_1492_ = v___x_1482_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
else
{
lean_object* v___x_1494_; 
lean_del_object(v___x_1482_);
v___x_1494_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v_init_1474_ = v___x_1494_;
v_x_1475_ = v_r_1479_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1498_; 
lean_dec(v_t_u2082_1473_);
lean_dec_ref(v_cmp_1472_);
v___x_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_init_1474_);
return v___x_1498_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_1499_, lean_object* v_t_u2081_1500_, lean_object* v_t_u2082_1501_){
_start:
{
lean_object* v___y_1503_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1516_; 
if (lean_obj_tag(v_t_u2081_1500_) == 0)
{
lean_object* v_size_1519_; 
v_size_1519_ = lean_ctor_get(v_t_u2081_1500_, 0);
lean_inc(v_size_1519_);
v___y_1516_ = v_size_1519_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
v___y_1516_ = v___x_1520_;
goto v___jp_1515_;
}
v___jp_1502_:
{
lean_object* v_fst_1504_; 
v_fst_1504_ = lean_ctor_get(v___y_1503_, 0);
lean_inc(v_fst_1504_);
lean_dec_ref(v___y_1503_);
if (lean_obj_tag(v_fst_1504_) == 0)
{
uint8_t v___x_1505_; 
v___x_1505_ = 1;
return v___x_1505_;
}
else
{
lean_object* v_val_1506_; uint8_t v___x_1507_; 
v_val_1506_ = lean_ctor_get(v_fst_1504_, 0);
lean_inc(v_val_1506_);
lean_dec_ref(v_fst_1504_);
v___x_1507_ = lean_unbox(v_val_1506_);
lean_dec(v_val_1506_);
return v___x_1507_;
}
}
v___jp_1508_:
{
uint8_t v___x_1511_; 
v___x_1511_ = lean_nat_dec_eq(v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec(v___y_1509_);
if (v___x_1511_ == 0)
{
lean_dec(v_t_u2082_1501_);
lean_dec(v_t_u2081_1500_);
lean_dec_ref(v_cmp_1499_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v_a_1514_; 
v___x_1512_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___x_1513_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_1499_, v_t_u2082_1501_, v___x_1512_, v_t_u2081_1500_);
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref(v___x_1513_);
v___y_1503_ = v_a_1514_;
goto v___jp_1502_;
}
}
v___jp_1515_:
{
if (lean_obj_tag(v_t_u2082_1501_) == 0)
{
lean_object* v_size_1517_; 
v_size_1517_ = lean_ctor_get(v_t_u2082_1501_, 0);
lean_inc(v_size_1517_);
v___y_1509_ = v___y_1516_;
v___y_1510_ = v_size_1517_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_unsigned_to_nat(0u);
v___y_1509_ = v___y_1516_;
v___y_1510_ = v___x_1518_;
goto v___jp_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_1521_, lean_object* v_t_u2081_1522_, lean_object* v_t_u2082_1523_){
_start:
{
uint8_t v_res_1524_; lean_object* v_r_1525_; 
v_res_1524_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1521_, v_t_u2081_1522_, v_t_u2082_1523_);
v_r_1525_ = lean_box(v_res_1524_);
return v_r_1525_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_beq___redArg(lean_object* v_cmp_1526_, lean_object* v_t_u2081_1527_, lean_object* v_t_u2082_1528_){
_start:
{
uint8_t v___x_1529_; 
v___x_1529_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1526_, v_t_u2081_1527_, v_t_u2082_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___redArg___boxed(lean_object* v_cmp_1530_, lean_object* v_t_u2081_1531_, lean_object* v_t_u2082_1532_){
_start:
{
uint8_t v_res_1533_; lean_object* v_r_1534_; 
v_res_1533_ = l_Std_TreeSet_Raw_beq___redArg(v_cmp_1530_, v_t_u2081_1531_, v_t_u2082_1532_);
v_r_1534_ = lean_box(v_res_1533_);
return v_r_1534_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_beq(lean_object* v_00_u03b1_1535_, lean_object* v_cmp_1536_, lean_object* v_t_u2081_1537_, lean_object* v_t_u2082_1538_){
_start:
{
uint8_t v___x_1539_; 
v___x_1539_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1536_, v_t_u2081_1537_, v_t_u2082_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___boxed(lean_object* v_00_u03b1_1540_, lean_object* v_cmp_1541_, lean_object* v_t_u2081_1542_, lean_object* v_t_u2082_1543_){
_start:
{
uint8_t v_res_1544_; lean_object* v_r_1545_; 
v_res_1544_ = l_Std_TreeSet_Raw_beq(v_00_u03b1_1540_, v_cmp_1541_, v_t_u2081_1542_, v_t_u2082_1543_);
v_r_1545_ = lean_box(v_res_1544_);
return v_r_1545_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(lean_object* v_cmp_1546_, lean_object* v_t_u2081_1547_, lean_object* v_t_u2082_1548_){
_start:
{
uint8_t v___x_1549_; 
v___x_1549_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1546_, v_t_u2081_1547_, v_t_u2082_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg___boxed(lean_object* v_cmp_1550_, lean_object* v_t_u2081_1551_, lean_object* v_t_u2082_1552_){
_start:
{
uint8_t v_res_1553_; lean_object* v_r_1554_; 
v_res_1553_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(v_cmp_1550_, v_t_u2081_1551_, v_t_u2082_1552_);
v_r_1554_ = lean_box(v_res_1553_);
return v_r_1554_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(lean_object* v_00_u03b1_1555_, lean_object* v_cmp_1556_, lean_object* v_t_u2081_1557_, lean_object* v_t_u2082_1558_){
_start:
{
uint8_t v___x_1559_; 
v___x_1559_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1556_, v_t_u2081_1557_, v_t_u2082_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___boxed(lean_object* v_00_u03b1_1560_, lean_object* v_cmp_1561_, lean_object* v_t_u2081_1562_, lean_object* v_t_u2082_1563_){
_start:
{
uint8_t v_res_1564_; lean_object* v_r_1565_; 
v_res_1564_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(v_00_u03b1_1560_, v_cmp_1561_, v_t_u2081_1562_, v_t_u2082_1563_);
v_r_1565_ = lean_box(v_res_1564_);
return v_r_1565_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(lean_object* v_cmp_1566_, lean_object* v_t_u2081_1567_, lean_object* v_t_u2082_1568_){
_start:
{
uint8_t v___x_1569_; 
v___x_1569_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1566_, v_t_u2081_1567_, v_t_u2082_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_1570_, lean_object* v_t_u2081_1571_, lean_object* v_t_u2082_1572_){
_start:
{
uint8_t v_res_1573_; lean_object* v_r_1574_; 
v_res_1573_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(v_cmp_1570_, v_t_u2081_1571_, v_t_u2082_1572_);
v_r_1574_ = lean_box(v_res_1573_);
return v_r_1574_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(lean_object* v_00_u03b1_1575_, lean_object* v_cmp_1576_, lean_object* v_t_u2081_1577_, lean_object* v_t_u2082_1578_){
_start:
{
uint8_t v___x_1579_; 
v___x_1579_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1576_, v_t_u2081_1577_, v_t_u2082_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1580_, lean_object* v_cmp_1581_, lean_object* v_t_u2081_1582_, lean_object* v_t_u2082_1583_){
_start:
{
uint8_t v_res_1584_; lean_object* v_r_1585_; 
v_res_1584_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(v_00_u03b1_1580_, v_cmp_1581_, v_t_u2081_1582_, v_t_u2082_1583_);
v_r_1585_ = lean_box(v_res_1584_);
return v_r_1585_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1586_, lean_object* v_cmp_1587_, lean_object* v_t_u2081_1588_, lean_object* v_t_u2082_1589_){
_start:
{
uint8_t v___x_1590_; 
v___x_1590_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1587_, v_t_u2081_1588_, v_t_u2082_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1591_, lean_object* v_cmp_1592_, lean_object* v_t_u2081_1593_, lean_object* v_t_u2082_1594_){
_start:
{
uint8_t v_res_1595_; lean_object* v_r_1596_; 
v_res_1595_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(v_00_u03b1_1591_, v_cmp_1592_, v_t_u2081_1593_, v_t_u2082_1594_);
v_r_1596_ = lean_box(v_res_1595_);
return v_r_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1597_, lean_object* v_cmp_1598_, lean_object* v_00_u03b4_1599_, lean_object* v_t_1600_, lean_object* v_k_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1598_, v_t_1600_, v_k_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1603_, lean_object* v_cmp_1604_, lean_object* v_t_u2082_1605_, lean_object* v_init_1606_, lean_object* v_x_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_1604_, v_t_u2082_1605_, v_init_1606_, v_x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq___redArg(lean_object* v_cmp_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_beq___boxed), 4, 2);
lean_closure_set(v___x_1610_, 0, lean_box(0));
lean_closure_set(v___x_1610_, 1, v_cmp_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq(lean_object* v_00_u03b1_1611_, lean_object* v_cmp_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_beq___boxed), 4, 2);
lean_closure_set(v___x_1613_, 0, lean_box(0));
lean_closure_set(v___x_1613_, 1, v_cmp_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff___redArg(lean_object* v_cmp_1614_, lean_object* v_t_u2081_1615_, lean_object* v_t_u2082_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_1614_, v_t_u2081_1615_, v_t_u2082_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff(lean_object* v_00_u03b1_1618_, lean_object* v_cmp_1619_, lean_object* v_t_u2081_1620_, lean_object* v_t_u2082_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_1619_, v_t_u2081_1620_, v_t_u2082_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff___redArg(lean_object* v_cmp_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_diff), 4, 2);
lean_closure_set(v___x_1624_, 0, lean_box(0));
lean_closure_set(v___x_1624_, 1, v_cmp_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff(lean_object* v_00_u03b1_1625_, lean_object* v_cmp_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_diff), 4, 2);
lean_closure_set(v___x_1627_, 0, lean_box(0));
lean_closure_set(v___x_1627_, 1, v_cmp_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_1628_, lean_object* v_a_1629_, lean_object* v_____s_1630_){
_start:
{
lean_object* v_r_1631_; lean_object* v___x_1632_; 
v_r_1631_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_1628_, v_a_1629_, v_____s_1630_);
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_r_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg(lean_object* v_cmp_1633_, lean_object* v_inst_1634_, lean_object* v_t_1635_, lean_object* v_l_1636_){
_start:
{
lean_object* v___f_1637_; lean_object* v___x_1638_; 
v___f_1637_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1637_, 0, v_cmp_1633_);
v___x_1638_ = lean_apply_4(v_inst_1634_, lean_box(0), v_l_1636_, v_t_1635_, v___f_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany(lean_object* v_00_u03b1_1639_, lean_object* v_cmp_1640_, lean_object* v_00_u03c1_1641_, lean_object* v_inst_1642_, lean_object* v_t_1643_, lean_object* v_l_1644_){
_start:
{
lean_object* v___f_1645_; lean_object* v___x_1646_; 
v___f_1645_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1645_, 0, v_cmp_1640_);
v___x_1646_ = lean_apply_4(v_inst_1642_, lean_box(0), v_l_1644_, v_t_1643_, v___f_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1(lean_object* v___f_1650_, lean_object* v_inst_1651_, lean_object* v_m_1652_, lean_object* v_prec_1653_){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1654_ = ((lean_object*)(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1));
v___x_1655_ = lean_box(0);
v___x_1656_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1657_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1656_, v___f_1650_, v___x_1655_, v_m_1652_);
v___x_1658_ = l_List_repr___redArg(v_inst_1651_, v___x_1657_);
v___x_1659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1654_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = l_Repr_addAppParen(v___x_1659_, v_prec_1653_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_1661_, lean_object* v_inst_1662_, lean_object* v_m_1663_, lean_object* v_prec_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Std_TreeSet_Raw_instRepr___redArg___lam__1(v___f_1661_, v_inst_1662_, v_m_1663_, v_prec_1664_);
lean_dec(v_prec_1664_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg(lean_object* v_inst_1666_){
_start:
{
lean_object* v___f_1667_; lean_object* v___f_1668_; 
v___f_1667_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___f_1668_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1668_, 0, v___f_1667_);
lean_closure_set(v___f_1668_, 1, v_inst_1666_);
return v___f_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr(lean_object* v_00_u03b1_1669_, lean_object* v_cmp_1670_, lean_object* v_inst_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Std_TreeSet_Raw_instRepr___redArg(v_inst_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___boxed(lean_object* v_00_u03b1_1673_, lean_object* v_cmp_1674_, lean_object* v_inst_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Std_TreeSet_Raw_instRepr(v_00_u03b1_1673_, v_cmp_1674_, v_inst_1675_);
lean_dec_ref(v_cmp_1674_);
return v_res_1676_;
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
