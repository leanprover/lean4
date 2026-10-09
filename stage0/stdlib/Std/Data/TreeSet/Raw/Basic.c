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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__15 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__15_value;
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_TreeSet_Raw___auto__1___closed__16 = (const lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__16_value;
static const lean_ctor_object l_Std_TreeSet_Raw___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__15_value),((lean_object*)&l_Std_TreeSet_Raw___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__17));
v___x_45_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__13, &l_Std_TreeSet_Raw___auto__1___closed__13_once, _init_l_Std_TreeSet_Raw___auto__1___closed__13);
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__18, &l_Std_TreeSet_Raw___auto__1___closed__18_once, _init_l_Std_TreeSet_Raw___auto__1___closed__18);
v___x_48_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__11));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__19, &l_Std_TreeSet_Raw___auto__1___closed__19_once, _init_l_Std_TreeSet_Raw___auto__1___closed__19);
v___x_52_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__20, &l_Std_TreeSet_Raw___auto__1___closed__20_once, _init_l_Std_TreeSet_Raw___auto__1___closed__20);
v___x_55_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__9));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__22(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__21, &l_Std_TreeSet_Raw___auto__1___closed__21_once, _init_l_Std_TreeSet_Raw___auto__1___closed__21);
v___x_59_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__23(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__22, &l_Std_TreeSet_Raw___auto__1___closed__22_once, _init_l_Std_TreeSet_Raw___auto__1___closed__22);
v___x_62_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__7));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__24(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__23, &l_Std_TreeSet_Raw___auto__1___closed__23_once, _init_l_Std_TreeSet_Raw___auto__1___closed__23);
v___x_66_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1___closed__25(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__24, &l_Std_TreeSet_Raw___auto__1___closed__24_once, _init_l_Std_TreeSet_Raw___auto__1___closed__24);
v___x_69_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__4));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___auto__1(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__25, &l_Std_TreeSet_Raw___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw___auto__1___closed__25);
return v___x_72_;
}
}
lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_75_;
v_res_75_ = l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg();
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg___boxed(lean_object* v___dummy_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner(lean_object* v_00_u03b1_78_, lean_object* v_cmp_79_, lean_object* v_t_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(0);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___boxed(lean_object* v_00_u03b1_82_, lean_object* v_cmp_83_, lean_object* v_t_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Std_TreeSet_Raw_instCoeWFWFUnitInner(v_00_u03b1_82_, v_cmp_83_, v_t_84_);
lean_dec(v_t_84_);
lean_dec_ref(v_cmp_83_);
return v_res_85_;
}
}
lean_object* l_Std_TreeSet_Raw_empty___redArg(){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(1);
return v___x_87_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_88_;
v_res_88_ = l_Std_TreeSet_Raw_empty___redArg();
stack->m_obj
 = v_res_88_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty___redArg___boxed(lean_object* v___dummy_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_TreeSet_Raw_empty___redArg();
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty(lean_object* v_00_u03b1_91_, lean_object* v_cmp_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_box(1);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty___boxed(lean_object* v_00_u03b1_94_, lean_object* v_cmp_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_TreeSet_Raw_empty(v_00_u03b1_94_, v_cmp_95_);
lean_dec_ref(v_cmp_95_);
return v_res_96_;
}
}
lean_object* l_Std_TreeSet_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_box(1);
return v___x_98_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_99_;
v_res_99_ = l_Std_TreeSet_Raw_instEmptyCollection___redArg();
stack->m_obj
 = v_res_99_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Std_TreeSet_Raw_instEmptyCollection___redArg();
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection(lean_object* v_00_u03b1_102_, lean_object* v_cmp_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(1);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___boxed(lean_object* v_00_u03b1_105_, lean_object* v_cmp_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_TreeSet_Raw_instEmptyCollection(v_00_u03b1_105_, v_cmp_106_);
lean_dec_ref(v_cmp_106_);
return v_res_107_;
}
}
lean_object* l_Std_TreeSet_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(1);
return v___x_109_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_110_;
v_res_110_ = l_Std_TreeSet_Raw_instInhabited___redArg();
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_TreeSet_Raw_instInhabited___redArg();
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited(lean_object* v_00_u03b1_113_, lean_object* v_cmp_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(1);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___boxed(lean_object* v_00_u03b1_116_, lean_object* v_cmp_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_TreeSet_Raw_instInhabited(v_00_u03b1_116_, v_cmp_117_);
lean_dec_ref(v_cmp_117_);
return v_res_118_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3));
v___x_159_ = l_String_toRawSubstring_x27(v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(lean_object* v_x_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__4));
lean_inc(v_x_178_);
v___x_182_ = l_Lean_Syntax_isOfKind(v_x_178_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_x_178_);
v___x_183_ = lean_box(1);
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_a_180_);
return v___x_184_;
}
else
{
lean_object* v_quotContext_185_; lean_object* v_currMacroScope_186_; lean_object* v_ref_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_quotContext_185_ = lean_ctor_get(v_a_179_, 1);
v_currMacroScope_186_ = lean_ctor_get(v_a_179_, 2);
v_ref_187_ = lean_ctor_get(v_a_179_, 5);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = l_Lean_Syntax_getArg(v_x_178_, v___x_188_);
v___x_190_ = lean_unsigned_to_nat(2u);
v___x_191_ = l_Lean_Syntax_getArg(v_x_178_, v___x_190_);
lean_dec(v_x_178_);
v___x_192_ = 0;
v___x_193_ = l_Lean_SourceInfo_fromRef(v_ref_187_, v___x_192_);
v___x_194_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2));
v___x_195_ = lean_obj_once(&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4, &l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4_once, _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4);
v___x_196_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_186_);
lean_inc(v_quotContext_185_);
v___x_197_ = l_Lean_addMacroScope(v_quotContext_185_, v___x_196_, v_currMacroScope_186_);
v___x_198_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10));
lean_inc_n(v___x_193_, 2);
v___x_199_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_199_, 0, v___x_193_);
lean_ctor_set(v___x_199_, 1, v___x_195_);
lean_ctor_set(v___x_199_, 2, v___x_197_);
lean_ctor_set(v___x_199_, 3, v___x_198_);
v___x_200_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__9));
v___x_201_ = l_Lean_Syntax_node2(v___x_193_, v___x_200_, v___x_189_, v___x_191_);
v___x_202_ = l_Lean_Syntax_node2(v___x_193_, v___x_194_, v___x_199_, v___x_201_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_a_180_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___boxed(lean_object* v_x_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(v_x_204_, v_a_205_, v_a_206_);
lean_dec_ref(v_a_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(lean_object* v_x_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2));
lean_inc(v_x_211_);
v___x_215_ = l_Lean_Syntax_isOfKind(v_x_211_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec(v_x_211_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v_a_213_);
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = l_Lean_Syntax_getArg(v_x_211_, v___x_218_);
v___x_220_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1));
lean_inc(v___x_219_);
v___x_221_ = l_Lean_Syntax_isOfKind(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec(v___x_219_);
lean_dec(v_x_211_);
v___x_222_ = lean_box(0);
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v_a_213_);
return v___x_223_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = l_Lean_Syntax_getArg(v_x_211_, v___x_224_);
lean_dec(v_x_211_);
v___x_226_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_225_);
v___x_227_ = l_Lean_Syntax_matchesNull(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v___x_225_);
lean_dec(v___x_219_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_a_213_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_ref_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_230_ = l_Lean_Syntax_getArg(v___x_225_, v___x_218_);
v___x_231_ = l_Lean_Syntax_getArg(v___x_225_, v___x_224_);
lean_dec(v___x_225_);
v_ref_232_ = l_Lean_replaceRef(v___x_219_, v_a_212_);
lean_dec(v___x_219_);
v___x_233_ = 0;
v___x_234_ = l_Lean_SourceInfo_fromRef(v_ref_232_, v___x_233_);
lean_dec(v_ref_232_);
v___x_235_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__4));
v___x_236_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__7));
lean_inc(v___x_234_);
v___x_237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_234_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = l_Lean_Syntax_node3(v___x_234_, v___x_235_, v___x_230_, v___x_237_, v___x_231_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_a_213_);
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___boxed(lean_object* v_x_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(v_x_240_, v_a_241_, v_a_242_);
lean_dec(v_a_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert___redArg(lean_object* v_cmp_244_, lean_object* v_l_245_, lean_object* v_a_246_){
_start:
{
uint8_t v___x_247_; 
lean_inc(v_l_245_);
lean_inc(v_a_246_);
lean_inc_ref(v_cmp_244_);
v___x_247_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_244_, v_a_246_, v_l_245_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_box(0);
v___x_249_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_244_, v_a_246_, v___x_248_, v_l_245_);
return v___x_249_;
}
else
{
lean_dec(v_a_246_);
lean_dec_ref(v_cmp_244_);
return v_l_245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert(lean_object* v_00_u03b1_250_, lean_object* v_cmp_251_, lean_object* v_l_252_, lean_object* v_a_253_){
_start:
{
uint8_t v___x_254_; 
lean_inc(v_l_252_);
lean_inc(v_a_253_);
lean_inc_ref(v_cmp_251_);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_251_, v_a_253_, v_l_252_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_box(0);
v___x_256_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_251_, v_a_253_, v___x_255_, v_l_252_);
return v___x_256_;
}
else
{
lean_dec(v_a_253_);
lean_dec_ref(v_cmp_251_);
return v_l_252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg___lam__0(lean_object* v_cmp_257_, lean_object* v_e_258_){
_start:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_box(1);
lean_inc(v_e_258_);
lean_inc_ref(v_cmp_257_);
v___x_260_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_257_, v_e_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_box(0);
v___x_262_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_257_, v_e_258_, v___x_261_, v___x_259_);
return v___x_262_;
}
else
{
lean_dec(v_e_258_);
lean_dec_ref(v_cmp_257_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg(lean_object* v_cmp_263_){
_start:
{
lean_object* v___f_264_; 
v___f_264_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_264_, 0, v_cmp_263_);
return v___f_264_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton(lean_object* v_00_u03b1_265_, lean_object* v_cmp_266_){
_start:
{
lean_object* v___f_267_; 
v___f_267_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_267_, 0, v_cmp_266_);
return v___f_267_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg___lam__0(lean_object* v_cmp_268_, lean_object* v_e_269_, lean_object* v_s_270_){
_start:
{
uint8_t v___x_271_; 
lean_inc(v_s_270_);
lean_inc(v_e_269_);
lean_inc_ref(v_cmp_268_);
v___x_271_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_268_, v_e_269_, v_s_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_box(0);
v___x_273_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_268_, v_e_269_, v___x_272_, v_s_270_);
return v___x_273_;
}
else
{
lean_dec(v_e_269_);
lean_dec_ref(v_cmp_268_);
return v_s_270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg(lean_object* v_cmp_274_){
_start:
{
lean_object* v___f_275_; 
v___f_275_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_275_, 0, v_cmp_274_);
return v___f_275_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert(lean_object* v_00_u03b1_276_, lean_object* v_cmp_277_){
_start:
{
lean_object* v___f_278_; 
v___f_278_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_278_, 0, v_cmp_277_);
return v___f_278_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert___redArg(lean_object* v_cmp_279_, lean_object* v_t_280_, lean_object* v_a_281_){
_start:
{
uint8_t v___x_282_; 
lean_inc(v_t_280_);
lean_inc(v_a_281_);
lean_inc_ref(v_cmp_279_);
v___x_282_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_279_, v_a_281_, v_t_280_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_283_ = lean_box(0);
v___x_284_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_279_, v_a_281_, v___x_283_, v_t_280_);
v___x_285_ = lean_box(v___x_282_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_284_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_a_281_);
lean_dec_ref(v_cmp_279_);
v___x_287_ = lean_box(v___x_282_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_t_280_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert(lean_object* v_00_u03b1_289_, lean_object* v_cmp_290_, lean_object* v_t_291_, lean_object* v_a_292_){
_start:
{
uint8_t v___x_293_; 
lean_inc(v_t_291_);
lean_inc(v_a_292_);
lean_inc_ref(v_cmp_290_);
v___x_293_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_290_, v_a_292_, v_t_291_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_294_ = lean_box(0);
v___x_295_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_290_, v_a_292_, v___x_294_, v_t_291_);
v___x_296_ = lean_box(v___x_293_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
return v___x_297_;
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_a_292_);
lean_dec_ref(v_cmp_290_);
v___x_298_ = lean_box(v___x_293_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_t_291_);
return v___x_299_;
}
}
}
uint8_t l_Std_TreeSet_Raw_contains___redArg(lean_object* v_cmp_300_, lean_object* v_l_301_, lean_object* v_a_302_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_300_, v_a_302_, v_l_301_);
return v___x_303_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_300_ = stack[0].m_obj;
lean_object* v_l_301_ = stack[1].m_obj;
lean_object* v_a_302_ = stack[2].m_obj;
uint8_t v_res_304_;
v_res_304_ = l_Std_TreeSet_Raw_contains___redArg(v_cmp_300_, v_l_301_, v_a_302_);
stack->m_num = v_res_304_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___redArg___boxed(lean_object* v_cmp_305_, lean_object* v_l_306_, lean_object* v_a_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l_Std_TreeSet_Raw_contains___redArg(v_cmp_305_, v_l_306_, v_a_307_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
uint8_t l_Std_TreeSet_Raw_contains(lean_object* v_00_u03b1_310_, lean_object* v_cmp_311_, lean_object* v_l_312_, lean_object* v_a_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_311_, v_a_313_, v_l_312_);
return v___x_314_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_311_ = stack[1].m_obj;
lean_object* v_l_312_ = stack[2].m_obj;
lean_object* v_a_313_ = stack[3].m_obj;
uint8_t v_res_315_;
v_res_315_ = l_Std_TreeSet_Raw_contains(lean_box(0), v_cmp_311_, v_l_312_, v_a_313_);
stack->m_num = v_res_315_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___boxed(lean_object* v_00_u03b1_316_, lean_object* v_cmp_317_, lean_object* v_l_318_, lean_object* v_a_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Std_TreeSet_Raw_contains(v_00_u03b1_316_, v_cmp_317_, v_l_318_, v_a_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
lean_object* l_Std_TreeSet_Raw_instMembership___redArg(){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_box(0);
return v___x_323_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_324_;
v_res_324_ = l_Std_TreeSet_Raw_instMembership___redArg();
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___redArg___boxed(lean_object* v___dummy_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_TreeSet_Raw_instMembership___redArg();
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership(lean_object* v_00_u03b1_327_, lean_object* v_cmp_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(0);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___boxed(lean_object* v_00_u03b1_330_, lean_object* v_cmp_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_TreeSet_Raw_instMembership(v_00_u03b1_330_, v_cmp_331_);
lean_dec_ref(v_cmp_331_);
return v_res_332_;
}
}
uint8_t l_Std_TreeSet_Raw_instDecidableMem___redArg(lean_object* v_cmp_333_, lean_object* v_t_334_, lean_object* v_a_335_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_333_, v_a_335_, v_t_334_);
return v___x_336_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_333_ = stack[0].m_obj;
lean_object* v_t_334_ = stack[1].m_obj;
lean_object* v_a_335_ = stack[2].m_obj;
uint8_t v_res_337_;
v_res_337_ = l_Std_TreeSet_Raw_instDecidableMem___redArg(v_cmp_333_, v_t_334_, v_a_335_);
stack->m_num = v_res_337_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_338_, lean_object* v_t_339_, lean_object* v_a_340_){
_start:
{
uint8_t v_res_341_; lean_object* v_r_342_; 
v_res_341_ = l_Std_TreeSet_Raw_instDecidableMem___redArg(v_cmp_338_, v_t_339_, v_a_340_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
uint8_t l_Std_TreeSet_Raw_instDecidableMem(lean_object* v_00_u03b1_343_, lean_object* v_cmp_344_, lean_object* v_t_345_, lean_object* v_a_346_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_344_, v_a_346_, v_t_345_);
return v___x_347_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_344_ = stack[1].m_obj;
lean_object* v_t_345_ = stack[2].m_obj;
lean_object* v_a_346_ = stack[3].m_obj;
uint8_t v_res_348_;
v_res_348_ = l_Std_TreeSet_Raw_instDecidableMem(lean_box(0), v_cmp_344_, v_t_345_, v_a_346_);
stack->m_num = v_res_348_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_349_, lean_object* v_cmp_350_, lean_object* v_t_351_, lean_object* v_a_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Std_TreeSet_Raw_instDecidableMem(v_00_u03b1_349_, v_cmp_350_, v_t_351_, v_a_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg(lean_object* v_t_355_){
_start:
{
if (lean_obj_tag(v_t_355_) == 0)
{
lean_object* v_size_356_; 
v_size_356_ = lean_ctor_get(v_t_355_, 0);
lean_inc(v_size_356_);
return v_size_356_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = lean_unsigned_to_nat(0u);
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg___boxed(lean_object* v_t_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_TreeSet_Raw_size___redArg(v_t_358_);
lean_dec(v_t_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size(lean_object* v_00_u03b1_360_, lean_object* v_cmp_361_, lean_object* v_t_362_){
_start:
{
if (lean_obj_tag(v_t_362_) == 0)
{
lean_object* v_size_363_; 
v_size_363_ = lean_ctor_get(v_t_362_, 0);
lean_inc(v_size_363_);
return v_size_363_;
}
else
{
lean_object* v___x_364_; 
v___x_364_ = lean_unsigned_to_nat(0u);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___boxed(lean_object* v_00_u03b1_365_, lean_object* v_cmp_366_, lean_object* v_t_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_TreeSet_Raw_size(v_00_u03b1_365_, v_cmp_366_, v_t_367_);
lean_dec(v_t_367_);
lean_dec_ref(v_cmp_366_);
return v_res_368_;
}
}
uint8_t l_Std_TreeSet_Raw_isEmpty___redArg(lean_object* v_t_369_){
_start:
{
if (lean_obj_tag(v_t_369_) == 0)
{
uint8_t v___x_370_; 
v___x_370_ = 0;
return v___x_370_;
}
else
{
uint8_t v___x_371_; 
v___x_371_ = 1;
return v___x_371_;
}
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_369_ = stack[0].m_obj;
uint8_t v_res_372_;
v_res_372_ = l_Std_TreeSet_Raw_isEmpty___redArg(v_t_369_);
stack->m_num = v_res_372_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___redArg___boxed(lean_object* v_t_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_Std_TreeSet_Raw_isEmpty___redArg(v_t_373_);
lean_dec(v_t_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
uint8_t l_Std_TreeSet_Raw_isEmpty(lean_object* v_00_u03b1_376_, lean_object* v_cmp_377_, lean_object* v_t_378_){
_start:
{
if (lean_obj_tag(v_t_378_) == 0)
{
uint8_t v___x_379_; 
v___x_379_ = 0;
return v___x_379_;
}
else
{
uint8_t v___x_380_; 
v___x_380_ = 1;
return v___x_380_;
}
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_377_ = stack[1].m_obj;
lean_object* v_t_378_ = stack[2].m_obj;
uint8_t v_res_381_;
v_res_381_ = l_Std_TreeSet_Raw_isEmpty(lean_box(0), v_cmp_377_, v_t_378_);
stack->m_num = v_res_381_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___boxed(lean_object* v_00_u03b1_382_, lean_object* v_cmp_383_, lean_object* v_t_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l_Std_TreeSet_Raw_isEmpty(v_00_u03b1_382_, v_cmp_383_, v_t_384_);
lean_dec(v_t_384_);
lean_dec_ref(v_cmp_383_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase___redArg(lean_object* v_cmp_387_, lean_object* v_t_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_387_, v_a_389_, v_t_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase(lean_object* v_00_u03b1_391_, lean_object* v_cmp_392_, lean_object* v_t_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_392_, v_a_394_, v_t_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f___redArg(lean_object* v_cmp_396_, lean_object* v_t_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_396_, v_t_397_, v_a_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f(lean_object* v_00_u03b1_400_, lean_object* v_cmp_401_, lean_object* v_t_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_401_, v_t_402_, v_a_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get___redArg(lean_object* v_cmp_405_, lean_object* v_t_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_405_, v_t_406_, v_a_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get(lean_object* v_00_u03b1_409_, lean_object* v_cmp_410_, lean_object* v_t_411_, lean_object* v_a_412_, lean_object* v_h_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_410_, v_t_411_, v_a_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___redArg(lean_object* v_cmp_415_, lean_object* v_inst_416_, lean_object* v_t_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_415_, v_t_417_, v_a_418_, v_inst_416_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___redArg___boxed(lean_object* v_cmp_420_, lean_object* v_inst_421_, lean_object* v_t_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_TreeSet_Raw_get_x21___redArg(v_cmp_420_, v_inst_421_, v_t_422_, v_a_423_);
lean_dec(v_inst_421_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21(lean_object* v_00_u03b1_425_, lean_object* v_cmp_426_, lean_object* v_inst_427_, lean_object* v_t_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_426_, v_t_428_, v_a_429_, v_inst_427_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___boxed(lean_object* v_00_u03b1_431_, lean_object* v_cmp_432_, lean_object* v_inst_433_, lean_object* v_t_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_TreeSet_Raw_get_x21(v_00_u03b1_431_, v_cmp_432_, v_inst_433_, v_t_434_, v_a_435_);
lean_dec(v_inst_433_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg(lean_object* v_cmp_437_, lean_object* v_t_438_, lean_object* v_a_439_, lean_object* v_fallback_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_437_, v_t_438_, v_a_439_, v_fallback_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg___boxed(lean_object* v_cmp_442_, lean_object* v_t_443_, lean_object* v_a_444_, lean_object* v_fallback_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_TreeSet_Raw_getD___redArg(v_cmp_442_, v_t_443_, v_a_444_, v_fallback_445_);
lean_dec(v_fallback_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD(lean_object* v_00_u03b1_447_, lean_object* v_cmp_448_, lean_object* v_t_449_, lean_object* v_a_450_, lean_object* v_fallback_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_448_, v_t_449_, v_a_450_, v_fallback_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___boxed(lean_object* v_00_u03b1_453_, lean_object* v_cmp_454_, lean_object* v_t_455_, lean_object* v_a_456_, lean_object* v_fallback_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_TreeSet_Raw_getD(v_00_u03b1_453_, v_cmp_454_, v_t_455_, v_a_456_, v_fallback_457_);
lean_dec(v_fallback_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg(lean_object* v_t_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg___boxed(lean_object* v_t_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_TreeSet_Raw_min_x3f___redArg(v_t_461_);
lean_dec(v_t_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f(lean_object* v_00_u03b1_463_, lean_object* v_cmp_464_, lean_object* v_t_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___boxed(lean_object* v_00_u03b1_467_, lean_object* v_cmp_468_, lean_object* v_t_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_TreeSet_Raw_min_x3f(v_00_u03b1_467_, v_cmp_468_, v_t_469_);
lean_dec(v_t_469_);
lean_dec_ref(v_cmp_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg(lean_object* v_inst_471_, lean_object* v_t_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_471_, v_t_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg___boxed(lean_object* v_inst_474_, lean_object* v_t_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_TreeSet_Raw_min_x21___redArg(v_inst_474_, v_t_475_);
lean_dec(v_t_475_);
lean_dec(v_inst_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21(lean_object* v_00_u03b1_477_, lean_object* v_cmp_478_, lean_object* v_inst_479_, lean_object* v_t_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_479_, v_t_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___boxed(lean_object* v_00_u03b1_482_, lean_object* v_cmp_483_, lean_object* v_inst_484_, lean_object* v_t_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_TreeSet_Raw_min_x21(v_00_u03b1_482_, v_cmp_483_, v_inst_484_, v_t_485_);
lean_dec(v_t_485_);
lean_dec(v_inst_484_);
lean_dec_ref(v_cmp_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg(lean_object* v_t_487_, lean_object* v_fallback_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_487_, v_fallback_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg___boxed(lean_object* v_t_490_, lean_object* v_fallback_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_TreeSet_Raw_minD___redArg(v_t_490_, v_fallback_491_);
lean_dec(v_fallback_491_);
lean_dec(v_t_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD(lean_object* v_00_u03b1_493_, lean_object* v_cmp_494_, lean_object* v_t_495_, lean_object* v_fallback_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_495_, v_fallback_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___boxed(lean_object* v_00_u03b1_498_, lean_object* v_cmp_499_, lean_object* v_t_500_, lean_object* v_fallback_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_TreeSet_Raw_minD(v_00_u03b1_498_, v_cmp_499_, v_t_500_, v_fallback_501_);
lean_dec(v_fallback_501_);
lean_dec(v_t_500_);
lean_dec_ref(v_cmp_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg(lean_object* v_t_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg___boxed(lean_object* v_t_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_TreeSet_Raw_max_x3f___redArg(v_t_505_);
lean_dec(v_t_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f(lean_object* v_00_u03b1_507_, lean_object* v_cmp_508_, lean_object* v_t_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___boxed(lean_object* v_00_u03b1_511_, lean_object* v_cmp_512_, lean_object* v_t_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_TreeSet_Raw_max_x3f(v_00_u03b1_511_, v_cmp_512_, v_t_513_);
lean_dec(v_t_513_);
lean_dec_ref(v_cmp_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg(lean_object* v_inst_515_, lean_object* v_t_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_515_, v_t_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg___boxed(lean_object* v_inst_518_, lean_object* v_t_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_TreeSet_Raw_max_x21___redArg(v_inst_518_, v_t_519_);
lean_dec(v_t_519_);
lean_dec(v_inst_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21(lean_object* v_00_u03b1_521_, lean_object* v_cmp_522_, lean_object* v_inst_523_, lean_object* v_t_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_523_, v_t_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___boxed(lean_object* v_00_u03b1_526_, lean_object* v_cmp_527_, lean_object* v_inst_528_, lean_object* v_t_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_TreeSet_Raw_max_x21(v_00_u03b1_526_, v_cmp_527_, v_inst_528_, v_t_529_);
lean_dec(v_t_529_);
lean_dec(v_inst_528_);
lean_dec_ref(v_cmp_527_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg(lean_object* v_t_531_, lean_object* v_fallback_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_531_, v_fallback_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg___boxed(lean_object* v_t_534_, lean_object* v_fallback_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_TreeSet_Raw_maxD___redArg(v_t_534_, v_fallback_535_);
lean_dec(v_fallback_535_);
lean_dec(v_t_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD(lean_object* v_00_u03b1_537_, lean_object* v_cmp_538_, lean_object* v_t_539_, lean_object* v_fallback_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_539_, v_fallback_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___boxed(lean_object* v_00_u03b1_542_, lean_object* v_cmp_543_, lean_object* v_t_544_, lean_object* v_fallback_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_TreeSet_Raw_maxD(v_00_u03b1_542_, v_cmp_543_, v_t_544_, v_fallback_545_);
lean_dec(v_fallback_545_);
lean_dec(v_t_544_);
lean_dec_ref(v_cmp_543_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg(lean_object* v_t_547_, lean_object* v_n_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_547_, v_n_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg___boxed(lean_object* v_t_550_, lean_object* v_n_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_TreeSet_Raw_atIdx_x3f___redArg(v_t_550_, v_n_551_);
lean_dec(v_t_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f(lean_object* v_00_u03b1_553_, lean_object* v_cmp_554_, lean_object* v_t_555_, lean_object* v_n_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_555_, v_n_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___boxed(lean_object* v_00_u03b1_558_, lean_object* v_cmp_559_, lean_object* v_t_560_, lean_object* v_n_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_TreeSet_Raw_atIdx_x3f(v_00_u03b1_558_, v_cmp_559_, v_t_560_, v_n_561_);
lean_dec(v_t_560_);
lean_dec_ref(v_cmp_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg(lean_object* v_inst_563_, lean_object* v_t_564_, lean_object* v_n_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_563_, v_t_564_, v_n_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg___boxed(lean_object* v_inst_567_, lean_object* v_t_568_, lean_object* v_n_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_TreeSet_Raw_atIdx_x21___redArg(v_inst_567_, v_t_568_, v_n_569_);
lean_dec(v_t_568_);
lean_dec(v_inst_567_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21(lean_object* v_00_u03b1_571_, lean_object* v_cmp_572_, lean_object* v_inst_573_, lean_object* v_t_574_, lean_object* v_n_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_573_, v_t_574_, v_n_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___boxed(lean_object* v_00_u03b1_577_, lean_object* v_cmp_578_, lean_object* v_inst_579_, lean_object* v_t_580_, lean_object* v_n_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_TreeSet_Raw_atIdx_x21(v_00_u03b1_577_, v_cmp_578_, v_inst_579_, v_t_580_, v_n_581_);
lean_dec(v_t_580_);
lean_dec(v_inst_579_);
lean_dec_ref(v_cmp_578_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg(lean_object* v_t_583_, lean_object* v_n_584_, lean_object* v_fallback_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_583_, v_n_584_, v_fallback_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg___boxed(lean_object* v_t_587_, lean_object* v_n_588_, lean_object* v_fallback_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_TreeSet_Raw_atIdxD___redArg(v_t_587_, v_n_588_, v_fallback_589_);
lean_dec(v_fallback_589_);
lean_dec(v_t_587_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD(lean_object* v_00_u03b1_591_, lean_object* v_cmp_592_, lean_object* v_t_593_, lean_object* v_n_594_, lean_object* v_fallback_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_593_, v_n_594_, v_fallback_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___boxed(lean_object* v_00_u03b1_597_, lean_object* v_cmp_598_, lean_object* v_t_599_, lean_object* v_n_600_, lean_object* v_fallback_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_TreeSet_Raw_atIdxD(v_00_u03b1_597_, v_cmp_598_, v_t_599_, v_n_600_, v_fallback_601_);
lean_dec(v_fallback_601_);
lean_dec(v_t_599_);
lean_dec_ref(v_cmp_598_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f___redArg(lean_object* v_cmp_603_, lean_object* v_t_604_, lean_object* v_k_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_box(0);
v___x_607_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_603_, v_k_605_, v___x_606_, v_t_604_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f(lean_object* v_00_u03b1_608_, lean_object* v_cmp_609_, lean_object* v_t_610_, lean_object* v_k_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_box(0);
v___x_613_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_609_, v_k_611_, v___x_612_, v_t_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f___redArg(lean_object* v_cmp_614_, lean_object* v_t_615_, lean_object* v_k_616_){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_box(0);
v___x_618_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_614_, v_k_616_, v___x_617_, v_t_615_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f(lean_object* v_00_u03b1_619_, lean_object* v_cmp_620_, lean_object* v_t_621_, lean_object* v_k_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_box(0);
v___x_624_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_620_, v_k_622_, v___x_623_, v_t_621_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f___redArg(lean_object* v_cmp_625_, lean_object* v_t_626_, lean_object* v_k_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_box(0);
v___x_629_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_625_, v_k_627_, v___x_628_, v_t_626_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f(lean_object* v_00_u03b1_630_, lean_object* v_cmp_631_, lean_object* v_t_632_, lean_object* v_k_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_box(0);
v___x_635_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_631_, v_k_633_, v___x_634_, v_t_632_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f___redArg(lean_object* v_cmp_636_, lean_object* v_t_637_, lean_object* v_k_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_box(0);
v___x_640_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_636_, v_k_638_, v___x_639_, v_t_637_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f(lean_object* v_00_u03b1_641_, lean_object* v_cmp_642_, lean_object* v_t_643_, lean_object* v_k_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box(0);
v___x_646_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_642_, v_k_644_, v___x_645_, v_t_643_);
return v___x_646_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_650_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2));
v___x_651_ = lean_unsigned_to_nat(14u);
v___x_652_ = lean_unsigned_to_nat(22u);
v___x_653_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1));
v___x_654_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0));
v___x_655_ = l_mkPanicMessageWithDecl(v___x_654_, v___x_653_, v___x_652_, v___x_651_, v___x_650_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg(lean_object* v_cmp_656_, lean_object* v_inst_657_, lean_object* v_t_658_, lean_object* v_k_659_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_box(0);
v___x_661_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_656_, v_k_659_, v___x_660_, v_t_658_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_663_ = l_panic___redArg(v_inst_657_, v___x_662_);
return v___x_663_;
}
else
{
lean_object* v_val_664_; 
v_val_664_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v___x_661_, 1);
return v_val_664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg___boxed(lean_object* v_cmp_665_, lean_object* v_inst_666_, lean_object* v_t_667_, lean_object* v_k_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_TreeSet_Raw_getGE_x21___redArg(v_cmp_665_, v_inst_666_, v_t_667_, v_k_668_);
lean_dec(v_inst_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21(lean_object* v_00_u03b1_670_, lean_object* v_cmp_671_, lean_object* v_inst_672_, lean_object* v_t_673_, lean_object* v_k_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_box(0);
v___x_676_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_671_, v_k_674_, v___x_675_, v_t_673_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_678_ = l_panic___redArg(v_inst_672_, v___x_677_);
return v___x_678_;
}
else
{
lean_object* v_val_679_; 
v_val_679_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v___x_676_, 1);
return v_val_679_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___boxed(lean_object* v_00_u03b1_680_, lean_object* v_cmp_681_, lean_object* v_inst_682_, lean_object* v_t_683_, lean_object* v_k_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Std_TreeSet_Raw_getGE_x21(v_00_u03b1_680_, v_cmp_681_, v_inst_682_, v_t_683_, v_k_684_);
lean_dec(v_inst_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg(lean_object* v_cmp_686_, lean_object* v_inst_687_, lean_object* v_t_688_, lean_object* v_k_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_box(0);
v___x_691_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_686_, v_k_689_, v___x_690_, v_t_688_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg___boxed(lean_object* v_cmp_695_, lean_object* v_inst_696_, lean_object* v_t_697_, lean_object* v_k_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_TreeSet_Raw_getGT_x21___redArg(v_cmp_695_, v_inst_696_, v_t_697_, v_k_698_);
lean_dec(v_inst_696_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21(lean_object* v_00_u03b1_700_, lean_object* v_cmp_701_, lean_object* v_inst_702_, lean_object* v_t_703_, lean_object* v_k_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_box(0);
v___x_706_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_701_, v_k_704_, v___x_705_, v_t_703_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___boxed(lean_object* v_00_u03b1_710_, lean_object* v_cmp_711_, lean_object* v_inst_712_, lean_object* v_t_713_, lean_object* v_k_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_TreeSet_Raw_getGT_x21(v_00_u03b1_710_, v_cmp_711_, v_inst_712_, v_t_713_, v_k_714_);
lean_dec(v_inst_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg(lean_object* v_cmp_716_, lean_object* v_inst_717_, lean_object* v_t_718_, lean_object* v_k_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_box(0);
v___x_721_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_716_, v_k_719_, v___x_720_, v_t_718_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg___boxed(lean_object* v_cmp_725_, lean_object* v_inst_726_, lean_object* v_t_727_, lean_object* v_k_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_TreeSet_Raw_getLE_x21___redArg(v_cmp_725_, v_inst_726_, v_t_727_, v_k_728_);
lean_dec(v_inst_726_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21(lean_object* v_00_u03b1_730_, lean_object* v_cmp_731_, lean_object* v_inst_732_, lean_object* v_t_733_, lean_object* v_k_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_box(0);
v___x_736_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_731_, v_k_734_, v___x_735_, v_t_733_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___boxed(lean_object* v_00_u03b1_740_, lean_object* v_cmp_741_, lean_object* v_inst_742_, lean_object* v_t_743_, lean_object* v_k_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Std_TreeSet_Raw_getLE_x21(v_00_u03b1_740_, v_cmp_741_, v_inst_742_, v_t_743_, v_k_744_);
lean_dec(v_inst_742_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg(lean_object* v_cmp_746_, lean_object* v_inst_747_, lean_object* v_t_748_, lean_object* v_k_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_box(0);
v___x_751_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_746_, v_k_749_, v___x_750_, v_t_748_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg___boxed(lean_object* v_cmp_755_, lean_object* v_inst_756_, lean_object* v_t_757_, lean_object* v_k_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_TreeSet_Raw_getLT_x21___redArg(v_cmp_755_, v_inst_756_, v_t_757_, v_k_758_);
lean_dec(v_inst_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21(lean_object* v_00_u03b1_760_, lean_object* v_cmp_761_, lean_object* v_inst_762_, lean_object* v_t_763_, lean_object* v_k_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_box(0);
v___x_766_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_761_, v_k_764_, v___x_765_, v_t_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___boxed(lean_object* v_00_u03b1_770_, lean_object* v_cmp_771_, lean_object* v_inst_772_, lean_object* v_t_773_, lean_object* v_k_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_TreeSet_Raw_getLT_x21(v_00_u03b1_770_, v_cmp_771_, v_inst_772_, v_t_773_, v_k_774_);
lean_dec(v_inst_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg(lean_object* v_cmp_776_, lean_object* v_t_777_, lean_object* v_k_778_, lean_object* v_fallback_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_box(0);
v___x_781_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_776_, v_k_778_, v___x_780_, v_t_777_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_inc(v_fallback_779_);
return v_fallback_779_;
}
else
{
lean_object* v_val_782_; 
v_val_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v___x_781_, 1);
return v_val_782_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg___boxed(lean_object* v_cmp_783_, lean_object* v_t_784_, lean_object* v_k_785_, lean_object* v_fallback_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Std_TreeSet_Raw_getGED___redArg(v_cmp_783_, v_t_784_, v_k_785_, v_fallback_786_);
lean_dec(v_fallback_786_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED(lean_object* v_00_u03b1_788_, lean_object* v_cmp_789_, lean_object* v_t_790_, lean_object* v_k_791_, lean_object* v_fallback_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_box(0);
v___x_794_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_789_, v_k_791_, v___x_793_, v_t_790_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_inc(v_fallback_792_);
return v_fallback_792_;
}
else
{
lean_object* v_val_795_; 
v_val_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_val_795_);
lean_dec_ref_known(v___x_794_, 1);
return v_val_795_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___boxed(lean_object* v_00_u03b1_796_, lean_object* v_cmp_797_, lean_object* v_t_798_, lean_object* v_k_799_, lean_object* v_fallback_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_TreeSet_Raw_getGED(v_00_u03b1_796_, v_cmp_797_, v_t_798_, v_k_799_, v_fallback_800_);
lean_dec(v_fallback_800_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg(lean_object* v_cmp_802_, lean_object* v_t_803_, lean_object* v_k_804_, lean_object* v_fallback_805_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_box(0);
v___x_807_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_802_, v_k_804_, v___x_806_, v_t_803_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_inc(v_fallback_805_);
return v_fallback_805_;
}
else
{
lean_object* v_val_808_; 
v_val_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v___x_807_, 1);
return v_val_808_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg___boxed(lean_object* v_cmp_809_, lean_object* v_t_810_, lean_object* v_k_811_, lean_object* v_fallback_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_TreeSet_Raw_getGTD___redArg(v_cmp_809_, v_t_810_, v_k_811_, v_fallback_812_);
lean_dec(v_fallback_812_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD(lean_object* v_00_u03b1_814_, lean_object* v_cmp_815_, lean_object* v_t_816_, lean_object* v_k_817_, lean_object* v_fallback_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_box(0);
v___x_820_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_815_, v_k_817_, v___x_819_, v_t_816_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_inc(v_fallback_818_);
return v_fallback_818_;
}
else
{
lean_object* v_val_821_; 
v_val_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v___x_820_, 1);
return v_val_821_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___boxed(lean_object* v_00_u03b1_822_, lean_object* v_cmp_823_, lean_object* v_t_824_, lean_object* v_k_825_, lean_object* v_fallback_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_TreeSet_Raw_getGTD(v_00_u03b1_822_, v_cmp_823_, v_t_824_, v_k_825_, v_fallback_826_);
lean_dec(v_fallback_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg(lean_object* v_cmp_828_, lean_object* v_t_829_, lean_object* v_k_830_, lean_object* v_fallback_831_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_box(0);
v___x_833_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_828_, v_k_830_, v___x_832_, v_t_829_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_inc(v_fallback_831_);
return v_fallback_831_;
}
else
{
lean_object* v_val_834_; 
v_val_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v___x_833_, 1);
return v_val_834_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg___boxed(lean_object* v_cmp_835_, lean_object* v_t_836_, lean_object* v_k_837_, lean_object* v_fallback_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_TreeSet_Raw_getLED___redArg(v_cmp_835_, v_t_836_, v_k_837_, v_fallback_838_);
lean_dec(v_fallback_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED(lean_object* v_00_u03b1_840_, lean_object* v_cmp_841_, lean_object* v_t_842_, lean_object* v_k_843_, lean_object* v_fallback_844_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_box(0);
v___x_846_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_841_, v_k_843_, v___x_845_, v_t_842_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_inc(v_fallback_844_);
return v_fallback_844_;
}
else
{
lean_object* v_val_847_; 
v_val_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v___x_846_, 1);
return v_val_847_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___boxed(lean_object* v_00_u03b1_848_, lean_object* v_cmp_849_, lean_object* v_t_850_, lean_object* v_k_851_, lean_object* v_fallback_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_TreeSet_Raw_getLED(v_00_u03b1_848_, v_cmp_849_, v_t_850_, v_k_851_, v_fallback_852_);
lean_dec(v_fallback_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg(lean_object* v_cmp_854_, lean_object* v_t_855_, lean_object* v_k_856_, lean_object* v_fallback_857_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_box(0);
v___x_859_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_854_, v_k_856_, v___x_858_, v_t_855_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_inc(v_fallback_857_);
return v_fallback_857_;
}
else
{
lean_object* v_val_860_; 
v_val_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v___x_859_, 1);
return v_val_860_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg___boxed(lean_object* v_cmp_861_, lean_object* v_t_862_, lean_object* v_k_863_, lean_object* v_fallback_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_TreeSet_Raw_getLTD___redArg(v_cmp_861_, v_t_862_, v_k_863_, v_fallback_864_);
lean_dec(v_fallback_864_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD(lean_object* v_00_u03b1_866_, lean_object* v_cmp_867_, lean_object* v_t_868_, lean_object* v_k_869_, lean_object* v_fallback_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_box(0);
v___x_872_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_867_, v_k_869_, v___x_871_, v_t_868_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_inc(v_fallback_870_);
return v_fallback_870_;
}
else
{
lean_object* v_val_873_; 
v_val_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v___x_872_, 1);
return v_val_873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___boxed(lean_object* v_00_u03b1_874_, lean_object* v_cmp_875_, lean_object* v_t_876_, lean_object* v_k_877_, lean_object* v_fallback_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_TreeSet_Raw_getLTD(v_00_u03b1_874_, v_cmp_875_, v_t_876_, v_k_877_, v_fallback_878_);
lean_dec(v_fallback_878_);
return v_res_879_;
}
}
uint8_t l_Std_TreeSet_Raw_filter___redArg___lam__0(lean_object* v_f_880_, lean_object* v_a_881_, lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = lean_apply_1(v_f_880_, v_a_881_);
v___x_884_ = lean_unbox(v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_filter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_880_ = stack[0].m_obj;
lean_object* v_a_881_ = stack[1].m_obj;
lean_object* v_x_882_ = stack[2].m_obj;
uint8_t v_res_885_;
v_res_885_ = l_Std_TreeSet_Raw_filter___redArg___lam__0(v_f_880_, v_a_881_, v_x_882_);
stack->m_num = v_res_885_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_886_, lean_object* v_a_887_, lean_object* v_x_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_Std_TreeSet_Raw_filter___redArg___lam__0(v_f_886_, v_a_887_, v_x_888_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg(lean_object* v_f_891_, lean_object* v_t_892_){
_start:
{
lean_object* v___f_893_; lean_object* v___x_894_; 
v___f_893_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_893_, 0, v_f_891_);
v___x_894_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_893_, v_t_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter(lean_object* v_00_u03b1_895_, lean_object* v_cmp_896_, lean_object* v_f_897_, lean_object* v_t_898_){
_start:
{
lean_object* v___f_899_; lean_object* v___x_900_; 
v___f_899_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_899_, 0, v_f_897_);
v___x_900_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_899_, v_t_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___boxed(lean_object* v_00_u03b1_901_, lean_object* v_cmp_902_, lean_object* v_f_903_, lean_object* v_t_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_TreeSet_Raw_filter(v_00_u03b1_901_, v_cmp_902_, v_f_903_, v_t_904_);
lean_dec_ref(v_cmp_902_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg___lam__0(lean_object* v_f_906_, lean_object* v_c_907_, lean_object* v_a_908_, lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lean_apply_2(v_f_906_, v_c_907_, v_a_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg(lean_object* v_inst_911_, lean_object* v_f_912_, lean_object* v_init_913_, lean_object* v_t_914_){
_start:
{
lean_object* v___f_915_; lean_object* v___x_916_; 
v___f_915_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_915_, 0, v_f_912_);
v___x_916_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_911_, v___f_915_, v_init_913_, v_t_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM(lean_object* v_00_u03b1_917_, lean_object* v_cmp_918_, lean_object* v_00_u03b4_919_, lean_object* v_m_920_, lean_object* v_inst_921_, lean_object* v_f_922_, lean_object* v_init_923_, lean_object* v_t_924_){
_start:
{
lean_object* v___f_925_; lean_object* v___x_926_; 
v___f_925_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_925_, 0, v_f_922_);
v___x_926_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_921_, v___f_925_, v_init_923_, v_t_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___boxed(lean_object* v_00_u03b1_927_, lean_object* v_cmp_928_, lean_object* v_00_u03b4_929_, lean_object* v_m_930_, lean_object* v_inst_931_, lean_object* v_f_932_, lean_object* v_init_933_, lean_object* v_t_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_TreeSet_Raw_foldlM(v_00_u03b1_927_, v_cmp_928_, v_00_u03b4_929_, v_m_930_, v_inst_931_, v_f_932_, v_init_933_, v_t_934_);
lean_dec_ref(v_cmp_928_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___redArg(lean_object* v_f_936_, lean_object* v_init_937_, lean_object* v_t_938_){
_start:
{
lean_object* v___f_939_; lean_object* v___x_940_; 
v___f_939_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_939_, 0, v_f_936_);
v___x_940_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_939_, v_init_937_, v_t_938_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl(lean_object* v_00_u03b1_941_, lean_object* v_cmp_942_, lean_object* v_00_u03b4_943_, lean_object* v_f_944_, lean_object* v_init_945_, lean_object* v_t_946_){
_start:
{
lean_object* v___f_947_; lean_object* v___x_948_; 
v___f_947_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_947_, 0, v_f_944_);
v___x_948_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_947_, v_init_945_, v_t_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___boxed(lean_object* v_00_u03b1_949_, lean_object* v_cmp_950_, lean_object* v_00_u03b4_951_, lean_object* v_f_952_, lean_object* v_init_953_, lean_object* v_t_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Std_TreeSet_Raw_foldl(v_00_u03b1_949_, v_cmp_950_, v_00_u03b4_951_, v_f_952_, v_init_953_, v_t_954_);
lean_dec_ref(v_cmp_950_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg___lam__0(lean_object* v_f_956_, lean_object* v_a_957_, lean_object* v_x_958_, lean_object* v_acc_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = lean_apply_2(v_f_956_, v_a_957_, v_acc_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg(lean_object* v_inst_961_, lean_object* v_f_962_, lean_object* v_init_963_, lean_object* v_t_964_){
_start:
{
lean_object* v___f_965_; lean_object* v___x_966_; 
v___f_965_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_965_, 0, v_f_962_);
v___x_966_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_961_, v___f_965_, v_init_963_, v_t_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM(lean_object* v_00_u03b1_967_, lean_object* v_cmp_968_, lean_object* v_00_u03b4_969_, lean_object* v_m_970_, lean_object* v_inst_971_, lean_object* v_f_972_, lean_object* v_init_973_, lean_object* v_t_974_){
_start:
{
lean_object* v___f_975_; lean_object* v___x_976_; 
v___f_975_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_975_, 0, v_f_972_);
v___x_976_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_971_, v___f_975_, v_init_973_, v_t_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___boxed(lean_object* v_00_u03b1_977_, lean_object* v_cmp_978_, lean_object* v_00_u03b4_979_, lean_object* v_m_980_, lean_object* v_inst_981_, lean_object* v_f_982_, lean_object* v_init_983_, lean_object* v_t_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_TreeSet_Raw_foldrM(v_00_u03b1_977_, v_cmp_978_, v_00_u03b4_979_, v_m_980_, v_inst_981_, v_f_982_, v_init_983_, v_t_984_);
lean_dec_ref(v_cmp_978_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg___lam__0(lean_object* v_f_986_, lean_object* v_x1_987_, lean_object* v_x2_988_, lean_object* v_x3_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = lean_apply_2(v_f_986_, v_x1_987_, v_x3_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg(lean_object* v_f_1010_, lean_object* v_init_1011_, lean_object* v_t_1012_){
_start:
{
lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___f_1013_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1013_, 0, v_f_1010_);
v___x_1014_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1015_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1014_, v___f_1013_, v_init_1011_, v_t_1012_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr(lean_object* v_00_u03b1_1016_, lean_object* v_cmp_1017_, lean_object* v_00_u03b4_1018_, lean_object* v_f_1019_, lean_object* v_init_1020_, lean_object* v_t_1021_){
_start:
{
lean_object* v___f_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___f_1022_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1022_, 0, v_f_1019_);
v___x_1023_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1024_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1023_, v___f_1022_, v_init_1020_, v_t_1021_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_cmp_1026_, lean_object* v_00_u03b4_1027_, lean_object* v_f_1028_, lean_object* v_init_1029_, lean_object* v_t_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Std_TreeSet_Raw_foldr(v_00_u03b1_1025_, v_cmp_1026_, v_00_u03b4_1027_, v_f_1028_, v_init_1029_, v_t_1030_);
lean_dec_ref(v_cmp_1026_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg___lam__0(lean_object* v_f_1032_, lean_object* v_cmp_1033_, lean_object* v_x_1034_, lean_object* v_a_1035_, lean_object* v_b_1036_){
_start:
{
lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1052_; 
v_fst_1037_ = lean_ctor_get(v_x_1034_, 0);
v_snd_1038_ = lean_ctor_get(v_x_1034_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1040_ = v_x_1034_;
v_isShared_1041_ = v_isSharedCheck_1052_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snd_1038_);
lean_inc(v_fst_1037_);
lean_dec(v_x_1034_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1052_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
lean_inc(v_a_1035_);
v___x_1042_ = lean_apply_1(v_f_1032_, v_a_1035_);
v___x_1043_ = lean_unbox(v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1033_, v_a_1035_, v_b_1036_, v_snd_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___x_1044_);
v___x_1046_ = v___x_1040_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_fst_1037_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1033_, v_a_1035_, v_b_1036_, v_fst_1037_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1048_);
v___x_1050_ = v___x_1040_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_snd_1038_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg(lean_object* v_cmp_1055_, lean_object* v_f_1056_, lean_object* v_t_1057_){
_start:
{
lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v_p_1060_; lean_object* v_fst_1061_; lean_object* v_snd_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v___f_1058_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1058_, 0, v_f_1056_);
lean_closure_set(v___f_1058_, 1, v_cmp_1055_);
v___x_1059_ = ((lean_object*)(l_Std_TreeSet_Raw_partition___redArg___closed__0));
v_p_1060_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1058_, v___x_1059_, v_t_1057_);
v_fst_1061_ = lean_ctor_get(v_p_1060_, 0);
v_snd_1062_ = lean_ctor_get(v_p_1060_, 1);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_p_1060_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v_p_1060_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_snd_1062_);
lean_inc(v_fst_1061_);
lean_dec(v_p_1060_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_fst_1061_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_snd_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition(lean_object* v_00_u03b1_1070_, lean_object* v_cmp_1071_, lean_object* v_f_1072_, lean_object* v_t_1073_){
_start:
{
lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v_p_1076_; lean_object* v_fst_1077_; lean_object* v_snd_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v___f_1074_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1074_, 0, v_f_1072_);
lean_closure_set(v___f_1074_, 1, v_cmp_1071_);
v___x_1075_ = ((lean_object*)(l_Std_TreeSet_Raw_partition___redArg___closed__0));
v_p_1076_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1074_, v___x_1075_, v_t_1073_);
v_fst_1077_ = lean_ctor_get(v_p_1076_, 0);
v_snd_1078_ = lean_ctor_get(v_p_1076_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_p_1076_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v_p_1076_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_snd_1078_);
lean_inc(v_fst_1077_);
lean_dec(v_p_1076_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_fst_1077_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_snd_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg___lam__0(lean_object* v_f_1086_, lean_object* v_x_1087_, lean_object* v_k_1088_, lean_object* v_v_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_apply_1(v_f_1086_, v_k_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg(lean_object* v_inst_1091_, lean_object* v_f_1092_, lean_object* v_t_1093_){
_start:
{
lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___f_1094_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1094_, 0, v_f_1092_);
v___x_1095_ = lean_box(0);
v___x_1096_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1091_, v___f_1094_, v___x_1095_, v_t_1093_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM(lean_object* v_00_u03b1_1097_, lean_object* v_cmp_1098_, lean_object* v_m_1099_, lean_object* v_inst_1100_, lean_object* v_f_1101_, lean_object* v_t_1102_){
_start:
{
lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___f_1103_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1103_, 0, v_f_1101_);
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1100_, v___f_1103_, v___x_1104_, v_t_1102_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___boxed(lean_object* v_00_u03b1_1106_, lean_object* v_cmp_1107_, lean_object* v_m_1108_, lean_object* v_inst_1109_, lean_object* v_f_1110_, lean_object* v_t_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Std_TreeSet_Raw_forM(v_00_u03b1_1106_, v_cmp_1107_, v_m_1108_, v_inst_1109_, v_f_1110_, v_t_1111_);
lean_dec_ref(v_cmp_1107_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__0(lean_object* v_f_1113_, lean_object* v_a_1114_, lean_object* v_b_1115_, lean_object* v_c_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_apply_2(v_f_1113_, v_a_1114_, v_c_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__1(lean_object* v_toPure_1118_, lean_object* v_____do__lift_1119_){
_start:
{
lean_object* v_a_1120_; lean_object* v___x_1121_; 
v_a_1120_ = lean_ctor_get(v_____do__lift_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref(v_____do__lift_1119_);
v___x_1121_ = lean_apply_2(v_toPure_1118_, lean_box(0), v_a_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg(lean_object* v_inst_1122_, lean_object* v_f_1123_, lean_object* v_init_1124_, lean_object* v_t_1125_){
_start:
{
lean_object* v_toApplicative_1126_; lean_object* v_toBind_1127_; lean_object* v_toPure_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; 
v_toApplicative_1126_ = lean_ctor_get(v_inst_1122_, 0);
v_toBind_1127_ = lean_ctor_get(v_inst_1122_, 1);
lean_inc(v_toBind_1127_);
v_toPure_1128_ = lean_ctor_get(v_toApplicative_1126_, 1);
lean_inc(v_toPure_1128_);
v___f_1129_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1129_, 0, v_f_1123_);
v___x_1130_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1122_, v___f_1129_, v_init_1124_, v_t_1125_);
v___f_1131_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1131_, 0, v_toPure_1128_);
v___x_1132_ = lean_apply_4(v_toBind_1127_, lean_box(0), lean_box(0), v___x_1130_, v___f_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn(lean_object* v_00_u03b1_1133_, lean_object* v_cmp_1134_, lean_object* v_00_u03b4_1135_, lean_object* v_m_1136_, lean_object* v_inst_1137_, lean_object* v_f_1138_, lean_object* v_init_1139_, lean_object* v_t_1140_){
_start:
{
lean_object* v_toApplicative_1141_; lean_object* v_toBind_1142_; lean_object* v_toPure_1143_; lean_object* v___f_1144_; lean_object* v___x_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; 
v_toApplicative_1141_ = lean_ctor_get(v_inst_1137_, 0);
v_toBind_1142_ = lean_ctor_get(v_inst_1137_, 1);
lean_inc(v_toBind_1142_);
v_toPure_1143_ = lean_ctor_get(v_toApplicative_1141_, 1);
lean_inc(v_toPure_1143_);
v___f_1144_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1144_, 0, v_f_1138_);
v___x_1145_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1137_, v___f_1144_, v_init_1139_, v_t_1140_);
v___f_1146_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1146_, 0, v_toPure_1143_);
v___x_1147_ = lean_apply_4(v_toBind_1142_, lean_box(0), lean_box(0), v___x_1145_, v___f_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___boxed(lean_object* v_00_u03b1_1148_, lean_object* v_cmp_1149_, lean_object* v_00_u03b4_1150_, lean_object* v_m_1151_, lean_object* v_inst_1152_, lean_object* v_f_1153_, lean_object* v_init_1154_, lean_object* v_t_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_TreeSet_Raw_forIn(v_00_u03b1_1148_, v_cmp_1149_, v_00_u03b4_1150_, v_m_1151_, v_inst_1152_, v_f_1153_, v_init_1154_, v_t_1155_);
lean_dec_ref(v_cmp_1149_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1(lean_object* v_inst_1157_, lean_object* v_t_1158_, lean_object* v_f_1159_){
_start:
{
lean_object* v___f_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___f_1160_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1160_, 0, v_f_1159_);
v___x_1161_ = lean_box(0);
v___x_1162_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1157_, v___f_1160_, v___x_1161_, v_t_1158_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_1163_){
_start:
{
lean_object* v___f_1164_; 
v___f_1164_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1164_, 0, v_inst_1163_);
return v___f_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_1165_, lean_object* v_cmp_1166_, lean_object* v_m_1167_, lean_object* v_inst_1168_){
_start:
{
lean_object* v___f_1169_; 
v___f_1169_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1169_, 0, v_inst_1168_);
return v___f_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___boxed(lean_object* v_00_u03b1_1170_, lean_object* v_cmp_1171_, lean_object* v_m_1172_, lean_object* v_inst_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Std_TreeSet_Raw_instForMOfMonad(v_00_u03b1_1170_, v_cmp_1171_, v_m_1172_, v_inst_1173_);
lean_dec_ref(v_cmp_1171_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2(lean_object* v_inst_1175_, lean_object* v_00_u03b2_1176_, lean_object* v_t_1177_, lean_object* v_init_1178_, lean_object* v_f_1179_){
_start:
{
lean_object* v_toApplicative_1180_; lean_object* v_toBind_1181_; lean_object* v_toPure_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; 
v_toApplicative_1180_ = lean_ctor_get(v_inst_1175_, 0);
v_toBind_1181_ = lean_ctor_get(v_inst_1175_, 1);
lean_inc(v_toBind_1181_);
v_toPure_1182_ = lean_ctor_get(v_toApplicative_1180_, 1);
lean_inc(v_toPure_1182_);
v___f_1183_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1183_, 0, v_f_1179_);
v___x_1184_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1175_, v___f_1183_, v_init_1178_, v_t_1177_);
v___f_1185_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1185_, 0, v_toPure_1182_);
v___x_1186_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v___x_1184_, v___f_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_1187_){
_start:
{
lean_object* v___f_1188_; 
v___f_1188_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1188_, 0, v_inst_1187_);
return v___f_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_1189_, lean_object* v_cmp_1190_, lean_object* v_m_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v___f_1193_; 
v___f_1193_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1193_, 0, v_inst_1192_);
return v___f_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_cmp_1195_, lean_object* v_m_1196_, lean_object* v_inst_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Std_TreeSet_Raw_instForInOfMonad(v_00_u03b1_1194_, v_cmp_1195_, v_m_1196_, v_inst_1197_);
lean_dec_ref(v_cmp_1195_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0(lean_object* v_p_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v_a_1202_, lean_object* v_b_1203_, lean_object* v_acc_1204_){
_start:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_apply_1(v_p_1199_, v_a_1202_);
v___x_1206_ = lean_unbox(v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1200_);
return v___x_1207_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref(v___x_1200_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1205_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1201_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1211_, lean_object* v___x_1212_, lean_object* v___x_1213_, lean_object* v_a_1214_, lean_object* v_b_1215_, lean_object* v_acc_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_TreeSet_Raw_any___redArg___lam__0(v_p_1211_, v___x_1212_, v___x_1213_, v_a_1214_, v_b_1215_, v_acc_1216_);
lean_dec_ref(v_acc_1216_);
return v_res_1217_;
}
}
uint8_t l_Std_TreeSet_Raw_any___redArg(lean_object* v_t_1221_, lean_object* v_p_1222_){
_start:
{
lean_object* v___y_1224_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; lean_object* v_a_1234_; 
v___x_1229_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1230_ = lean_box(0);
v___x_1231_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1232_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1232_, 0, v_p_1222_);
lean_closure_set(v___f_1232_, 1, v___x_1231_);
lean_closure_set(v___f_1232_, 2, v___x_1230_);
v___x_1233_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1229_, v___f_1232_, v___x_1231_, v_t_1221_);
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___y_1224_ = v_a_1234_;
goto v___jp_1223_;
v___jp_1223_:
{
lean_object* v_fst_1225_; 
v_fst_1225_ = lean_ctor_get(v___y_1224_, 0);
lean_inc(v_fst_1225_);
lean_dec_ref(v___y_1224_);
if (lean_obj_tag(v_fst_1225_) == 0)
{
uint8_t v___x_1226_; 
v___x_1226_ = 0;
return v___x_1226_;
}
else
{
lean_object* v_val_1227_; uint8_t v___x_1228_; 
v_val_1227_ = lean_ctor_get(v_fst_1225_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v_fst_1225_, 1);
v___x_1228_ = lean_unbox(v_val_1227_);
lean_dec(v_val_1227_);
return v___x_1228_;
}
}
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1221_ = stack[0].m_obj;
lean_object* v_p_1222_ = stack[1].m_obj;
uint8_t v_res_1235_;
v_res_1235_ = l_Std_TreeSet_Raw_any___redArg(v_t_1221_, v_p_1222_);
stack->m_num = v_res_1235_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___boxed(lean_object* v_t_1236_, lean_object* v_p_1237_){
_start:
{
uint8_t v_res_1238_; lean_object* v_r_1239_; 
v_res_1238_ = l_Std_TreeSet_Raw_any___redArg(v_t_1236_, v_p_1237_);
v_r_1239_ = lean_box(v_res_1238_);
return v_r_1239_;
}
}
uint8_t l_Std_TreeSet_Raw_any(lean_object* v_00_u03b1_1240_, lean_object* v_cmp_1241_, lean_object* v_t_1242_, lean_object* v_p_1243_){
_start:
{
lean_object* v___y_1245_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___f_1253_; lean_object* v___x_1254_; lean_object* v_a_1255_; 
v___x_1250_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1251_ = lean_box(0);
v___x_1252_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1253_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_any___redArg___lam__0___boxed), 6, 3);
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
LEAN_EXPORT void l_Std_TreeSet_Raw_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1241_ = stack[1].m_obj;
lean_object* v_t_1242_ = stack[2].m_obj;
lean_object* v_p_1243_ = stack[3].m_obj;
uint8_t v_res_1256_;
v_res_1256_ = l_Std_TreeSet_Raw_any(lean_box(0), v_cmp_1241_, v_t_1242_, v_p_1243_);
stack->m_num = v_res_1256_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___boxed(lean_object* v_00_u03b1_1257_, lean_object* v_cmp_1258_, lean_object* v_t_1259_, lean_object* v_p_1260_){
_start:
{
uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_res_1261_ = l_Std_TreeSet_Raw_any(v_00_u03b1_1257_, v_cmp_1258_, v_t_1259_, v_p_1260_);
lean_dec_ref(v_cmp_1258_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0(lean_object* v_p_1263_, lean_object* v___x_1264_, lean_object* v___x_1265_, lean_object* v_a_1266_, lean_object* v_b_1267_, lean_object* v_acc_1268_){
_start:
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = lean_apply_1(v_p_1263_, v_a_1266_);
v___x_1270_ = lean_unbox(v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec_ref(v___x_1265_);
v___x_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v___x_1264_);
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
return v___x_1273_;
}
else
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1265_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1275_, lean_object* v___x_1276_, lean_object* v___x_1277_, lean_object* v_a_1278_, lean_object* v_b_1279_, lean_object* v_acc_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Std_TreeSet_Raw_all___redArg___lam__0(v_p_1275_, v___x_1276_, v___x_1277_, v_a_1278_, v_b_1279_, v_acc_1280_);
lean_dec_ref(v_acc_1280_);
return v_res_1281_;
}
}
uint8_t l_Std_TreeSet_Raw_all___redArg(lean_object* v_t_1282_, lean_object* v_p_1283_){
_start:
{
lean_object* v___y_1285_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___f_1293_; lean_object* v___x_1294_; lean_object* v_a_1295_; 
v___x_1290_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1291_ = lean_box(0);
v___x_1292_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1293_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1293_, 0, v_p_1283_);
lean_closure_set(v___f_1293_, 1, v___x_1291_);
lean_closure_set(v___f_1293_, 2, v___x_1292_);
v___x_1294_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1290_, v___f_1293_, v___x_1292_, v_t_1282_);
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___y_1285_ = v_a_1295_;
goto v___jp_1284_;
v___jp_1284_:
{
lean_object* v_fst_1286_; 
v_fst_1286_ = lean_ctor_get(v___y_1285_, 0);
lean_inc(v_fst_1286_);
lean_dec_ref(v___y_1285_);
if (lean_obj_tag(v_fst_1286_) == 0)
{
uint8_t v___x_1287_; 
v___x_1287_ = 1;
return v___x_1287_;
}
else
{
lean_object* v_val_1288_; uint8_t v___x_1289_; 
v_val_1288_ = lean_ctor_get(v_fst_1286_, 0);
lean_inc(v_val_1288_);
lean_dec_ref_known(v_fst_1286_, 1);
v___x_1289_ = lean_unbox(v_val_1288_);
lean_dec(v_val_1288_);
return v___x_1289_;
}
}
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1282_ = stack[0].m_obj;
lean_object* v_p_1283_ = stack[1].m_obj;
uint8_t v_res_1296_;
v_res_1296_ = l_Std_TreeSet_Raw_all___redArg(v_t_1282_, v_p_1283_);
stack->m_num = v_res_1296_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___boxed(lean_object* v_t_1297_, lean_object* v_p_1298_){
_start:
{
uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_res_1299_ = l_Std_TreeSet_Raw_all___redArg(v_t_1297_, v_p_1298_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
uint8_t l_Std_TreeSet_Raw_all(lean_object* v_00_u03b1_1301_, lean_object* v_cmp_1302_, lean_object* v_t_1303_, lean_object* v_p_1304_){
_start:
{
lean_object* v___y_1306_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___f_1314_; lean_object* v___x_1315_; lean_object* v_a_1316_; 
v___x_1311_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1312_ = lean_box(0);
v___x_1313_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1314_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1314_, 0, v_p_1304_);
lean_closure_set(v___f_1314_, 1, v___x_1312_);
lean_closure_set(v___f_1314_, 2, v___x_1313_);
v___x_1315_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1311_, v___f_1314_, v___x_1313_, v_t_1303_);
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___y_1306_ = v_a_1316_;
goto v___jp_1305_;
v___jp_1305_:
{
lean_object* v_fst_1307_; 
v_fst_1307_ = lean_ctor_get(v___y_1306_, 0);
lean_inc(v_fst_1307_);
lean_dec_ref(v___y_1306_);
if (lean_obj_tag(v_fst_1307_) == 0)
{
uint8_t v___x_1308_; 
v___x_1308_ = 1;
return v___x_1308_;
}
else
{
lean_object* v_val_1309_; uint8_t v___x_1310_; 
v_val_1309_ = lean_ctor_get(v_fst_1307_, 0);
lean_inc(v_val_1309_);
lean_dec_ref_known(v_fst_1307_, 1);
v___x_1310_ = lean_unbox(v_val_1309_);
lean_dec(v_val_1309_);
return v___x_1310_;
}
}
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1302_ = stack[1].m_obj;
lean_object* v_t_1303_ = stack[2].m_obj;
lean_object* v_p_1304_ = stack[3].m_obj;
uint8_t v_res_1317_;
v_res_1317_ = l_Std_TreeSet_Raw_all(lean_box(0), v_cmp_1302_, v_t_1303_, v_p_1304_);
stack->m_num = v_res_1317_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_cmp_1319_, lean_object* v_t_1320_, lean_object* v_p_1321_){
_start:
{
uint8_t v_res_1322_; lean_object* v_r_1323_; 
v_res_1322_ = l_Std_TreeSet_Raw_all(v_00_u03b1_1318_, v_cmp_1319_, v_t_1320_, v_p_1321_);
lean_dec_ref(v_cmp_1319_);
v_r_1323_ = lean_box(v_res_1322_);
return v_r_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg___lam__0(lean_object* v_x1_1324_, lean_object* v_x2_1325_, lean_object* v_x3_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1327_, 0, v_x1_1324_);
lean_ctor_set(v___x_1327_, 1, v_x3_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg(lean_object* v_t_1329_){
_start:
{
lean_object* v___f_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___f_1330_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___x_1331_ = lean_box(0);
v___x_1332_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1333_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1332_, v___f_1330_, v___x_1331_, v_t_1329_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList(lean_object* v_00_u03b1_1334_, lean_object* v_cmp_1335_, lean_object* v_t_1336_){
_start:
{
lean_object* v___f_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___f_1337_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___x_1338_ = lean_box(0);
v___x_1339_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1340_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1339_, v___f_1337_, v___x_1338_, v_t_1336_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_cmp_1342_, lean_object* v_t_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Std_TreeSet_Raw_toList(v_00_u03b1_1341_, v_cmp_1342_, v_t_1343_);
lean_dec_ref(v_cmp_1342_);
return v_res_1344_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__25, &l_Std_TreeSet_Raw___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw___auto__1___closed__25);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg___lam__0(lean_object* v_cmp_1346_, lean_object* v_a_1347_, lean_object* v_x_1348_, lean_object* v___y_1349_){
_start:
{
uint8_t v___x_1350_; 
lean_inc(v___y_1349_);
lean_inc(v_a_1347_);
lean_inc_ref(v_cmp_1346_);
v___x_1350_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1346_, v_a_1347_, v___y_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = lean_box(0);
v___x_1352_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1346_, v_a_1347_, v___x_1351_, v___y_1349_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; 
lean_dec(v_a_1347_);
lean_dec_ref(v_cmp_1346_);
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___y_1349_);
return v___x_1354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg(lean_object* v_l_1355_, lean_object* v_cmp_1356_){
_start:
{
lean_object* v___f_1357_; lean_object* v___x_1358_; lean_object* v_r_1359_; lean_object* v___x_1360_; 
v___f_1357_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1357_, 0, v_cmp_1356_);
v___x_1358_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1359_ = lean_box(1);
v___x_1360_ = l_List_forIn_x27_loop___redArg(v___x_1358_, v___f_1357_, v_l_1355_, v_r_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg___boxed(lean_object* v_l_1361_, lean_object* v_cmp_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_TreeSet_Raw_ofList___redArg(v_l_1361_, v_cmp_1362_);
lean_dec(v_l_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList(lean_object* v_00_u03b1_1364_, lean_object* v_l_1365_, lean_object* v_cmp_1366_){
_start:
{
lean_object* v___f_1367_; lean_object* v___x_1368_; lean_object* v_r_1369_; lean_object* v___x_1370_; 
v___f_1367_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1367_, 0, v_cmp_1366_);
v___x_1368_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1369_ = lean_box(1);
v___x_1370_ = l_List_forIn_x27_loop___redArg(v___x_1368_, v___f_1367_, v_l_1365_, v_r_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___boxed(lean_object* v_00_u03b1_1371_, lean_object* v_l_1372_, lean_object* v_cmp_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Std_TreeSet_Raw_ofList(v_00_u03b1_1371_, v_l_1372_, v_cmp_1373_);
lean_dec(v_l_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg___lam__0(lean_object* v_c_1375_, lean_object* v_a_1376_, lean_object* v_x_1377_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_array_push(v_c_1375_, v_a_1376_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg(lean_object* v_t_1382_){
_start:
{
lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___f_1383_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__0));
v___x_1384_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__1));
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1383_, v___x_1384_, v_t_1382_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray(lean_object* v_00_u03b1_1386_, lean_object* v_cmp_1387_, lean_object* v_t_1388_){
_start:
{
lean_object* v___f_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___f_1389_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__0));
v___x_1390_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__1));
v___x_1391_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1389_, v___x_1390_, v_t_1388_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___boxed(lean_object* v_00_u03b1_1392_, lean_object* v_cmp_1393_, lean_object* v_t_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Std_TreeSet_Raw_toArray(v_00_u03b1_1392_, v_cmp_1393_, v_t_1394_);
lean_dec_ref(v_cmp_1393_);
return v_res_1395_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__25, &l_Std_TreeSet_Raw___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw___auto__1___closed__25);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray___redArg(lean_object* v_a_1397_, lean_object* v_cmp_1398_){
_start:
{
lean_object* v___f_1399_; lean_object* v___x_1400_; lean_object* v_r_1401_; size_t v_sz_1402_; size_t v___x_1403_; lean_object* v___x_1404_; 
v___f_1399_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1399_, 0, v_cmp_1398_);
v___x_1400_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1401_ = lean_box(1);
v_sz_1402_ = lean_array_size(v_a_1397_);
v___x_1403_ = ((size_t)0ULL);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1400_, v_a_1397_, v___f_1399_, v_sz_1402_, v___x_1403_, v_r_1401_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray(lean_object* v_00_u03b1_1405_, lean_object* v_a_1406_, lean_object* v_cmp_1407_){
_start:
{
lean_object* v___f_1408_; lean_object* v___x_1409_; lean_object* v_r_1410_; size_t v_sz_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v___f_1408_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1408_, 0, v_cmp_1407_);
v___x_1409_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1410_ = lean_box(1);
v_sz_1411_ = lean_array_size(v_a_1406_);
v___x_1412_ = ((size_t)0ULL);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1409_, v_a_1406_, v___f_1408_, v_sz_1411_, v___x_1412_, v_r_1410_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0(lean_object* v_b_u2082_1416_, lean_object* v_x_1417_){
_start:
{
if (lean_obj_tag(v_x_1417_) == 0)
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_b_u2082_1416_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; 
v___x_1419_ = ((lean_object*)(l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0));
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1420_, lean_object* v_x_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Std_TreeSet_Raw_merge___redArg___lam__0(v_b_u2082_1420_, v_x_1421_);
lean_dec(v_x_1421_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__1(lean_object* v_cmp_1423_, lean_object* v_t_1424_, lean_object* v_a_1425_, lean_object* v_b_u2082_1426_){
_start:
{
lean_object* v___f_1427_; lean_object* v___x_1428_; 
v___f_1427_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1427_, 0, v_b_u2082_1426_);
v___x_1428_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_1423_, v_a_1425_, v___f_1427_, v_t_1424_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg(lean_object* v_cmp_1429_, lean_object* v_t_u2081_1430_, lean_object* v_t_u2082_1431_){
_start:
{
lean_object* v___f_1432_; lean_object* v___x_1433_; 
v___f_1432_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1432_, 0, v_cmp_1429_);
v___x_1433_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1432_, v_t_u2081_1430_, v_t_u2082_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge(lean_object* v_00_u03b1_1434_, lean_object* v_cmp_1435_, lean_object* v_t_u2081_1436_, lean_object* v_t_u2082_1437_){
_start:
{
lean_object* v___f_1438_; lean_object* v___x_1439_; 
v___f_1438_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1438_, 0, v_cmp_1435_);
v___x_1439_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1438_, v_t_u2081_1436_, v_t_u2082_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_1440_, lean_object* v_a_1441_, lean_object* v_____s_1442_){
_start:
{
uint8_t v___x_1443_; 
lean_inc(v_____s_1442_);
lean_inc(v_a_1441_);
lean_inc_ref(v_cmp_1440_);
v___x_1443_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1440_, v_a_1441_, v_____s_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1440_, v_a_1441_, v___x_1444_, v_____s_1442_);
v___x_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; 
lean_dec(v_a_1441_);
lean_dec_ref(v_cmp_1440_);
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_____s_1442_);
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg(lean_object* v_cmp_1448_, lean_object* v_inst_1449_, lean_object* v_t_1450_, lean_object* v_l_1451_){
_start:
{
lean_object* v___f_1452_; lean_object* v___x_1453_; 
v___f_1452_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1452_, 0, v_cmp_1448_);
v___x_1453_ = lean_apply_4(v_inst_1449_, lean_box(0), v_l_1451_, v_t_1450_, v___f_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany(lean_object* v_00_u03b1_1454_, lean_object* v_cmp_1455_, lean_object* v_00_u03c1_1456_, lean_object* v_inst_1457_, lean_object* v_t_1458_, lean_object* v_l_1459_){
_start:
{
lean_object* v___f_1460_; lean_object* v___x_1461_; 
v___f_1460_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1460_, 0, v_cmp_1455_);
v___x_1461_ = lean_apply_4(v_inst_1457_, lean_box(0), v_l_1459_, v_t_1458_, v___f_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union___redArg(lean_object* v_cmp_1462_, lean_object* v_t_u2081_1463_, lean_object* v_t_u2082_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_1462_, v_t_u2081_1463_, v_t_u2082_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union(lean_object* v_00_u03b1_1466_, lean_object* v_cmp_1467_, lean_object* v_t_u2081_1468_, lean_object* v_t_u2082_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_1467_, v_t_u2081_1468_, v_t_u2082_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion___redArg(lean_object* v_cmp_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_union), 4, 2);
lean_closure_set(v___x_1472_, 0, lean_box(0));
lean_closure_set(v___x_1472_, 1, v_cmp_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion(lean_object* v_00_u03b1_1473_, lean_object* v_cmp_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_union), 4, 2);
lean_closure_set(v___x_1475_, 0, lean_box(0));
lean_closure_set(v___x_1475_, 1, v_cmp_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter___redArg(lean_object* v_cmp_1476_, lean_object* v_t_u2081_1477_, lean_object* v_t_u2082_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_1476_, v_t_u2081_1477_, v_t_u2082_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter(lean_object* v_00_u03b1_1480_, lean_object* v_cmp_1481_, lean_object* v_t_u2081_1482_, lean_object* v_t_u2082_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_1481_, v_t_u2081_1482_, v_t_u2082_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter___redArg(lean_object* v_cmp_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_inter), 4, 2);
lean_closure_set(v___x_1486_, 0, lean_box(0));
lean_closure_set(v___x_1486_, 1, v_cmp_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter(lean_object* v_00_u03b1_1487_, lean_object* v_cmp_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_inter), 4, 2);
lean_closure_set(v___x_1489_, 0, lean_box(0));
lean_closure_set(v___x_1489_, 1, v_cmp_1488_);
return v___x_1489_;
}
}
uint8_t l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
if (lean_obj_tag(v_x_1490_) == 0)
{
if (lean_obj_tag(v_x_1491_) == 0)
{
uint8_t v___x_1492_; 
v___x_1492_ = 1;
return v___x_1492_;
}
else
{
uint8_t v___x_1493_; 
v___x_1493_ = 0;
return v___x_1493_;
}
}
else
{
if (lean_obj_tag(v_x_1491_) == 0)
{
uint8_t v___x_1494_; 
v___x_1494_ = 0;
return v___x_1494_;
}
else
{
uint8_t v___x_1495_; 
v___x_1495_ = 1;
return v___x_1495_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1490_ = stack[0].m_obj;
lean_object* v_x_1491_ = stack[1].m_obj;
uint8_t v_res_1496_;
v_res_1496_ = l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v_x_1490_, v_x_1491_);
stack->m_num = v_res_1496_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1497_, lean_object* v_x_1498_){
_start:
{
uint8_t v_res_1499_; lean_object* v_r_1500_; 
v_res_1499_ = l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v_x_1497_, v_x_1498_);
lean_dec(v_x_1498_);
lean_dec(v_x_1497_);
v_r_1500_ = lean_box(v_res_1499_);
return v_r_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_cmp_1501_, lean_object* v_t_1502_, lean_object* v_k_1503_){
_start:
{
if (lean_obj_tag(v_t_1502_) == 0)
{
lean_object* v_k_1504_; lean_object* v_v_1505_; lean_object* v_l_1506_; lean_object* v_r_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_k_1504_ = lean_ctor_get(v_t_1502_, 1);
lean_inc(v_k_1504_);
v_v_1505_ = lean_ctor_get(v_t_1502_, 2);
lean_inc(v_v_1505_);
v_l_1506_ = lean_ctor_get(v_t_1502_, 3);
lean_inc(v_l_1506_);
v_r_1507_ = lean_ctor_get(v_t_1502_, 4);
lean_inc(v_r_1507_);
lean_dec_ref_known(v_t_1502_, 5);
lean_inc_ref(v_cmp_1501_);
lean_inc(v_k_1503_);
v___x_1508_ = lean_apply_2(v_cmp_1501_, v_k_1503_, v_k_1504_);
v___x_1509_ = lean_unbox(v___x_1508_);
switch(v___x_1509_)
{
case 0:
{
lean_dec(v_r_1507_);
lean_dec(v_v_1505_);
v_t_1502_ = v_l_1506_;
goto _start;
}
case 1:
{
lean_object* v___x_1511_; 
lean_dec(v_r_1507_);
lean_dec(v_l_1506_);
lean_dec(v_k_1503_);
lean_dec_ref(v_cmp_1501_);
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_v_1505_);
return v___x_1511_;
}
default: 
{
lean_dec(v_l_1506_);
lean_dec(v_v_1505_);
v_t_1502_ = v_r_1507_;
goto _start;
}
}
}
else
{
lean_object* v___x_1513_; 
lean_dec(v_k_1503_);
lean_dec_ref(v_cmp_1501_);
v___x_1513_ = lean_box(0);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v_cmp_1516_, lean_object* v_t_u2082_1517_, lean_object* v_init_1518_, lean_object* v_x_1519_){
_start:
{
lean_object* v___x_1520_; uint8_t v___y_1522_; lean_object* v___x_1527_; uint8_t v___y_1529_; uint8_t v___x_1547_; 
v___x_1520_ = lean_box(0);
v___x_1527_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___x_1547_ = lean_nat_dec_eq(v___y_1514_, v___y_1515_);
if (v___x_1547_ == 0)
{
uint8_t v___x_1548_; 
v___x_1548_ = 1;
v___y_1529_ = v___x_1548_;
goto v___jp_1528_;
}
else
{
uint8_t v___x_1549_; 
v___x_1549_ = 0;
v___y_1529_ = v___x_1549_;
goto v___jp_1528_;
}
v___jp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_box(v___y_1522_);
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v___x_1520_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
v___jp_1528_:
{
if (lean_obj_tag(v_x_1519_) == 0)
{
lean_object* v_k_1530_; lean_object* v_v_1531_; lean_object* v_l_1532_; lean_object* v_r_1533_; lean_object* v___x_1534_; 
v_k_1530_ = lean_ctor_get(v_x_1519_, 1);
lean_inc(v_k_1530_);
v_v_1531_ = lean_ctor_get(v_x_1519_, 2);
lean_inc(v_v_1531_);
v_l_1532_ = lean_ctor_get(v_x_1519_, 3);
lean_inc(v_l_1532_);
v_r_1533_ = lean_ctor_get(v_x_1519_, 4);
lean_inc(v_r_1533_);
lean_dec_ref_known(v_x_1519_, 5);
lean_inc(v_t_u2082_1517_);
lean_inc_ref(v_cmp_1516_);
v___x_1534_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1514_, v___y_1515_, v_cmp_1516_, v_t_u2082_1517_, v_init_1518_, v_l_1532_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_dec(v_r_1533_);
lean_dec(v_v_1531_);
lean_dec(v_k_1530_);
lean_dec(v_t_u2082_1517_);
lean_dec_ref(v_cmp_1516_);
return v___x_1534_;
}
else
{
lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1544_; 
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v___x_1534_, 0);
lean_dec(v_unused_1545_);
v___x_1536_ = v___x_1534_;
v_isShared_1537_ = v_isSharedCheck_1544_;
goto v_resetjp_1535_;
}
else
{
lean_dec(v___x_1534_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1544_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
lean_inc(v_t_u2082_1517_);
lean_inc_ref(v_cmp_1516_);
v___x_1538_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1516_, v_t_u2082_1517_, v_k_1530_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v_v_1531_);
v___x_1540_ = v___x_1536_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_v_1531_);
v___x_1540_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
uint8_t v___x_1541_; 
v___x_1541_ = l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v___x_1538_, v___x_1540_);
lean_dec_ref(v___x_1540_);
lean_dec(v___x_1538_);
if (v___x_1541_ == 0)
{
lean_dec(v_r_1533_);
lean_dec(v_t_u2082_1517_);
lean_dec_ref(v_cmp_1516_);
v___y_1522_ = v___y_1529_;
goto v___jp_1521_;
}
else
{
if (v___y_1529_ == 0)
{
v_init_1518_ = v___x_1527_;
v_x_1519_ = v_r_1533_;
goto _start;
}
else
{
lean_dec(v_r_1533_);
lean_dec(v_t_u2082_1517_);
lean_dec_ref(v_cmp_1516_);
v___y_1522_ = v___y_1529_;
goto v___jp_1521_;
}
}
}
}
}
}
else
{
lean_object* v___x_1546_; 
lean_dec(v_t_u2082_1517_);
lean_dec_ref(v_cmp_1516_);
v___x_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1546_, 0, v_init_1518_);
return v___x_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v_cmp_1552_, lean_object* v_t_u2082_1553_, lean_object* v_init_1554_, lean_object* v_x_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1550_, v___y_1551_, v_cmp_1552_, v_t_u2082_1553_, v_init_1554_, v_x_1555_);
lean_dec(v___y_1551_);
lean_dec(v___y_1550_);
return v_res_1556_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_1557_, lean_object* v_t_u2081_1558_, lean_object* v_t_u2082_1559_){
_start:
{
lean_object* v___y_1561_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1574_; 
if (lean_obj_tag(v_t_u2081_1558_) == 0)
{
lean_object* v_size_1577_; 
v_size_1577_ = lean_ctor_get(v_t_u2081_1558_, 0);
lean_inc(v_size_1577_);
v___y_1574_ = v_size_1577_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_unsigned_to_nat(0u);
v___y_1574_ = v___x_1578_;
goto v___jp_1573_;
}
v___jp_1560_:
{
lean_object* v_fst_1562_; 
v_fst_1562_ = lean_ctor_get(v___y_1561_, 0);
lean_inc(v_fst_1562_);
lean_dec_ref(v___y_1561_);
if (lean_obj_tag(v_fst_1562_) == 0)
{
uint8_t v___x_1563_; 
v___x_1563_ = 1;
return v___x_1563_;
}
else
{
lean_object* v_val_1564_; uint8_t v___x_1565_; 
v_val_1564_ = lean_ctor_get(v_fst_1562_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v_fst_1562_, 1);
v___x_1565_ = lean_unbox(v_val_1564_);
lean_dec(v_val_1564_);
return v___x_1565_;
}
}
v___jp_1566_:
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_nat_dec_eq(v___y_1567_, v___y_1568_);
if (v___x_1569_ == 0)
{
lean_dec(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec(v_t_u2082_1559_);
lean_dec(v_t_u2081_1558_);
lean_dec_ref(v_cmp_1557_);
return v___x_1569_;
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v_a_1572_; 
v___x_1570_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___x_1571_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1567_, v___y_1568_, v_cmp_1557_, v_t_u2082_1559_, v___x_1570_, v_t_u2081_1558_);
lean_dec(v___y_1568_);
lean_dec(v___y_1567_);
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v___x_1571_);
v___y_1561_ = v_a_1572_;
goto v___jp_1560_;
}
}
v___jp_1573_:
{
if (lean_obj_tag(v_t_u2082_1559_) == 0)
{
lean_object* v_size_1575_; 
v_size_1575_ = lean_ctor_get(v_t_u2082_1559_, 0);
lean_inc(v_size_1575_);
v___y_1567_ = v___y_1574_;
v___y_1568_ = v_size_1575_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_unsigned_to_nat(0u);
v___y_1567_ = v___y_1574_;
v___y_1568_ = v___x_1576_;
goto v___jp_1566_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1557_ = stack[0].m_obj;
lean_object* v_t_u2081_1558_ = stack[1].m_obj;
lean_object* v_t_u2082_1559_ = stack[2].m_obj;
uint8_t v_res_1579_;
v_res_1579_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1557_, v_t_u2081_1558_, v_t_u2082_1559_);
stack->m_num = v_res_1579_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_1580_, lean_object* v_t_u2081_1581_, lean_object* v_t_u2082_1582_){
_start:
{
uint8_t v_res_1583_; lean_object* v_r_1584_; 
v_res_1583_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1580_, v_t_u2081_1581_, v_t_u2082_1582_);
v_r_1584_ = lean_box(v_res_1583_);
return v_r_1584_;
}
}
uint8_t l_Std_TreeSet_Raw_beq___redArg(lean_object* v_cmp_1585_, lean_object* v_t_u2081_1586_, lean_object* v_t_u2082_1587_){
_start:
{
uint8_t v___x_1588_; 
v___x_1588_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1585_, v_t_u2081_1586_, v_t_u2082_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1585_ = stack[0].m_obj;
lean_object* v_t_u2081_1586_ = stack[1].m_obj;
lean_object* v_t_u2082_1587_ = stack[2].m_obj;
uint8_t v_res_1589_;
v_res_1589_ = l_Std_TreeSet_Raw_beq___redArg(v_cmp_1585_, v_t_u2081_1586_, v_t_u2082_1587_);
stack->m_num = v_res_1589_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___redArg___boxed(lean_object* v_cmp_1590_, lean_object* v_t_u2081_1591_, lean_object* v_t_u2082_1592_){
_start:
{
uint8_t v_res_1593_; lean_object* v_r_1594_; 
v_res_1593_ = l_Std_TreeSet_Raw_beq___redArg(v_cmp_1590_, v_t_u2081_1591_, v_t_u2082_1592_);
v_r_1594_ = lean_box(v_res_1593_);
return v_r_1594_;
}
}
uint8_t l_Std_TreeSet_Raw_beq(lean_object* v_00_u03b1_1595_, lean_object* v_cmp_1596_, lean_object* v_t_u2081_1597_, lean_object* v_t_u2082_1598_){
_start:
{
uint8_t v___x_1599_; 
v___x_1599_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1596_, v_t_u2081_1597_, v_t_u2082_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1596_ = stack[1].m_obj;
lean_object* v_t_u2081_1597_ = stack[2].m_obj;
lean_object* v_t_u2082_1598_ = stack[3].m_obj;
uint8_t v_res_1600_;
v_res_1600_ = l_Std_TreeSet_Raw_beq(lean_box(0), v_cmp_1596_, v_t_u2081_1597_, v_t_u2082_1598_);
stack->m_num = v_res_1600_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___boxed(lean_object* v_00_u03b1_1601_, lean_object* v_cmp_1602_, lean_object* v_t_u2081_1603_, lean_object* v_t_u2082_1604_){
_start:
{
uint8_t v_res_1605_; lean_object* v_r_1606_; 
v_res_1605_ = l_Std_TreeSet_Raw_beq(v_00_u03b1_1601_, v_cmp_1602_, v_t_u2081_1603_, v_t_u2082_1604_);
v_r_1606_ = lean_box(v_res_1605_);
return v_r_1606_;
}
}
uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(lean_object* v_cmp_1607_, lean_object* v_t_u2081_1608_, lean_object* v_t_u2082_1609_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1607_, v_t_u2081_1608_, v_t_u2082_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1607_ = stack[0].m_obj;
lean_object* v_t_u2081_1608_ = stack[1].m_obj;
lean_object* v_t_u2082_1609_ = stack[2].m_obj;
uint8_t v_res_1611_;
v_res_1611_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(v_cmp_1607_, v_t_u2081_1608_, v_t_u2082_1609_);
stack->m_num = v_res_1611_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg___boxed(lean_object* v_cmp_1612_, lean_object* v_t_u2081_1613_, lean_object* v_t_u2082_1614_){
_start:
{
uint8_t v_res_1615_; lean_object* v_r_1616_; 
v_res_1615_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(v_cmp_1612_, v_t_u2081_1613_, v_t_u2082_1614_);
v_r_1616_ = lean_box(v_res_1615_);
return v_r_1616_;
}
}
uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(lean_object* v_00_u03b1_1617_, lean_object* v_cmp_1618_, lean_object* v_t_u2081_1619_, lean_object* v_t_u2082_1620_){
_start:
{
uint8_t v___x_1621_; 
v___x_1621_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1618_, v_t_u2081_1619_, v_t_u2082_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT void l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1618_ = stack[1].m_obj;
lean_object* v_t_u2081_1619_ = stack[2].m_obj;
lean_object* v_t_u2082_1620_ = stack[3].m_obj;
uint8_t v_res_1622_;
v_res_1622_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(lean_box(0), v_cmp_1618_, v_t_u2081_1619_, v_t_u2082_1620_);
stack->m_num = v_res_1622_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___boxed(lean_object* v_00_u03b1_1623_, lean_object* v_cmp_1624_, lean_object* v_t_u2081_1625_, lean_object* v_t_u2082_1626_){
_start:
{
uint8_t v_res_1627_; lean_object* v_r_1628_; 
v_res_1627_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(v_00_u03b1_1623_, v_cmp_1624_, v_t_u2081_1625_, v_t_u2082_1626_);
v_r_1628_ = lean_box(v_res_1627_);
return v_r_1628_;
}
}
uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(lean_object* v_cmp_1629_, lean_object* v_t_u2081_1630_, lean_object* v_t_u2082_1631_){
_start:
{
uint8_t v___x_1632_; 
v___x_1632_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1629_, v_t_u2081_1630_, v_t_u2082_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1629_ = stack[0].m_obj;
lean_object* v_t_u2081_1630_ = stack[1].m_obj;
lean_object* v_t_u2082_1631_ = stack[2].m_obj;
uint8_t v_res_1633_;
v_res_1633_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(v_cmp_1629_, v_t_u2081_1630_, v_t_u2082_1631_);
stack->m_num = v_res_1633_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_1634_, lean_object* v_t_u2081_1635_, lean_object* v_t_u2082_1636_){
_start:
{
uint8_t v_res_1637_; lean_object* v_r_1638_; 
v_res_1637_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(v_cmp_1634_, v_t_u2081_1635_, v_t_u2082_1636_);
v_r_1638_ = lean_box(v_res_1637_);
return v_r_1638_;
}
}
uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(lean_object* v_00_u03b1_1639_, lean_object* v_cmp_1640_, lean_object* v_t_u2081_1641_, lean_object* v_t_u2082_1642_){
_start:
{
uint8_t v___x_1643_; 
v___x_1643_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1640_, v_t_u2081_1641_, v_t_u2082_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1640_ = stack[1].m_obj;
lean_object* v_t_u2081_1641_ = stack[2].m_obj;
lean_object* v_t_u2082_1642_ = stack[3].m_obj;
uint8_t v_res_1644_;
v_res_1644_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(lean_box(0), v_cmp_1640_, v_t_u2081_1641_, v_t_u2082_1642_);
stack->m_num = v_res_1644_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_cmp_1646_, lean_object* v_t_u2081_1647_, lean_object* v_t_u2082_1648_){
_start:
{
uint8_t v_res_1649_; lean_object* v_r_1650_; 
v_res_1649_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(v_00_u03b1_1645_, v_cmp_1646_, v_t_u2081_1647_, v_t_u2082_1648_);
v_r_1650_ = lean_box(v_res_1649_);
return v_r_1650_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1651_, lean_object* v_cmp_1652_, lean_object* v_t_u2081_1653_, lean_object* v_t_u2082_1654_){
_start:
{
uint8_t v___x_1655_; 
v___x_1655_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1652_, v_t_u2081_1653_, v_t_u2082_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1652_ = stack[1].m_obj;
lean_object* v_t_u2081_1653_ = stack[2].m_obj;
lean_object* v_t_u2082_1654_ = stack[3].m_obj;
uint8_t v_res_1656_;
v_res_1656_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(lean_box(0), v_cmp_1652_, v_t_u2081_1653_, v_t_u2082_1654_);
stack->m_num = v_res_1656_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1657_, lean_object* v_cmp_1658_, lean_object* v_t_u2081_1659_, lean_object* v_t_u2082_1660_){
_start:
{
uint8_t v_res_1661_; lean_object* v_r_1662_; 
v_res_1661_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(v_00_u03b1_1657_, v_cmp_1658_, v_t_u2081_1659_, v_t_u2082_1660_);
v_r_1662_ = lean_box(v_res_1661_);
return v_r_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1663_, lean_object* v_cmp_1664_, lean_object* v_00_u03b4_1665_, lean_object* v_t_1666_, lean_object* v_k_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1664_, v_t_1666_, v_k_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v_cmp_1672_, lean_object* v_t_u2082_1673_, lean_object* v_init_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1670_, v___y_1671_, v_cmp_1672_, v_t_u2082_1673_, v_init_1674_, v_x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v_cmp_1680_, lean_object* v_t_u2082_1681_, lean_object* v_init_1682_, lean_object* v_x_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1677_, v___y_1678_, v___y_1679_, v_cmp_1680_, v_t_u2082_1681_, v_init_1682_, v_x_1683_);
lean_dec(v___y_1679_);
lean_dec(v___y_1678_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq___redArg(lean_object* v_cmp_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_beq___boxed), 4, 2);
lean_closure_set(v___x_1686_, 0, lean_box(0));
lean_closure_set(v___x_1686_, 1, v_cmp_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq(lean_object* v_00_u03b1_1687_, lean_object* v_cmp_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_beq___boxed), 4, 2);
lean_closure_set(v___x_1689_, 0, lean_box(0));
lean_closure_set(v___x_1689_, 1, v_cmp_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff___redArg(lean_object* v_cmp_1690_, lean_object* v_t_u2081_1691_, lean_object* v_t_u2082_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_1690_, v_t_u2081_1691_, v_t_u2082_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff(lean_object* v_00_u03b1_1694_, lean_object* v_cmp_1695_, lean_object* v_t_u2081_1696_, lean_object* v_t_u2082_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_1695_, v_t_u2081_1696_, v_t_u2082_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff___redArg(lean_object* v_cmp_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_diff), 4, 2);
lean_closure_set(v___x_1700_, 0, lean_box(0));
lean_closure_set(v___x_1700_, 1, v_cmp_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff(lean_object* v_00_u03b1_1701_, lean_object* v_cmp_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_diff), 4, 2);
lean_closure_set(v___x_1703_, 0, lean_box(0));
lean_closure_set(v___x_1703_, 1, v_cmp_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_1704_, lean_object* v_a_1705_, lean_object* v_____s_1706_){
_start:
{
lean_object* v_r_1707_; lean_object* v___x_1708_; 
v_r_1707_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_1704_, v_a_1705_, v_____s_1706_);
v___x_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1708_, 0, v_r_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg(lean_object* v_cmp_1709_, lean_object* v_inst_1710_, lean_object* v_t_1711_, lean_object* v_l_1712_){
_start:
{
lean_object* v___f_1713_; lean_object* v___x_1714_; 
v___f_1713_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1713_, 0, v_cmp_1709_);
v___x_1714_ = lean_apply_4(v_inst_1710_, lean_box(0), v_l_1712_, v_t_1711_, v___f_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany(lean_object* v_00_u03b1_1715_, lean_object* v_cmp_1716_, lean_object* v_00_u03c1_1717_, lean_object* v_inst_1718_, lean_object* v_t_1719_, lean_object* v_l_1720_){
_start:
{
lean_object* v___f_1721_; lean_object* v___x_1722_; 
v___f_1721_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1721_, 0, v_cmp_1716_);
v___x_1722_ = lean_apply_4(v_inst_1718_, lean_box(0), v_l_1720_, v_t_1719_, v___f_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1(lean_object* v___f_1726_, lean_object* v_inst_1727_, lean_object* v_m_1728_, lean_object* v_prec_1729_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1730_ = ((lean_object*)(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1));
v___x_1731_ = lean_box(0);
v___x_1732_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1733_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1732_, v___f_1726_, v___x_1731_, v_m_1728_);
v___x_1734_ = l_List_repr___redArg(v_inst_1727_, v___x_1733_);
v___x_1735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1730_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = l_Repr_addAppParen(v___x_1735_, v_prec_1729_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_1737_, lean_object* v_inst_1738_, lean_object* v_m_1739_, lean_object* v_prec_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Std_TreeSet_Raw_instRepr___redArg___lam__1(v___f_1737_, v_inst_1738_, v_m_1739_, v_prec_1740_);
lean_dec(v_prec_1740_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg(lean_object* v_inst_1742_){
_start:
{
lean_object* v___f_1743_; lean_object* v___f_1744_; 
v___f_1743_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___f_1744_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1744_, 0, v___f_1743_);
lean_closure_set(v___f_1744_, 1, v_inst_1742_);
return v___f_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr(lean_object* v_00_u03b1_1745_, lean_object* v_cmp_1746_, lean_object* v_inst_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Std_TreeSet_Raw_instRepr___redArg(v_inst_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___boxed(lean_object* v_00_u03b1_1749_, lean_object* v_cmp_1750_, lean_object* v_inst_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Std_TreeSet_Raw_instRepr(v_00_u03b1_1749_, v_cmp_1750_, v_inst_1751_);
lean_dec_ref(v_cmp_1750_);
return v_res_1752_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
