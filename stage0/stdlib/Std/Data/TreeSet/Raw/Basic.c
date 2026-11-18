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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg___boxed(lean_object* v___dummy_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner(lean_object* v_00_u03b1_77_, lean_object* v_cmp_78_, lean_object* v_t_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(0);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___boxed(lean_object* v_00_u03b1_81_, lean_object* v_cmp_82_, lean_object* v_t_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_TreeSet_Raw_instCoeWFWFUnitInner(v_00_u03b1_81_, v_cmp_82_, v_t_83_);
lean_dec(v_t_83_);
lean_dec_ref(v_cmp_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty___redArg(){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(1);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty___redArg___boxed(lean_object* v___dummy_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_TreeSet_Raw_empty___redArg();
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty(lean_object* v_00_u03b1_89_, lean_object* v_cmp_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(1);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty___boxed(lean_object* v_00_u03b1_92_, lean_object* v_cmp_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_TreeSet_Raw_empty(v_00_u03b1_92_, v_cmp_93_);
lean_dec_ref(v_cmp_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_TreeSet_Raw_instEmptyCollection___redArg();
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection(lean_object* v_00_u03b1_99_, lean_object* v_cmp_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_box(1);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___boxed(lean_object* v_00_u03b1_102_, lean_object* v_cmp_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_TreeSet_Raw_instEmptyCollection(v_00_u03b1_102_, v_cmp_103_);
lean_dec_ref(v_cmp_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(1);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_TreeSet_Raw_instInhabited___redArg();
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited(lean_object* v_00_u03b1_109_, lean_object* v_cmp_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_box(1);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___boxed(lean_object* v_00_u03b1_112_, lean_object* v_cmp_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_TreeSet_Raw_instInhabited(v_00_u03b1_112_, v_cmp_113_);
lean_dec_ref(v_cmp_113_);
return v_res_114_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3));
v___x_155_ = l_String_toRawSubstring_x27(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(lean_object* v_x_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__4));
lean_inc(v_x_174_);
v___x_178_ = l_Lean_Syntax_isOfKind(v_x_174_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_x_174_);
v___x_179_ = lean_box(1);
v___x_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v_a_176_);
return v___x_180_;
}
else
{
lean_object* v_quotContext_181_; lean_object* v_currMacroScope_182_; lean_object* v_ref_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_quotContext_181_ = lean_ctor_get(v_a_175_, 1);
v_currMacroScope_182_ = lean_ctor_get(v_a_175_, 2);
v_ref_183_ = lean_ctor_get(v_a_175_, 5);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = l_Lean_Syntax_getArg(v_x_174_, v___x_184_);
v___x_186_ = lean_unsigned_to_nat(2u);
v___x_187_ = l_Lean_Syntax_getArg(v_x_174_, v___x_186_);
lean_dec(v_x_174_);
v___x_188_ = 0;
v___x_189_ = l_Lean_SourceInfo_fromRef(v_ref_183_, v___x_188_);
v___x_190_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2));
v___x_191_ = lean_obj_once(&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4, &l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4_once, _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4);
v___x_192_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_182_);
lean_inc(v_quotContext_181_);
v___x_193_ = l_Lean_addMacroScope(v_quotContext_181_, v___x_192_, v_currMacroScope_182_);
v___x_194_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10));
lean_inc_n(v___x_189_, 2);
v___x_195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_195_, 0, v___x_189_);
lean_ctor_set(v___x_195_, 1, v___x_191_);
lean_ctor_set(v___x_195_, 2, v___x_193_);
lean_ctor_set(v___x_195_, 3, v___x_194_);
v___x_196_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__9));
v___x_197_ = l_Lean_Syntax_node2(v___x_189_, v___x_196_, v___x_185_, v___x_187_);
v___x_198_ = l_Lean_Syntax_node2(v___x_189_, v___x_190_, v___x_195_, v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v_a_176_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___boxed(lean_object* v_x_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(v_x_200_, v_a_201_, v_a_202_);
lean_dec_ref(v_a_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(lean_object* v_x_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2));
lean_inc(v_x_207_);
v___x_211_ = l_Lean_Syntax_isOfKind(v_x_207_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_x_207_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_a_209_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = l_Lean_Syntax_getArg(v_x_207_, v___x_214_);
v___x_216_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1));
lean_inc(v___x_215_);
v___x_217_ = l_Lean_Syntax_isOfKind(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v___x_215_);
lean_dec(v_x_207_);
v___x_218_ = lean_box(0);
v___x_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v_a_209_);
return v___x_219_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_220_ = lean_unsigned_to_nat(1u);
v___x_221_ = l_Lean_Syntax_getArg(v_x_207_, v___x_220_);
lean_dec(v_x_207_);
v___x_222_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_221_);
v___x_223_ = l_Lean_Syntax_matchesNull(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec(v___x_221_);
lean_dec(v___x_215_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v_a_209_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v_ref_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_226_ = l_Lean_Syntax_getArg(v___x_221_, v___x_214_);
v___x_227_ = l_Lean_Syntax_getArg(v___x_221_, v___x_220_);
lean_dec(v___x_221_);
v_ref_228_ = l_Lean_replaceRef(v___x_215_, v_a_208_);
lean_dec(v___x_215_);
v___x_229_ = 0;
v___x_230_ = l_Lean_SourceInfo_fromRef(v_ref_228_, v___x_229_);
lean_dec(v_ref_228_);
v___x_231_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__4));
v___x_232_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__7));
lean_inc(v___x_230_);
v___x_233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_230_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = l_Lean_Syntax_node3(v___x_230_, v___x_231_, v___x_226_, v___x_233_, v___x_227_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v_a_209_);
return v___x_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___boxed(lean_object* v_x_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(v_x_236_, v_a_237_, v_a_238_);
lean_dec(v_a_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert___redArg(lean_object* v_cmp_240_, lean_object* v_l_241_, lean_object* v_a_242_){
_start:
{
uint8_t v___x_243_; 
lean_inc(v_l_241_);
lean_inc(v_a_242_);
lean_inc_ref(v_cmp_240_);
v___x_243_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_240_, v_a_242_, v_l_241_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_box(0);
v___x_245_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_240_, v_a_242_, v___x_244_, v_l_241_);
return v___x_245_;
}
else
{
lean_dec(v_a_242_);
lean_dec_ref(v_cmp_240_);
return v_l_241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert(lean_object* v_00_u03b1_246_, lean_object* v_cmp_247_, lean_object* v_l_248_, lean_object* v_a_249_){
_start:
{
uint8_t v___x_250_; 
lean_inc(v_l_248_);
lean_inc(v_a_249_);
lean_inc_ref(v_cmp_247_);
v___x_250_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_247_, v_a_249_, v_l_248_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_box(0);
v___x_252_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_247_, v_a_249_, v___x_251_, v_l_248_);
return v___x_252_;
}
else
{
lean_dec(v_a_249_);
lean_dec_ref(v_cmp_247_);
return v_l_248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg___lam__0(lean_object* v_cmp_253_, lean_object* v_e_254_){
_start:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_box(1);
lean_inc(v_e_254_);
lean_inc_ref(v_cmp_253_);
v___x_256_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_253_, v_e_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_box(0);
v___x_258_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_253_, v_e_254_, v___x_257_, v___x_255_);
return v___x_258_;
}
else
{
lean_dec(v_e_254_);
lean_dec_ref(v_cmp_253_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg(lean_object* v_cmp_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_260_, 0, v_cmp_259_);
return v___f_260_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton(lean_object* v_00_u03b1_261_, lean_object* v_cmp_262_){
_start:
{
lean_object* v___f_263_; 
v___f_263_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_263_, 0, v_cmp_262_);
return v___f_263_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg___lam__0(lean_object* v_cmp_264_, lean_object* v_e_265_, lean_object* v_s_266_){
_start:
{
uint8_t v___x_267_; 
lean_inc(v_s_266_);
lean_inc(v_e_265_);
lean_inc_ref(v_cmp_264_);
v___x_267_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_264_, v_e_265_, v_s_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_box(0);
v___x_269_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_264_, v_e_265_, v___x_268_, v_s_266_);
return v___x_269_;
}
else
{
lean_dec(v_e_265_);
lean_dec_ref(v_cmp_264_);
return v_s_266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg(lean_object* v_cmp_270_){
_start:
{
lean_object* v___f_271_; 
v___f_271_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_271_, 0, v_cmp_270_);
return v___f_271_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert(lean_object* v_00_u03b1_272_, lean_object* v_cmp_273_){
_start:
{
lean_object* v___f_274_; 
v___f_274_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_274_, 0, v_cmp_273_);
return v___f_274_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert___redArg(lean_object* v_cmp_275_, lean_object* v_t_276_, lean_object* v_a_277_){
_start:
{
uint8_t v___x_278_; 
lean_inc(v_t_276_);
lean_inc(v_a_277_);
lean_inc_ref(v_cmp_275_);
v___x_278_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_275_, v_a_277_, v_t_276_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_279_ = lean_box(0);
v___x_280_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_275_, v_a_277_, v___x_279_, v_t_276_);
v___x_281_ = lean_box(v___x_278_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v_a_277_);
lean_dec_ref(v_cmp_275_);
v___x_283_ = lean_box(v___x_278_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_t_276_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert(lean_object* v_00_u03b1_285_, lean_object* v_cmp_286_, lean_object* v_t_287_, lean_object* v_a_288_){
_start:
{
uint8_t v___x_289_; 
lean_inc(v_t_287_);
lean_inc(v_a_288_);
lean_inc_ref(v_cmp_286_);
v___x_289_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_286_, v_a_288_, v_t_287_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_290_ = lean_box(0);
v___x_291_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_286_, v_a_288_, v___x_290_, v_t_287_);
v___x_292_ = lean_box(v___x_289_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_291_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec(v_a_288_);
lean_dec_ref(v_cmp_286_);
v___x_294_ = lean_box(v___x_289_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_t_287_);
return v___x_295_;
}
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_contains___redArg(lean_object* v_cmp_296_, lean_object* v_l_297_, lean_object* v_a_298_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_296_, v_a_298_, v_l_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___redArg___boxed(lean_object* v_cmp_300_, lean_object* v_l_301_, lean_object* v_a_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Std_TreeSet_Raw_contains___redArg(v_cmp_300_, v_l_301_, v_a_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_contains(lean_object* v_00_u03b1_305_, lean_object* v_cmp_306_, lean_object* v_l_307_, lean_object* v_a_308_){
_start:
{
uint8_t v___x_309_; 
v___x_309_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_306_, v_a_308_, v_l_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___boxed(lean_object* v_00_u03b1_310_, lean_object* v_cmp_311_, lean_object* v_l_312_, lean_object* v_a_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Std_TreeSet_Raw_contains(v_00_u03b1_310_, v_cmp_311_, v_l_312_, v_a_313_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___redArg(){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_box(0);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___redArg___boxed(lean_object* v___dummy_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_TreeSet_Raw_instMembership___redArg();
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership(lean_object* v_00_u03b1_320_, lean_object* v_cmp_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_box(0);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___boxed(lean_object* v_00_u03b1_323_, lean_object* v_cmp_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Std_TreeSet_Raw_instMembership(v_00_u03b1_323_, v_cmp_324_);
lean_dec_ref(v_cmp_324_);
return v_res_325_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableMem___redArg(lean_object* v_cmp_326_, lean_object* v_t_327_, lean_object* v_a_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_326_, v_a_328_, v_t_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_330_, lean_object* v_t_331_, lean_object* v_a_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Std_TreeSet_Raw_instDecidableMem___redArg(v_cmp_330_, v_t_331_, v_a_332_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableMem(lean_object* v_00_u03b1_335_, lean_object* v_cmp_336_, lean_object* v_t_337_, lean_object* v_a_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_336_, v_a_338_, v_t_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_340_, lean_object* v_cmp_341_, lean_object* v_t_342_, lean_object* v_a_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Std_TreeSet_Raw_instDecidableMem(v_00_u03b1_340_, v_cmp_341_, v_t_342_, v_a_343_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg(lean_object* v_t_346_){
_start:
{
if (lean_obj_tag(v_t_346_) == 0)
{
lean_object* v_size_347_; 
v_size_347_ = lean_ctor_get(v_t_346_, 0);
lean_inc(v_size_347_);
return v_size_347_;
}
else
{
lean_object* v___x_348_; 
v___x_348_ = lean_unsigned_to_nat(0u);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg___boxed(lean_object* v_t_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_TreeSet_Raw_size___redArg(v_t_349_);
lean_dec(v_t_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size(lean_object* v_00_u03b1_351_, lean_object* v_cmp_352_, lean_object* v_t_353_){
_start:
{
if (lean_obj_tag(v_t_353_) == 0)
{
lean_object* v_size_354_; 
v_size_354_ = lean_ctor_get(v_t_353_, 0);
lean_inc(v_size_354_);
return v_size_354_;
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_unsigned_to_nat(0u);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___boxed(lean_object* v_00_u03b1_356_, lean_object* v_cmp_357_, lean_object* v_t_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_TreeSet_Raw_size(v_00_u03b1_356_, v_cmp_357_, v_t_358_);
lean_dec(v_t_358_);
lean_dec_ref(v_cmp_357_);
return v_res_359_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_isEmpty___redArg(lean_object* v_t_360_){
_start:
{
if (lean_obj_tag(v_t_360_) == 0)
{
uint8_t v___x_361_; 
v___x_361_ = 0;
return v___x_361_;
}
else
{
uint8_t v___x_362_; 
v___x_362_ = 1;
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___redArg___boxed(lean_object* v_t_363_){
_start:
{
uint8_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_Std_TreeSet_Raw_isEmpty___redArg(v_t_363_);
lean_dec(v_t_363_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_isEmpty(lean_object* v_00_u03b1_366_, lean_object* v_cmp_367_, lean_object* v_t_368_){
_start:
{
if (lean_obj_tag(v_t_368_) == 0)
{
uint8_t v___x_369_; 
v___x_369_ = 0;
return v___x_369_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = 1;
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___boxed(lean_object* v_00_u03b1_371_, lean_object* v_cmp_372_, lean_object* v_t_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_Std_TreeSet_Raw_isEmpty(v_00_u03b1_371_, v_cmp_372_, v_t_373_);
lean_dec(v_t_373_);
lean_dec_ref(v_cmp_372_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase___redArg(lean_object* v_cmp_376_, lean_object* v_t_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_376_, v_a_378_, v_t_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase(lean_object* v_00_u03b1_380_, lean_object* v_cmp_381_, lean_object* v_t_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_381_, v_a_383_, v_t_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f___redArg(lean_object* v_cmp_385_, lean_object* v_t_386_, lean_object* v_a_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_385_, v_t_386_, v_a_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f(lean_object* v_00_u03b1_389_, lean_object* v_cmp_390_, lean_object* v_t_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_390_, v_t_391_, v_a_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get___redArg(lean_object* v_cmp_394_, lean_object* v_t_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_394_, v_t_395_, v_a_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get(lean_object* v_00_u03b1_398_, lean_object* v_cmp_399_, lean_object* v_t_400_, lean_object* v_a_401_, lean_object* v_h_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_399_, v_t_400_, v_a_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___redArg(lean_object* v_cmp_404_, lean_object* v_inst_405_, lean_object* v_t_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_404_, v_t_406_, v_a_407_, v_inst_405_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___redArg___boxed(lean_object* v_cmp_409_, lean_object* v_inst_410_, lean_object* v_t_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_TreeSet_Raw_get_x21___redArg(v_cmp_409_, v_inst_410_, v_t_411_, v_a_412_);
lean_dec(v_inst_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21(lean_object* v_00_u03b1_414_, lean_object* v_cmp_415_, lean_object* v_inst_416_, lean_object* v_t_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_415_, v_t_417_, v_a_418_, v_inst_416_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___boxed(lean_object* v_00_u03b1_420_, lean_object* v_cmp_421_, lean_object* v_inst_422_, lean_object* v_t_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_TreeSet_Raw_get_x21(v_00_u03b1_420_, v_cmp_421_, v_inst_422_, v_t_423_, v_a_424_);
lean_dec(v_inst_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg(lean_object* v_cmp_426_, lean_object* v_t_427_, lean_object* v_a_428_, lean_object* v_fallback_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_426_, v_t_427_, v_a_428_, v_fallback_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg___boxed(lean_object* v_cmp_431_, lean_object* v_t_432_, lean_object* v_a_433_, lean_object* v_fallback_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_TreeSet_Raw_getD___redArg(v_cmp_431_, v_t_432_, v_a_433_, v_fallback_434_);
lean_dec(v_fallback_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD(lean_object* v_00_u03b1_436_, lean_object* v_cmp_437_, lean_object* v_t_438_, lean_object* v_a_439_, lean_object* v_fallback_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_437_, v_t_438_, v_a_439_, v_fallback_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___boxed(lean_object* v_00_u03b1_442_, lean_object* v_cmp_443_, lean_object* v_t_444_, lean_object* v_a_445_, lean_object* v_fallback_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_TreeSet_Raw_getD(v_00_u03b1_442_, v_cmp_443_, v_t_444_, v_a_445_, v_fallback_446_);
lean_dec(v_fallback_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg(lean_object* v_t_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg___boxed(lean_object* v_t_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_TreeSet_Raw_min_x3f___redArg(v_t_450_);
lean_dec(v_t_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f(lean_object* v_00_u03b1_452_, lean_object* v_cmp_453_, lean_object* v_t_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___boxed(lean_object* v_00_u03b1_456_, lean_object* v_cmp_457_, lean_object* v_t_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_TreeSet_Raw_min_x3f(v_00_u03b1_456_, v_cmp_457_, v_t_458_);
lean_dec(v_t_458_);
lean_dec_ref(v_cmp_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg(lean_object* v_inst_460_, lean_object* v_t_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_460_, v_t_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg___boxed(lean_object* v_inst_463_, lean_object* v_t_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_TreeSet_Raw_min_x21___redArg(v_inst_463_, v_t_464_);
lean_dec(v_t_464_);
lean_dec(v_inst_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21(lean_object* v_00_u03b1_466_, lean_object* v_cmp_467_, lean_object* v_inst_468_, lean_object* v_t_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_468_, v_t_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___boxed(lean_object* v_00_u03b1_471_, lean_object* v_cmp_472_, lean_object* v_inst_473_, lean_object* v_t_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_TreeSet_Raw_min_x21(v_00_u03b1_471_, v_cmp_472_, v_inst_473_, v_t_474_);
lean_dec(v_t_474_);
lean_dec(v_inst_473_);
lean_dec_ref(v_cmp_472_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg(lean_object* v_t_476_, lean_object* v_fallback_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_476_, v_fallback_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg___boxed(lean_object* v_t_479_, lean_object* v_fallback_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_TreeSet_Raw_minD___redArg(v_t_479_, v_fallback_480_);
lean_dec(v_fallback_480_);
lean_dec(v_t_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD(lean_object* v_00_u03b1_482_, lean_object* v_cmp_483_, lean_object* v_t_484_, lean_object* v_fallback_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_484_, v_fallback_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___boxed(lean_object* v_00_u03b1_487_, lean_object* v_cmp_488_, lean_object* v_t_489_, lean_object* v_fallback_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_TreeSet_Raw_minD(v_00_u03b1_487_, v_cmp_488_, v_t_489_, v_fallback_490_);
lean_dec(v_fallback_490_);
lean_dec(v_t_489_);
lean_dec_ref(v_cmp_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg(lean_object* v_t_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg___boxed(lean_object* v_t_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_TreeSet_Raw_max_x3f___redArg(v_t_494_);
lean_dec(v_t_494_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f(lean_object* v_00_u03b1_496_, lean_object* v_cmp_497_, lean_object* v_t_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___boxed(lean_object* v_00_u03b1_500_, lean_object* v_cmp_501_, lean_object* v_t_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_TreeSet_Raw_max_x3f(v_00_u03b1_500_, v_cmp_501_, v_t_502_);
lean_dec(v_t_502_);
lean_dec_ref(v_cmp_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg(lean_object* v_inst_504_, lean_object* v_t_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_504_, v_t_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg___boxed(lean_object* v_inst_507_, lean_object* v_t_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_TreeSet_Raw_max_x21___redArg(v_inst_507_, v_t_508_);
lean_dec(v_t_508_);
lean_dec(v_inst_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21(lean_object* v_00_u03b1_510_, lean_object* v_cmp_511_, lean_object* v_inst_512_, lean_object* v_t_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_512_, v_t_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___boxed(lean_object* v_00_u03b1_515_, lean_object* v_cmp_516_, lean_object* v_inst_517_, lean_object* v_t_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_TreeSet_Raw_max_x21(v_00_u03b1_515_, v_cmp_516_, v_inst_517_, v_t_518_);
lean_dec(v_t_518_);
lean_dec(v_inst_517_);
lean_dec_ref(v_cmp_516_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg(lean_object* v_t_520_, lean_object* v_fallback_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_520_, v_fallback_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg___boxed(lean_object* v_t_523_, lean_object* v_fallback_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_TreeSet_Raw_maxD___redArg(v_t_523_, v_fallback_524_);
lean_dec(v_fallback_524_);
lean_dec(v_t_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD(lean_object* v_00_u03b1_526_, lean_object* v_cmp_527_, lean_object* v_t_528_, lean_object* v_fallback_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_528_, v_fallback_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___boxed(lean_object* v_00_u03b1_531_, lean_object* v_cmp_532_, lean_object* v_t_533_, lean_object* v_fallback_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_TreeSet_Raw_maxD(v_00_u03b1_531_, v_cmp_532_, v_t_533_, v_fallback_534_);
lean_dec(v_fallback_534_);
lean_dec(v_t_533_);
lean_dec_ref(v_cmp_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg(lean_object* v_t_536_, lean_object* v_n_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_536_, v_n_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg___boxed(lean_object* v_t_539_, lean_object* v_n_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_TreeSet_Raw_atIdx_x3f___redArg(v_t_539_, v_n_540_);
lean_dec(v_t_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f(lean_object* v_00_u03b1_542_, lean_object* v_cmp_543_, lean_object* v_t_544_, lean_object* v_n_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_544_, v_n_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___boxed(lean_object* v_00_u03b1_547_, lean_object* v_cmp_548_, lean_object* v_t_549_, lean_object* v_n_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_TreeSet_Raw_atIdx_x3f(v_00_u03b1_547_, v_cmp_548_, v_t_549_, v_n_550_);
lean_dec(v_t_549_);
lean_dec_ref(v_cmp_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg(lean_object* v_inst_552_, lean_object* v_t_553_, lean_object* v_n_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_552_, v_t_553_, v_n_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg___boxed(lean_object* v_inst_556_, lean_object* v_t_557_, lean_object* v_n_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_TreeSet_Raw_atIdx_x21___redArg(v_inst_556_, v_t_557_, v_n_558_);
lean_dec(v_t_557_);
lean_dec(v_inst_556_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21(lean_object* v_00_u03b1_560_, lean_object* v_cmp_561_, lean_object* v_inst_562_, lean_object* v_t_563_, lean_object* v_n_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_562_, v_t_563_, v_n_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___boxed(lean_object* v_00_u03b1_566_, lean_object* v_cmp_567_, lean_object* v_inst_568_, lean_object* v_t_569_, lean_object* v_n_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_TreeSet_Raw_atIdx_x21(v_00_u03b1_566_, v_cmp_567_, v_inst_568_, v_t_569_, v_n_570_);
lean_dec(v_t_569_);
lean_dec(v_inst_568_);
lean_dec_ref(v_cmp_567_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg(lean_object* v_t_572_, lean_object* v_n_573_, lean_object* v_fallback_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_572_, v_n_573_, v_fallback_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg___boxed(lean_object* v_t_576_, lean_object* v_n_577_, lean_object* v_fallback_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_TreeSet_Raw_atIdxD___redArg(v_t_576_, v_n_577_, v_fallback_578_);
lean_dec(v_fallback_578_);
lean_dec(v_t_576_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD(lean_object* v_00_u03b1_580_, lean_object* v_cmp_581_, lean_object* v_t_582_, lean_object* v_n_583_, lean_object* v_fallback_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_582_, v_n_583_, v_fallback_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___boxed(lean_object* v_00_u03b1_586_, lean_object* v_cmp_587_, lean_object* v_t_588_, lean_object* v_n_589_, lean_object* v_fallback_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_TreeSet_Raw_atIdxD(v_00_u03b1_586_, v_cmp_587_, v_t_588_, v_n_589_, v_fallback_590_);
lean_dec(v_fallback_590_);
lean_dec(v_t_588_);
lean_dec_ref(v_cmp_587_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f___redArg(lean_object* v_cmp_592_, lean_object* v_t_593_, lean_object* v_k_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_box(0);
v___x_596_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_592_, v_k_594_, v___x_595_, v_t_593_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f(lean_object* v_00_u03b1_597_, lean_object* v_cmp_598_, lean_object* v_t_599_, lean_object* v_k_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_box(0);
v___x_602_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_598_, v_k_600_, v___x_601_, v_t_599_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f___redArg(lean_object* v_cmp_603_, lean_object* v_t_604_, lean_object* v_k_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_box(0);
v___x_607_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_603_, v_k_605_, v___x_606_, v_t_604_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f(lean_object* v_00_u03b1_608_, lean_object* v_cmp_609_, lean_object* v_t_610_, lean_object* v_k_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_box(0);
v___x_613_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_609_, v_k_611_, v___x_612_, v_t_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f___redArg(lean_object* v_cmp_614_, lean_object* v_t_615_, lean_object* v_k_616_){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_box(0);
v___x_618_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_614_, v_k_616_, v___x_617_, v_t_615_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f(lean_object* v_00_u03b1_619_, lean_object* v_cmp_620_, lean_object* v_t_621_, lean_object* v_k_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_box(0);
v___x_624_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_620_, v_k_622_, v___x_623_, v_t_621_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f___redArg(lean_object* v_cmp_625_, lean_object* v_t_626_, lean_object* v_k_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_box(0);
v___x_629_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_625_, v_k_627_, v___x_628_, v_t_626_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f(lean_object* v_00_u03b1_630_, lean_object* v_cmp_631_, lean_object* v_t_632_, lean_object* v_k_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_box(0);
v___x_635_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_631_, v_k_633_, v___x_634_, v_t_632_);
return v___x_635_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_639_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2));
v___x_640_ = lean_unsigned_to_nat(14u);
v___x_641_ = lean_unsigned_to_nat(22u);
v___x_642_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1));
v___x_643_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0));
v___x_644_ = l_mkPanicMessageWithDecl(v___x_643_, v___x_642_, v___x_641_, v___x_640_, v___x_639_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg(lean_object* v_cmp_645_, lean_object* v_inst_646_, lean_object* v_t_647_, lean_object* v_k_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_box(0);
v___x_650_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_645_, v_k_648_, v___x_649_, v_t_647_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_652_ = l_panic___redArg(v_inst_646_, v___x_651_);
return v___x_652_;
}
else
{
lean_object* v_val_653_; 
v_val_653_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_653_);
lean_dec_ref_known(v___x_650_, 1);
return v_val_653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg___boxed(lean_object* v_cmp_654_, lean_object* v_inst_655_, lean_object* v_t_656_, lean_object* v_k_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_TreeSet_Raw_getGE_x21___redArg(v_cmp_654_, v_inst_655_, v_t_656_, v_k_657_);
lean_dec(v_inst_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21(lean_object* v_00_u03b1_659_, lean_object* v_cmp_660_, lean_object* v_inst_661_, lean_object* v_t_662_, lean_object* v_k_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_box(0);
v___x_665_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_660_, v_k_663_, v___x_664_, v_t_662_);
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
v_val_668_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_665_, 1);
return v_val_668_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___boxed(lean_object* v_00_u03b1_669_, lean_object* v_cmp_670_, lean_object* v_inst_671_, lean_object* v_t_672_, lean_object* v_k_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_TreeSet_Raw_getGE_x21(v_00_u03b1_669_, v_cmp_670_, v_inst_671_, v_t_672_, v_k_673_);
lean_dec(v_inst_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg(lean_object* v_cmp_675_, lean_object* v_inst_676_, lean_object* v_t_677_, lean_object* v_k_678_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_box(0);
v___x_680_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_675_, v_k_678_, v___x_679_, v_t_677_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_682_ = l_panic___redArg(v_inst_676_, v___x_681_);
return v___x_682_;
}
else
{
lean_object* v_val_683_; 
v_val_683_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v___x_680_, 1);
return v_val_683_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg___boxed(lean_object* v_cmp_684_, lean_object* v_inst_685_, lean_object* v_t_686_, lean_object* v_k_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_TreeSet_Raw_getGT_x21___redArg(v_cmp_684_, v_inst_685_, v_t_686_, v_k_687_);
lean_dec(v_inst_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21(lean_object* v_00_u03b1_689_, lean_object* v_cmp_690_, lean_object* v_inst_691_, lean_object* v_t_692_, lean_object* v_k_693_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_box(0);
v___x_695_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_690_, v_k_693_, v___x_694_, v_t_692_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_697_ = l_panic___redArg(v_inst_691_, v___x_696_);
return v___x_697_;
}
else
{
lean_object* v_val_698_; 
v_val_698_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_val_698_);
lean_dec_ref_known(v___x_695_, 1);
return v_val_698_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___boxed(lean_object* v_00_u03b1_699_, lean_object* v_cmp_700_, lean_object* v_inst_701_, lean_object* v_t_702_, lean_object* v_k_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_TreeSet_Raw_getGT_x21(v_00_u03b1_699_, v_cmp_700_, v_inst_701_, v_t_702_, v_k_703_);
lean_dec(v_inst_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg(lean_object* v_cmp_705_, lean_object* v_inst_706_, lean_object* v_t_707_, lean_object* v_k_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_box(0);
v___x_710_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_705_, v_k_708_, v___x_709_, v_t_707_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_712_ = l_panic___redArg(v_inst_706_, v___x_711_);
return v___x_712_;
}
else
{
lean_object* v_val_713_; 
v_val_713_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_val_713_);
lean_dec_ref_known(v___x_710_, 1);
return v_val_713_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg___boxed(lean_object* v_cmp_714_, lean_object* v_inst_715_, lean_object* v_t_716_, lean_object* v_k_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_TreeSet_Raw_getLE_x21___redArg(v_cmp_714_, v_inst_715_, v_t_716_, v_k_717_);
lean_dec(v_inst_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21(lean_object* v_00_u03b1_719_, lean_object* v_cmp_720_, lean_object* v_inst_721_, lean_object* v_t_722_, lean_object* v_k_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_box(0);
v___x_725_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_720_, v_k_723_, v___x_724_, v_t_722_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_727_ = l_panic___redArg(v_inst_721_, v___x_726_);
return v___x_727_;
}
else
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v___x_725_, 1);
return v_val_728_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___boxed(lean_object* v_00_u03b1_729_, lean_object* v_cmp_730_, lean_object* v_inst_731_, lean_object* v_t_732_, lean_object* v_k_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_TreeSet_Raw_getLE_x21(v_00_u03b1_729_, v_cmp_730_, v_inst_731_, v_t_732_, v_k_733_);
lean_dec(v_inst_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg(lean_object* v_cmp_735_, lean_object* v_inst_736_, lean_object* v_t_737_, lean_object* v_k_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_box(0);
v___x_740_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_735_, v_k_738_, v___x_739_, v_t_737_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_742_ = l_panic___redArg(v_inst_736_, v___x_741_);
return v___x_742_;
}
else
{
lean_object* v_val_743_; 
v_val_743_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_val_743_);
lean_dec_ref_known(v___x_740_, 1);
return v_val_743_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg___boxed(lean_object* v_cmp_744_, lean_object* v_inst_745_, lean_object* v_t_746_, lean_object* v_k_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_TreeSet_Raw_getLT_x21___redArg(v_cmp_744_, v_inst_745_, v_t_746_, v_k_747_);
lean_dec(v_inst_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21(lean_object* v_00_u03b1_749_, lean_object* v_cmp_750_, lean_object* v_inst_751_, lean_object* v_t_752_, lean_object* v_k_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_box(0);
v___x_755_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_750_, v_k_753_, v___x_754_, v_t_752_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_757_ = l_panic___redArg(v_inst_751_, v___x_756_);
return v___x_757_;
}
else
{
lean_object* v_val_758_; 
v_val_758_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_val_758_);
lean_dec_ref_known(v___x_755_, 1);
return v_val_758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___boxed(lean_object* v_00_u03b1_759_, lean_object* v_cmp_760_, lean_object* v_inst_761_, lean_object* v_t_762_, lean_object* v_k_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_TreeSet_Raw_getLT_x21(v_00_u03b1_759_, v_cmp_760_, v_inst_761_, v_t_762_, v_k_763_);
lean_dec(v_inst_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg(lean_object* v_cmp_765_, lean_object* v_t_766_, lean_object* v_k_767_, lean_object* v_fallback_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_box(0);
v___x_770_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_765_, v_k_767_, v___x_769_, v_t_766_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_inc(v_fallback_768_);
return v_fallback_768_;
}
else
{
lean_object* v_val_771_; 
v_val_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v___x_770_, 1);
return v_val_771_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg___boxed(lean_object* v_cmp_772_, lean_object* v_t_773_, lean_object* v_k_774_, lean_object* v_fallback_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Std_TreeSet_Raw_getGED___redArg(v_cmp_772_, v_t_773_, v_k_774_, v_fallback_775_);
lean_dec(v_fallback_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED(lean_object* v_00_u03b1_777_, lean_object* v_cmp_778_, lean_object* v_t_779_, lean_object* v_k_780_, lean_object* v_fallback_781_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_box(0);
v___x_783_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_778_, v_k_780_, v___x_782_, v_t_779_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_inc(v_fallback_781_);
return v_fallback_781_;
}
else
{
lean_object* v_val_784_; 
v_val_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v___x_783_, 1);
return v_val_784_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___boxed(lean_object* v_00_u03b1_785_, lean_object* v_cmp_786_, lean_object* v_t_787_, lean_object* v_k_788_, lean_object* v_fallback_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_TreeSet_Raw_getGED(v_00_u03b1_785_, v_cmp_786_, v_t_787_, v_k_788_, v_fallback_789_);
lean_dec(v_fallback_789_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg(lean_object* v_cmp_791_, lean_object* v_t_792_, lean_object* v_k_793_, lean_object* v_fallback_794_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_box(0);
v___x_796_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_791_, v_k_793_, v___x_795_, v_t_792_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_inc(v_fallback_794_);
return v_fallback_794_;
}
else
{
lean_object* v_val_797_; 
v_val_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v___x_796_, 1);
return v_val_797_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg___boxed(lean_object* v_cmp_798_, lean_object* v_t_799_, lean_object* v_k_800_, lean_object* v_fallback_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_TreeSet_Raw_getGTD___redArg(v_cmp_798_, v_t_799_, v_k_800_, v_fallback_801_);
lean_dec(v_fallback_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD(lean_object* v_00_u03b1_803_, lean_object* v_cmp_804_, lean_object* v_t_805_, lean_object* v_k_806_, lean_object* v_fallback_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_box(0);
v___x_809_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_804_, v_k_806_, v___x_808_, v_t_805_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_inc(v_fallback_807_);
return v_fallback_807_;
}
else
{
lean_object* v_val_810_; 
v_val_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_val_810_);
lean_dec_ref_known(v___x_809_, 1);
return v_val_810_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___boxed(lean_object* v_00_u03b1_811_, lean_object* v_cmp_812_, lean_object* v_t_813_, lean_object* v_k_814_, lean_object* v_fallback_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_TreeSet_Raw_getGTD(v_00_u03b1_811_, v_cmp_812_, v_t_813_, v_k_814_, v_fallback_815_);
lean_dec(v_fallback_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg(lean_object* v_cmp_817_, lean_object* v_t_818_, lean_object* v_k_819_, lean_object* v_fallback_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_box(0);
v___x_822_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_817_, v_k_819_, v___x_821_, v_t_818_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_inc(v_fallback_820_);
return v_fallback_820_;
}
else
{
lean_object* v_val_823_; 
v_val_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_val_823_);
lean_dec_ref_known(v___x_822_, 1);
return v_val_823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg___boxed(lean_object* v_cmp_824_, lean_object* v_t_825_, lean_object* v_k_826_, lean_object* v_fallback_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_TreeSet_Raw_getLED___redArg(v_cmp_824_, v_t_825_, v_k_826_, v_fallback_827_);
lean_dec(v_fallback_827_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED(lean_object* v_00_u03b1_829_, lean_object* v_cmp_830_, lean_object* v_t_831_, lean_object* v_k_832_, lean_object* v_fallback_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_box(0);
v___x_835_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_830_, v_k_832_, v___x_834_, v_t_831_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_inc(v_fallback_833_);
return v_fallback_833_;
}
else
{
lean_object* v_val_836_; 
v_val_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_val_836_);
lean_dec_ref_known(v___x_835_, 1);
return v_val_836_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___boxed(lean_object* v_00_u03b1_837_, lean_object* v_cmp_838_, lean_object* v_t_839_, lean_object* v_k_840_, lean_object* v_fallback_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_TreeSet_Raw_getLED(v_00_u03b1_837_, v_cmp_838_, v_t_839_, v_k_840_, v_fallback_841_);
lean_dec(v_fallback_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg(lean_object* v_cmp_843_, lean_object* v_t_844_, lean_object* v_k_845_, lean_object* v_fallback_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_box(0);
v___x_848_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_843_, v_k_845_, v___x_847_, v_t_844_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_inc(v_fallback_846_);
return v_fallback_846_;
}
else
{
lean_object* v_val_849_; 
v_val_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_val_849_);
lean_dec_ref_known(v___x_848_, 1);
return v_val_849_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg___boxed(lean_object* v_cmp_850_, lean_object* v_t_851_, lean_object* v_k_852_, lean_object* v_fallback_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_TreeSet_Raw_getLTD___redArg(v_cmp_850_, v_t_851_, v_k_852_, v_fallback_853_);
lean_dec(v_fallback_853_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD(lean_object* v_00_u03b1_855_, lean_object* v_cmp_856_, lean_object* v_t_857_, lean_object* v_k_858_, lean_object* v_fallback_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_box(0);
v___x_861_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_856_, v_k_858_, v___x_860_, v_t_857_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_inc(v_fallback_859_);
return v_fallback_859_;
}
else
{
lean_object* v_val_862_; 
v_val_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v___x_861_, 1);
return v_val_862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___boxed(lean_object* v_00_u03b1_863_, lean_object* v_cmp_864_, lean_object* v_t_865_, lean_object* v_k_866_, lean_object* v_fallback_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_TreeSet_Raw_getLTD(v_00_u03b1_863_, v_cmp_864_, v_t_865_, v_k_866_, v_fallback_867_);
lean_dec(v_fallback_867_);
return v_res_868_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_filter___redArg___lam__0(lean_object* v_f_869_, lean_object* v_a_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = lean_apply_1(v_f_869_, v_a_870_);
v___x_873_ = lean_unbox(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_874_, lean_object* v_a_875_, lean_object* v_x_876_){
_start:
{
uint8_t v_res_877_; lean_object* v_r_878_; 
v_res_877_ = l_Std_TreeSet_Raw_filter___redArg___lam__0(v_f_874_, v_a_875_, v_x_876_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg(lean_object* v_f_879_, lean_object* v_t_880_){
_start:
{
lean_object* v___f_881_; lean_object* v___x_882_; 
v___f_881_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_881_, 0, v_f_879_);
v___x_882_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_881_, v_t_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter(lean_object* v_00_u03b1_883_, lean_object* v_cmp_884_, lean_object* v_f_885_, lean_object* v_t_886_){
_start:
{
lean_object* v___f_887_; lean_object* v___x_888_; 
v___f_887_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_887_, 0, v_f_885_);
v___x_888_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_887_, v_t_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___boxed(lean_object* v_00_u03b1_889_, lean_object* v_cmp_890_, lean_object* v_f_891_, lean_object* v_t_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_TreeSet_Raw_filter(v_00_u03b1_889_, v_cmp_890_, v_f_891_, v_t_892_);
lean_dec_ref(v_cmp_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg___lam__0(lean_object* v_f_894_, lean_object* v_c_895_, lean_object* v_a_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_apply_2(v_f_894_, v_c_895_, v_a_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg(lean_object* v_inst_899_, lean_object* v_f_900_, lean_object* v_init_901_, lean_object* v_t_902_){
_start:
{
lean_object* v___f_903_; lean_object* v___x_904_; 
v___f_903_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_903_, 0, v_f_900_);
v___x_904_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_899_, v___f_903_, v_init_901_, v_t_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM(lean_object* v_00_u03b1_905_, lean_object* v_cmp_906_, lean_object* v_00_u03b4_907_, lean_object* v_m_908_, lean_object* v_inst_909_, lean_object* v_f_910_, lean_object* v_init_911_, lean_object* v_t_912_){
_start:
{
lean_object* v___f_913_; lean_object* v___x_914_; 
v___f_913_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_913_, 0, v_f_910_);
v___x_914_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_909_, v___f_913_, v_init_911_, v_t_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___boxed(lean_object* v_00_u03b1_915_, lean_object* v_cmp_916_, lean_object* v_00_u03b4_917_, lean_object* v_m_918_, lean_object* v_inst_919_, lean_object* v_f_920_, lean_object* v_init_921_, lean_object* v_t_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_TreeSet_Raw_foldlM(v_00_u03b1_915_, v_cmp_916_, v_00_u03b4_917_, v_m_918_, v_inst_919_, v_f_920_, v_init_921_, v_t_922_);
lean_dec_ref(v_cmp_916_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___redArg(lean_object* v_f_924_, lean_object* v_init_925_, lean_object* v_t_926_){
_start:
{
lean_object* v___f_927_; lean_object* v___x_928_; 
v___f_927_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_927_, 0, v_f_924_);
v___x_928_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_927_, v_init_925_, v_t_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl(lean_object* v_00_u03b1_929_, lean_object* v_cmp_930_, lean_object* v_00_u03b4_931_, lean_object* v_f_932_, lean_object* v_init_933_, lean_object* v_t_934_){
_start:
{
lean_object* v___f_935_; lean_object* v___x_936_; 
v___f_935_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_935_, 0, v_f_932_);
v___x_936_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_935_, v_init_933_, v_t_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___boxed(lean_object* v_00_u03b1_937_, lean_object* v_cmp_938_, lean_object* v_00_u03b4_939_, lean_object* v_f_940_, lean_object* v_init_941_, lean_object* v_t_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Std_TreeSet_Raw_foldl(v_00_u03b1_937_, v_cmp_938_, v_00_u03b4_939_, v_f_940_, v_init_941_, v_t_942_);
lean_dec_ref(v_cmp_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg___lam__0(lean_object* v_f_944_, lean_object* v_a_945_, lean_object* v_x_946_, lean_object* v_acc_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = lean_apply_2(v_f_944_, v_a_945_, v_acc_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg(lean_object* v_inst_949_, lean_object* v_f_950_, lean_object* v_init_951_, lean_object* v_t_952_){
_start:
{
lean_object* v___f_953_; lean_object* v___x_954_; 
v___f_953_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_953_, 0, v_f_950_);
v___x_954_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_949_, v___f_953_, v_init_951_, v_t_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM(lean_object* v_00_u03b1_955_, lean_object* v_cmp_956_, lean_object* v_00_u03b4_957_, lean_object* v_m_958_, lean_object* v_inst_959_, lean_object* v_f_960_, lean_object* v_init_961_, lean_object* v_t_962_){
_start:
{
lean_object* v___f_963_; lean_object* v___x_964_; 
v___f_963_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_963_, 0, v_f_960_);
v___x_964_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_959_, v___f_963_, v_init_961_, v_t_962_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___boxed(lean_object* v_00_u03b1_965_, lean_object* v_cmp_966_, lean_object* v_00_u03b4_967_, lean_object* v_m_968_, lean_object* v_inst_969_, lean_object* v_f_970_, lean_object* v_init_971_, lean_object* v_t_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_TreeSet_Raw_foldrM(v_00_u03b1_965_, v_cmp_966_, v_00_u03b4_967_, v_m_968_, v_inst_969_, v_f_970_, v_init_971_, v_t_972_);
lean_dec_ref(v_cmp_966_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg___lam__0(lean_object* v_f_974_, lean_object* v_x1_975_, lean_object* v_x2_976_, lean_object* v_x3_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = lean_apply_2(v_f_974_, v_x1_975_, v_x3_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg(lean_object* v_f_998_, lean_object* v_init_999_, lean_object* v_t_1000_){
_start:
{
lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___f_1001_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1001_, 0, v_f_998_);
v___x_1002_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1003_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1002_, v___f_1001_, v_init_999_, v_t_1000_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr(lean_object* v_00_u03b1_1004_, lean_object* v_cmp_1005_, lean_object* v_00_u03b4_1006_, lean_object* v_f_1007_, lean_object* v_init_1008_, lean_object* v_t_1009_){
_start:
{
lean_object* v___f_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___f_1010_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1010_, 0, v_f_1007_);
v___x_1011_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1011_, v___f_1010_, v_init_1008_, v_t_1009_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___boxed(lean_object* v_00_u03b1_1013_, lean_object* v_cmp_1014_, lean_object* v_00_u03b4_1015_, lean_object* v_f_1016_, lean_object* v_init_1017_, lean_object* v_t_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Std_TreeSet_Raw_foldr(v_00_u03b1_1013_, v_cmp_1014_, v_00_u03b4_1015_, v_f_1016_, v_init_1017_, v_t_1018_);
lean_dec_ref(v_cmp_1014_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg___lam__0(lean_object* v_f_1020_, lean_object* v_cmp_1021_, lean_object* v_x_1022_, lean_object* v_a_1023_, lean_object* v_b_1024_){
_start:
{
lean_object* v_fst_1025_; lean_object* v_snd_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1040_; 
v_fst_1025_ = lean_ctor_get(v_x_1022_, 0);
v_snd_1026_ = lean_ctor_get(v_x_1022_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1028_ = v_x_1022_;
v_isShared_1029_ = v_isSharedCheck_1040_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_snd_1026_);
lean_inc(v_fst_1025_);
lean_dec(v_x_1022_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1040_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
lean_inc(v_a_1023_);
v___x_1030_ = lean_apply_1(v_f_1020_, v_a_1023_);
v___x_1031_ = lean_unbox(v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1021_, v_a_1023_, v_b_1024_, v_snd_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v___x_1032_);
v___x_1034_ = v___x_1028_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_fst_1025_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1021_, v_a_1023_, v_b_1024_, v_fst_1025_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1036_);
v___x_1038_ = v___x_1028_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_snd_1026_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg(lean_object* v_cmp_1043_, lean_object* v_f_1044_, lean_object* v_t_1045_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v_p_1048_; lean_object* v_fst_1049_; lean_object* v_snd_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v___f_1046_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1046_, 0, v_f_1044_);
lean_closure_set(v___f_1046_, 1, v_cmp_1043_);
v___x_1047_ = ((lean_object*)(l_Std_TreeSet_Raw_partition___redArg___closed__0));
v_p_1048_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1046_, v___x_1047_, v_t_1045_);
v_fst_1049_ = lean_ctor_get(v_p_1048_, 0);
v_snd_1050_ = lean_ctor_get(v_p_1048_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_p_1048_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v_p_1048_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_snd_1050_);
lean_inc(v_fst_1049_);
lean_dec(v_p_1048_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_fst_1049_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_snd_1050_);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition(lean_object* v_00_u03b1_1058_, lean_object* v_cmp_1059_, lean_object* v_f_1060_, lean_object* v_t_1061_){
_start:
{
lean_object* v___f_1062_; lean_object* v___x_1063_; lean_object* v_p_1064_; lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
v___f_1062_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1062_, 0, v_f_1060_);
lean_closure_set(v___f_1062_, 1, v_cmp_1059_);
v___x_1063_ = ((lean_object*)(l_Std_TreeSet_Raw_partition___redArg___closed__0));
v_p_1064_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1062_, v___x_1063_, v_t_1061_);
v_fst_1065_ = lean_ctor_get(v_p_1064_, 0);
v_snd_1066_ = lean_ctor_get(v_p_1064_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_p_1064_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v_p_1064_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_snd_1066_);
lean_inc(v_fst_1065_);
lean_dec(v_p_1064_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_fst_1065_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_snd_1066_);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg___lam__0(lean_object* v_f_1074_, lean_object* v_x_1075_, lean_object* v_k_1076_, lean_object* v_v_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_apply_1(v_f_1074_, v_k_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg(lean_object* v_inst_1079_, lean_object* v_f_1080_, lean_object* v_t_1081_){
_start:
{
lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___f_1082_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1082_, 0, v_f_1080_);
v___x_1083_ = lean_box(0);
v___x_1084_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1079_, v___f_1082_, v___x_1083_, v_t_1081_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM(lean_object* v_00_u03b1_1085_, lean_object* v_cmp_1086_, lean_object* v_m_1087_, lean_object* v_inst_1088_, lean_object* v_f_1089_, lean_object* v_t_1090_){
_start:
{
lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___f_1091_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1091_, 0, v_f_1089_);
v___x_1092_ = lean_box(0);
v___x_1093_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1088_, v___f_1091_, v___x_1092_, v_t_1090_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___boxed(lean_object* v_00_u03b1_1094_, lean_object* v_cmp_1095_, lean_object* v_m_1096_, lean_object* v_inst_1097_, lean_object* v_f_1098_, lean_object* v_t_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Std_TreeSet_Raw_forM(v_00_u03b1_1094_, v_cmp_1095_, v_m_1096_, v_inst_1097_, v_f_1098_, v_t_1099_);
lean_dec_ref(v_cmp_1095_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__0(lean_object* v_f_1101_, lean_object* v_a_1102_, lean_object* v_b_1103_, lean_object* v_c_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_apply_2(v_f_1101_, v_a_1102_, v_c_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__1(lean_object* v_toPure_1106_, lean_object* v_____do__lift_1107_){
_start:
{
lean_object* v_a_1108_; lean_object* v___x_1109_; 
v_a_1108_ = lean_ctor_get(v_____do__lift_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref(v_____do__lift_1107_);
v___x_1109_ = lean_apply_2(v_toPure_1106_, lean_box(0), v_a_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg(lean_object* v_inst_1110_, lean_object* v_f_1111_, lean_object* v_init_1112_, lean_object* v_t_1113_){
_start:
{
lean_object* v_toApplicative_1114_; lean_object* v_toBind_1115_; lean_object* v_toPure_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; lean_object* v___f_1119_; lean_object* v___x_1120_; 
v_toApplicative_1114_ = lean_ctor_get(v_inst_1110_, 0);
v_toBind_1115_ = lean_ctor_get(v_inst_1110_, 1);
lean_inc(v_toBind_1115_);
v_toPure_1116_ = lean_ctor_get(v_toApplicative_1114_, 1);
lean_inc(v_toPure_1116_);
v___f_1117_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1117_, 0, v_f_1111_);
v___x_1118_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1110_, v___f_1117_, v_init_1112_, v_t_1113_);
v___f_1119_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1119_, 0, v_toPure_1116_);
v___x_1120_ = lean_apply_4(v_toBind_1115_, lean_box(0), lean_box(0), v___x_1118_, v___f_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn(lean_object* v_00_u03b1_1121_, lean_object* v_cmp_1122_, lean_object* v_00_u03b4_1123_, lean_object* v_m_1124_, lean_object* v_inst_1125_, lean_object* v_f_1126_, lean_object* v_init_1127_, lean_object* v_t_1128_){
_start:
{
lean_object* v_toApplicative_1129_; lean_object* v_toBind_1130_; lean_object* v_toPure_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; 
v_toApplicative_1129_ = lean_ctor_get(v_inst_1125_, 0);
v_toBind_1130_ = lean_ctor_get(v_inst_1125_, 1);
lean_inc(v_toBind_1130_);
v_toPure_1131_ = lean_ctor_get(v_toApplicative_1129_, 1);
lean_inc(v_toPure_1131_);
v___f_1132_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1132_, 0, v_f_1126_);
v___x_1133_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1125_, v___f_1132_, v_init_1127_, v_t_1128_);
v___f_1134_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1134_, 0, v_toPure_1131_);
v___x_1135_ = lean_apply_4(v_toBind_1130_, lean_box(0), lean_box(0), v___x_1133_, v___f_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_cmp_1137_, lean_object* v_00_u03b4_1138_, lean_object* v_m_1139_, lean_object* v_inst_1140_, lean_object* v_f_1141_, lean_object* v_init_1142_, lean_object* v_t_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_TreeSet_Raw_forIn(v_00_u03b1_1136_, v_cmp_1137_, v_00_u03b4_1138_, v_m_1139_, v_inst_1140_, v_f_1141_, v_init_1142_, v_t_1143_);
lean_dec_ref(v_cmp_1137_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1(lean_object* v_inst_1145_, lean_object* v_t_1146_, lean_object* v_f_1147_){
_start:
{
lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___f_1148_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1148_, 0, v_f_1147_);
v___x_1149_ = lean_box(0);
v___x_1150_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1145_, v___f_1148_, v___x_1149_, v_t_1146_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_1151_){
_start:
{
lean_object* v___f_1152_; 
v___f_1152_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1152_, 0, v_inst_1151_);
return v___f_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_1153_, lean_object* v_cmp_1154_, lean_object* v_m_1155_, lean_object* v_inst_1156_){
_start:
{
lean_object* v___f_1157_; 
v___f_1157_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1157_, 0, v_inst_1156_);
return v___f_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_cmp_1159_, lean_object* v_m_1160_, lean_object* v_inst_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_TreeSet_Raw_instForMOfMonad(v_00_u03b1_1158_, v_cmp_1159_, v_m_1160_, v_inst_1161_);
lean_dec_ref(v_cmp_1159_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2(lean_object* v_inst_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_t_1165_, lean_object* v_init_1166_, lean_object* v_f_1167_){
_start:
{
lean_object* v_toApplicative_1168_; lean_object* v_toBind_1169_; lean_object* v_toPure_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; lean_object* v___f_1173_; lean_object* v___x_1174_; 
v_toApplicative_1168_ = lean_ctor_get(v_inst_1163_, 0);
v_toBind_1169_ = lean_ctor_get(v_inst_1163_, 1);
lean_inc(v_toBind_1169_);
v_toPure_1170_ = lean_ctor_get(v_toApplicative_1168_, 1);
lean_inc(v_toPure_1170_);
v___f_1171_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1171_, 0, v_f_1167_);
v___x_1172_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1163_, v___f_1171_, v_init_1166_, v_t_1165_);
v___f_1173_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1173_, 0, v_toPure_1170_);
v___x_1174_ = lean_apply_4(v_toBind_1169_, lean_box(0), lean_box(0), v___x_1172_, v___f_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_1175_){
_start:
{
lean_object* v___f_1176_; 
v___f_1176_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1176_, 0, v_inst_1175_);
return v___f_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_1177_, lean_object* v_cmp_1178_, lean_object* v_m_1179_, lean_object* v_inst_1180_){
_start:
{
lean_object* v___f_1181_; 
v___f_1181_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1181_, 0, v_inst_1180_);
return v___f_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_cmp_1183_, lean_object* v_m_1184_, lean_object* v_inst_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Std_TreeSet_Raw_instForInOfMonad(v_00_u03b1_1182_, v_cmp_1183_, v_m_1184_, v_inst_1185_);
lean_dec_ref(v_cmp_1183_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0(lean_object* v_p_1187_, lean_object* v___x_1188_, lean_object* v___x_1189_, lean_object* v_a_1190_, lean_object* v_b_1191_, lean_object* v_acc_1192_){
_start:
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = lean_apply_1(v_p_1187_, v_a_1190_);
v___x_1194_ = lean_unbox(v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1188_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec_ref(v___x_1188_);
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1193_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1189_);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v_a_1202_, lean_object* v_b_1203_, lean_object* v_acc_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Std_TreeSet_Raw_any___redArg___lam__0(v_p_1199_, v___x_1200_, v___x_1201_, v_a_1202_, v_b_1203_, v_acc_1204_);
lean_dec_ref(v_acc_1204_);
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_any___redArg(lean_object* v_t_1209_, lean_object* v_p_1210_){
_start:
{
lean_object* v___y_1212_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; lean_object* v_a_1222_; 
v___x_1217_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1218_ = lean_box(0);
v___x_1219_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1220_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1220_, 0, v_p_1210_);
lean_closure_set(v___f_1220_, 1, v___x_1219_);
lean_closure_set(v___f_1220_, 2, v___x_1218_);
v___x_1221_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1217_, v___f_1220_, v___x_1219_, v_t_1209_);
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___y_1212_ = v_a_1222_;
goto v___jp_1211_;
v___jp_1211_:
{
lean_object* v_fst_1213_; 
v_fst_1213_ = lean_ctor_get(v___y_1212_, 0);
lean_inc(v_fst_1213_);
lean_dec_ref(v___y_1212_);
if (lean_obj_tag(v_fst_1213_) == 0)
{
uint8_t v___x_1214_; 
v___x_1214_ = 0;
return v___x_1214_;
}
else
{
lean_object* v_val_1215_; uint8_t v___x_1216_; 
v_val_1215_ = lean_ctor_get(v_fst_1213_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v_fst_1213_, 1);
v___x_1216_ = lean_unbox(v_val_1215_);
lean_dec(v_val_1215_);
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___boxed(lean_object* v_t_1223_, lean_object* v_p_1224_){
_start:
{
uint8_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l_Std_TreeSet_Raw_any___redArg(v_t_1223_, v_p_1224_);
v_r_1226_ = lean_box(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_any(lean_object* v_00_u03b1_1227_, lean_object* v_cmp_1228_, lean_object* v_t_1229_, lean_object* v_p_1230_){
_start:
{
lean_object* v___y_1232_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; lean_object* v_a_1242_; 
v___x_1237_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1238_ = lean_box(0);
v___x_1239_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1240_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1240_, 0, v_p_1230_);
lean_closure_set(v___f_1240_, 1, v___x_1239_);
lean_closure_set(v___f_1240_, 2, v___x_1238_);
v___x_1241_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1237_, v___f_1240_, v___x_1239_, v_t_1229_);
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___y_1232_ = v_a_1242_;
goto v___jp_1231_;
v___jp_1231_:
{
lean_object* v_fst_1233_; 
v_fst_1233_ = lean_ctor_get(v___y_1232_, 0);
lean_inc(v_fst_1233_);
lean_dec_ref(v___y_1232_);
if (lean_obj_tag(v_fst_1233_) == 0)
{
uint8_t v___x_1234_; 
v___x_1234_ = 0;
return v___x_1234_;
}
else
{
lean_object* v_val_1235_; uint8_t v___x_1236_; 
v_val_1235_ = lean_ctor_get(v_fst_1233_, 0);
lean_inc(v_val_1235_);
lean_dec_ref_known(v_fst_1233_, 1);
v___x_1236_ = lean_unbox(v_val_1235_);
lean_dec(v_val_1235_);
return v___x_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___boxed(lean_object* v_00_u03b1_1243_, lean_object* v_cmp_1244_, lean_object* v_t_1245_, lean_object* v_p_1246_){
_start:
{
uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_res_1247_ = l_Std_TreeSet_Raw_any(v_00_u03b1_1243_, v_cmp_1244_, v_t_1245_, v_p_1246_);
lean_dec_ref(v_cmp_1244_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0(lean_object* v_p_1249_, lean_object* v___x_1250_, lean_object* v___x_1251_, lean_object* v_a_1252_, lean_object* v_b_1253_, lean_object* v_acc_1254_){
_start:
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = lean_apply_1(v_p_1249_, v_a_1252_);
v___x_1256_ = lean_unbox(v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec_ref(v___x_1251_);
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v___x_1250_);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
else
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1251_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1261_, lean_object* v___x_1262_, lean_object* v___x_1263_, lean_object* v_a_1264_, lean_object* v_b_1265_, lean_object* v_acc_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_TreeSet_Raw_all___redArg___lam__0(v_p_1261_, v___x_1262_, v___x_1263_, v_a_1264_, v_b_1265_, v_acc_1266_);
lean_dec_ref(v_acc_1266_);
return v_res_1267_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_all___redArg(lean_object* v_t_1268_, lean_object* v_p_1269_){
_start:
{
lean_object* v___y_1271_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___f_1279_; lean_object* v___x_1280_; lean_object* v_a_1281_; 
v___x_1276_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1277_ = lean_box(0);
v___x_1278_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1279_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1279_, 0, v_p_1269_);
lean_closure_set(v___f_1279_, 1, v___x_1277_);
lean_closure_set(v___f_1279_, 2, v___x_1278_);
v___x_1280_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1276_, v___f_1279_, v___x_1278_, v_t_1268_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___y_1271_ = v_a_1281_;
goto v___jp_1270_;
v___jp_1270_:
{
lean_object* v_fst_1272_; 
v_fst_1272_ = lean_ctor_get(v___y_1271_, 0);
lean_inc(v_fst_1272_);
lean_dec_ref(v___y_1271_);
if (lean_obj_tag(v_fst_1272_) == 0)
{
uint8_t v___x_1273_; 
v___x_1273_ = 1;
return v___x_1273_;
}
else
{
lean_object* v_val_1274_; uint8_t v___x_1275_; 
v_val_1274_ = lean_ctor_get(v_fst_1272_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v_fst_1272_, 1);
v___x_1275_ = lean_unbox(v_val_1274_);
lean_dec(v_val_1274_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___boxed(lean_object* v_t_1282_, lean_object* v_p_1283_){
_start:
{
uint8_t v_res_1284_; lean_object* v_r_1285_; 
v_res_1284_ = l_Std_TreeSet_Raw_all___redArg(v_t_1282_, v_p_1283_);
v_r_1285_ = lean_box(v_res_1284_);
return v_r_1285_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_all(lean_object* v_00_u03b1_1286_, lean_object* v_cmp_1287_, lean_object* v_t_1288_, lean_object* v_p_1289_){
_start:
{
lean_object* v___y_1291_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___f_1299_; lean_object* v___x_1300_; lean_object* v_a_1301_; 
v___x_1296_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1297_ = lean_box(0);
v___x_1298_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1299_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1299_, 0, v_p_1289_);
lean_closure_set(v___f_1299_, 1, v___x_1297_);
lean_closure_set(v___f_1299_, 2, v___x_1298_);
v___x_1300_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1296_, v___f_1299_, v___x_1298_, v_t_1288_);
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___y_1291_ = v_a_1301_;
goto v___jp_1290_;
v___jp_1290_:
{
lean_object* v_fst_1292_; 
v_fst_1292_ = lean_ctor_get(v___y_1291_, 0);
lean_inc(v_fst_1292_);
lean_dec_ref(v___y_1291_);
if (lean_obj_tag(v_fst_1292_) == 0)
{
uint8_t v___x_1293_; 
v___x_1293_ = 1;
return v___x_1293_;
}
else
{
lean_object* v_val_1294_; uint8_t v___x_1295_; 
v_val_1294_ = lean_ctor_get(v_fst_1292_, 0);
lean_inc(v_val_1294_);
lean_dec_ref_known(v_fst_1292_, 1);
v___x_1295_ = lean_unbox(v_val_1294_);
lean_dec(v_val_1294_);
return v___x_1295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___boxed(lean_object* v_00_u03b1_1302_, lean_object* v_cmp_1303_, lean_object* v_t_1304_, lean_object* v_p_1305_){
_start:
{
uint8_t v_res_1306_; lean_object* v_r_1307_; 
v_res_1306_ = l_Std_TreeSet_Raw_all(v_00_u03b1_1302_, v_cmp_1303_, v_t_1304_, v_p_1305_);
lean_dec_ref(v_cmp_1303_);
v_r_1307_ = lean_box(v_res_1306_);
return v_r_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg___lam__0(lean_object* v_x1_1308_, lean_object* v_x2_1309_, lean_object* v_x3_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1311_, 0, v_x1_1308_);
lean_ctor_set(v___x_1311_, 1, v_x3_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg(lean_object* v_t_1313_){
_start:
{
lean_object* v___f_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___f_1314_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___x_1315_ = lean_box(0);
v___x_1316_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1317_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1316_, v___f_1314_, v___x_1315_, v_t_1313_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList(lean_object* v_00_u03b1_1318_, lean_object* v_cmp_1319_, lean_object* v_t_1320_){
_start:
{
lean_object* v___f_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___f_1321_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___x_1322_ = lean_box(0);
v___x_1323_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1324_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1323_, v___f_1321_, v___x_1322_, v_t_1320_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___boxed(lean_object* v_00_u03b1_1325_, lean_object* v_cmp_1326_, lean_object* v_t_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Std_TreeSet_Raw_toList(v_00_u03b1_1325_, v_cmp_1326_, v_t_1327_);
lean_dec_ref(v_cmp_1326_);
return v_res_1328_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__25, &l_Std_TreeSet_Raw___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw___auto__1___closed__25);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg___lam__0(lean_object* v_cmp_1330_, lean_object* v_a_1331_, lean_object* v_x_1332_, lean_object* v___y_1333_){
_start:
{
uint8_t v___x_1334_; 
lean_inc(v___y_1333_);
lean_inc(v_a_1331_);
lean_inc_ref(v_cmp_1330_);
v___x_1334_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1330_, v_a_1331_, v___y_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_box(0);
v___x_1336_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1330_, v_a_1331_, v___x_1335_, v___y_1333_);
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; 
lean_dec(v_a_1331_);
lean_dec_ref(v_cmp_1330_);
v___x_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___y_1333_);
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg(lean_object* v_l_1339_, lean_object* v_cmp_1340_){
_start:
{
lean_object* v___f_1341_; lean_object* v___x_1342_; lean_object* v_r_1343_; lean_object* v___x_1344_; 
v___f_1341_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1341_, 0, v_cmp_1340_);
v___x_1342_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1343_ = lean_box(1);
v___x_1344_ = l_List_forIn_x27_loop___redArg(v___x_1342_, v___f_1341_, v_l_1339_, v_r_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg___boxed(lean_object* v_l_1345_, lean_object* v_cmp_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_TreeSet_Raw_ofList___redArg(v_l_1345_, v_cmp_1346_);
lean_dec(v_l_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList(lean_object* v_00_u03b1_1348_, lean_object* v_l_1349_, lean_object* v_cmp_1350_){
_start:
{
lean_object* v___f_1351_; lean_object* v___x_1352_; lean_object* v_r_1353_; lean_object* v___x_1354_; 
v___f_1351_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1351_, 0, v_cmp_1350_);
v___x_1352_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1353_ = lean_box(1);
v___x_1354_ = l_List_forIn_x27_loop___redArg(v___x_1352_, v___f_1351_, v_l_1349_, v_r_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_l_1356_, lean_object* v_cmp_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Std_TreeSet_Raw_ofList(v_00_u03b1_1355_, v_l_1356_, v_cmp_1357_);
lean_dec(v_l_1356_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg___lam__0(lean_object* v_c_1359_, lean_object* v_a_1360_, lean_object* v_x_1361_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_array_push(v_c_1359_, v_a_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg(lean_object* v_t_1366_){
_start:
{
lean_object* v___f_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___f_1367_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__0));
v___x_1368_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__1));
v___x_1369_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1367_, v___x_1368_, v_t_1366_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray(lean_object* v_00_u03b1_1370_, lean_object* v_cmp_1371_, lean_object* v_t_1372_){
_start:
{
lean_object* v___f_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___f_1373_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__0));
v___x_1374_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__1));
v___x_1375_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1373_, v___x_1374_, v_t_1372_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___boxed(lean_object* v_00_u03b1_1376_, lean_object* v_cmp_1377_, lean_object* v_t_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_TreeSet_Raw_toArray(v_00_u03b1_1376_, v_cmp_1377_, v_t_1378_);
lean_dec_ref(v_cmp_1377_);
return v_res_1379_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__25, &l_Std_TreeSet_Raw___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw___auto__1___closed__25);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray___redArg(lean_object* v_a_1381_, lean_object* v_cmp_1382_){
_start:
{
lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v_r_1385_; size_t v_sz_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v___f_1383_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1383_, 0, v_cmp_1382_);
v___x_1384_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1385_ = lean_box(1);
v_sz_1386_ = lean_array_size(v_a_1381_);
v___x_1387_ = ((size_t)0ULL);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1384_, v_a_1381_, v___f_1383_, v_sz_1386_, v___x_1387_, v_r_1385_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray(lean_object* v_00_u03b1_1389_, lean_object* v_a_1390_, lean_object* v_cmp_1391_){
_start:
{
lean_object* v___f_1392_; lean_object* v___x_1393_; lean_object* v_r_1394_; size_t v_sz_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v___f_1392_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1392_, 0, v_cmp_1391_);
v___x_1393_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1394_ = lean_box(1);
v_sz_1395_ = lean_array_size(v_a_1390_);
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1393_, v_a_1390_, v___f_1392_, v_sz_1395_, v___x_1396_, v_r_1394_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0(lean_object* v_b_u2082_1400_, lean_object* v_x_1401_){
_start:
{
if (lean_obj_tag(v_x_1401_) == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_b_u2082_1400_);
return v___x_1402_;
}
else
{
lean_object* v___x_1403_; 
v___x_1403_ = ((lean_object*)(l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0));
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1404_, lean_object* v_x_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Std_TreeSet_Raw_merge___redArg___lam__0(v_b_u2082_1404_, v_x_1405_);
lean_dec(v_x_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__1(lean_object* v_cmp_1407_, lean_object* v_t_1408_, lean_object* v_a_1409_, lean_object* v_b_u2082_1410_){
_start:
{
lean_object* v___f_1411_; lean_object* v___x_1412_; 
v___f_1411_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1411_, 0, v_b_u2082_1410_);
v___x_1412_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_1407_, v_a_1409_, v___f_1411_, v_t_1408_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg(lean_object* v_cmp_1413_, lean_object* v_t_u2081_1414_, lean_object* v_t_u2082_1415_){
_start:
{
lean_object* v___f_1416_; lean_object* v___x_1417_; 
v___f_1416_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1416_, 0, v_cmp_1413_);
v___x_1417_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1416_, v_t_u2081_1414_, v_t_u2082_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge(lean_object* v_00_u03b1_1418_, lean_object* v_cmp_1419_, lean_object* v_t_u2081_1420_, lean_object* v_t_u2082_1421_){
_start:
{
lean_object* v___f_1422_; lean_object* v___x_1423_; 
v___f_1422_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1422_, 0, v_cmp_1419_);
v___x_1423_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1422_, v_t_u2081_1420_, v_t_u2082_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_1424_, lean_object* v_a_1425_, lean_object* v_____s_1426_){
_start:
{
uint8_t v___x_1427_; 
lean_inc(v_____s_1426_);
lean_inc(v_a_1425_);
lean_inc_ref(v_cmp_1424_);
v___x_1427_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1424_, v_a_1425_, v_____s_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = lean_box(0);
v___x_1429_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1424_, v_a_1425_, v___x_1428_, v_____s_1426_);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; 
lean_dec(v_a_1425_);
lean_dec_ref(v_cmp_1424_);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_____s_1426_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg(lean_object* v_cmp_1432_, lean_object* v_inst_1433_, lean_object* v_t_1434_, lean_object* v_l_1435_){
_start:
{
lean_object* v___f_1436_; lean_object* v___x_1437_; 
v___f_1436_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1436_, 0, v_cmp_1432_);
v___x_1437_ = lean_apply_4(v_inst_1433_, lean_box(0), v_l_1435_, v_t_1434_, v___f_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany(lean_object* v_00_u03b1_1438_, lean_object* v_cmp_1439_, lean_object* v_00_u03c1_1440_, lean_object* v_inst_1441_, lean_object* v_t_1442_, lean_object* v_l_1443_){
_start:
{
lean_object* v___f_1444_; lean_object* v___x_1445_; 
v___f_1444_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1444_, 0, v_cmp_1439_);
v___x_1445_ = lean_apply_4(v_inst_1441_, lean_box(0), v_l_1443_, v_t_1442_, v___f_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union___redArg(lean_object* v_cmp_1446_, lean_object* v_t_u2081_1447_, lean_object* v_t_u2082_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_1446_, v_t_u2081_1447_, v_t_u2082_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union(lean_object* v_00_u03b1_1450_, lean_object* v_cmp_1451_, lean_object* v_t_u2081_1452_, lean_object* v_t_u2082_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_1451_, v_t_u2081_1452_, v_t_u2082_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion___redArg(lean_object* v_cmp_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_union), 4, 2);
lean_closure_set(v___x_1456_, 0, lean_box(0));
lean_closure_set(v___x_1456_, 1, v_cmp_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion(lean_object* v_00_u03b1_1457_, lean_object* v_cmp_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_union), 4, 2);
lean_closure_set(v___x_1459_, 0, lean_box(0));
lean_closure_set(v___x_1459_, 1, v_cmp_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter___redArg(lean_object* v_cmp_1460_, lean_object* v_t_u2081_1461_, lean_object* v_t_u2082_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_1460_, v_t_u2081_1461_, v_t_u2082_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter(lean_object* v_00_u03b1_1464_, lean_object* v_cmp_1465_, lean_object* v_t_u2081_1466_, lean_object* v_t_u2082_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_1465_, v_t_u2081_1466_, v_t_u2082_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter___redArg(lean_object* v_cmp_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_inter), 4, 2);
lean_closure_set(v___x_1470_, 0, lean_box(0));
lean_closure_set(v___x_1470_, 1, v_cmp_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter(lean_object* v_00_u03b1_1471_, lean_object* v_cmp_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_inter), 4, 2);
lean_closure_set(v___x_1473_, 0, lean_box(0));
lean_closure_set(v___x_1473_, 1, v_cmp_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
if (lean_obj_tag(v_x_1474_) == 0)
{
if (lean_obj_tag(v_x_1475_) == 0)
{
uint8_t v___x_1476_; 
v___x_1476_ = 1;
return v___x_1476_;
}
else
{
uint8_t v___x_1477_; 
v___x_1477_ = 0;
return v___x_1477_;
}
}
else
{
if (lean_obj_tag(v_x_1475_) == 0)
{
uint8_t v___x_1478_; 
v___x_1478_ = 0;
return v___x_1478_;
}
else
{
uint8_t v___x_1479_; 
v___x_1479_ = 1;
return v___x_1479_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1480_, lean_object* v_x_1481_){
_start:
{
uint8_t v_res_1482_; lean_object* v_r_1483_; 
v_res_1482_ = l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v_x_1480_, v_x_1481_);
lean_dec(v_x_1481_);
lean_dec(v_x_1480_);
v_r_1483_ = lean_box(v_res_1482_);
return v_r_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_cmp_1484_, lean_object* v_t_1485_, lean_object* v_k_1486_){
_start:
{
if (lean_obj_tag(v_t_1485_) == 0)
{
lean_object* v_k_1487_; lean_object* v_v_1488_; lean_object* v_l_1489_; lean_object* v_r_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v_k_1487_ = lean_ctor_get(v_t_1485_, 1);
lean_inc(v_k_1487_);
v_v_1488_ = lean_ctor_get(v_t_1485_, 2);
lean_inc(v_v_1488_);
v_l_1489_ = lean_ctor_get(v_t_1485_, 3);
lean_inc(v_l_1489_);
v_r_1490_ = lean_ctor_get(v_t_1485_, 4);
lean_inc(v_r_1490_);
lean_dec_ref_known(v_t_1485_, 5);
lean_inc_ref(v_cmp_1484_);
lean_inc(v_k_1486_);
v___x_1491_ = lean_apply_2(v_cmp_1484_, v_k_1486_, v_k_1487_);
v___x_1492_ = lean_unbox(v___x_1491_);
switch(v___x_1492_)
{
case 0:
{
lean_dec(v_r_1490_);
lean_dec(v_v_1488_);
v_t_1485_ = v_l_1489_;
goto _start;
}
case 1:
{
lean_object* v___x_1494_; 
lean_dec(v_r_1490_);
lean_dec(v_l_1489_);
lean_dec(v_k_1486_);
lean_dec_ref(v_cmp_1484_);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_v_1488_);
return v___x_1494_;
}
default: 
{
lean_dec(v_l_1489_);
lean_dec(v_v_1488_);
v_t_1485_ = v_r_1490_;
goto _start;
}
}
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_k_1486_);
lean_dec_ref(v_cmp_1484_);
v___x_1496_ = lean_box(0);
return v___x_1496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v_cmp_1499_, lean_object* v_t_u2082_1500_, lean_object* v_init_1501_, lean_object* v_x_1502_){
_start:
{
lean_object* v___x_1503_; uint8_t v___y_1505_; lean_object* v___x_1510_; uint8_t v___y_1512_; uint8_t v___x_1530_; 
v___x_1503_ = lean_box(0);
v___x_1510_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___x_1530_ = lean_nat_dec_eq(v___y_1497_, v___y_1498_);
if (v___x_1530_ == 0)
{
uint8_t v___x_1531_; 
v___x_1531_ = 1;
v___y_1512_ = v___x_1531_;
goto v___jp_1511_;
}
else
{
uint8_t v___x_1532_; 
v___x_1532_ = 0;
v___y_1512_ = v___x_1532_;
goto v___jp_1511_;
}
v___jp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1506_ = lean_box(v___y_1505_);
v___x_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___x_1503_);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
v___jp_1511_:
{
if (lean_obj_tag(v_x_1502_) == 0)
{
lean_object* v_k_1513_; lean_object* v_v_1514_; lean_object* v_l_1515_; lean_object* v_r_1516_; lean_object* v___x_1517_; 
v_k_1513_ = lean_ctor_get(v_x_1502_, 1);
lean_inc(v_k_1513_);
v_v_1514_ = lean_ctor_get(v_x_1502_, 2);
lean_inc(v_v_1514_);
v_l_1515_ = lean_ctor_get(v_x_1502_, 3);
lean_inc(v_l_1515_);
v_r_1516_ = lean_ctor_get(v_x_1502_, 4);
lean_inc(v_r_1516_);
lean_dec_ref_known(v_x_1502_, 5);
lean_inc(v_t_u2082_1500_);
lean_inc_ref(v_cmp_1499_);
v___x_1517_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1497_, v___y_1498_, v_cmp_1499_, v_t_u2082_1500_, v_init_1501_, v_l_1515_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_dec(v_r_1516_);
lean_dec(v_v_1514_);
lean_dec(v_k_1513_);
lean_dec(v_t_u2082_1500_);
lean_dec_ref(v_cmp_1499_);
return v___x_1517_;
}
else
{
lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1527_; 
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v___x_1517_, 0);
lean_dec(v_unused_1528_);
v___x_1519_ = v___x_1517_;
v_isShared_1520_ = v_isSharedCheck_1527_;
goto v_resetjp_1518_;
}
else
{
lean_dec(v___x_1517_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1527_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
lean_inc(v_t_u2082_1500_);
lean_inc_ref(v_cmp_1499_);
v___x_1521_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1499_, v_t_u2082_1500_, v_k_1513_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v_v_1514_);
v___x_1523_ = v___x_1519_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_v_1514_);
v___x_1523_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
uint8_t v___x_1524_; 
v___x_1524_ = l_instBEqOption_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v___x_1521_, v___x_1523_);
lean_dec_ref(v___x_1523_);
lean_dec(v___x_1521_);
if (v___x_1524_ == 0)
{
lean_dec(v_r_1516_);
lean_dec(v_t_u2082_1500_);
lean_dec_ref(v_cmp_1499_);
v___y_1505_ = v___y_1512_;
goto v___jp_1504_;
}
else
{
if (v___y_1512_ == 0)
{
v_init_1501_ = v___x_1510_;
v_x_1502_ = v_r_1516_;
goto _start;
}
else
{
lean_dec(v_r_1516_);
lean_dec(v_t_u2082_1500_);
lean_dec_ref(v_cmp_1499_);
v___y_1505_ = v___y_1512_;
goto v___jp_1504_;
}
}
}
}
}
}
else
{
lean_object* v___x_1529_; 
lean_dec(v_t_u2082_1500_);
lean_dec_ref(v_cmp_1499_);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v_init_1501_);
return v___x_1529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v_cmp_1535_, lean_object* v_t_u2082_1536_, lean_object* v_init_1537_, lean_object* v_x_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1533_, v___y_1534_, v_cmp_1535_, v_t_u2082_1536_, v_init_1537_, v_x_1538_);
lean_dec(v___y_1534_);
lean_dec(v___y_1533_);
return v_res_1539_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_1540_, lean_object* v_t_u2081_1541_, lean_object* v_t_u2082_1542_){
_start:
{
lean_object* v___y_1544_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1557_; 
if (lean_obj_tag(v_t_u2081_1541_) == 0)
{
lean_object* v_size_1560_; 
v_size_1560_ = lean_ctor_get(v_t_u2081_1541_, 0);
lean_inc(v_size_1560_);
v___y_1557_ = v_size_1560_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_unsigned_to_nat(0u);
v___y_1557_ = v___x_1561_;
goto v___jp_1556_;
}
v___jp_1543_:
{
lean_object* v_fst_1545_; 
v_fst_1545_ = lean_ctor_get(v___y_1544_, 0);
lean_inc(v_fst_1545_);
lean_dec_ref(v___y_1544_);
if (lean_obj_tag(v_fst_1545_) == 0)
{
uint8_t v___x_1546_; 
v___x_1546_ = 1;
return v___x_1546_;
}
else
{
lean_object* v_val_1547_; uint8_t v___x_1548_; 
v_val_1547_ = lean_ctor_get(v_fst_1545_, 0);
lean_inc(v_val_1547_);
lean_dec_ref_known(v_fst_1545_, 1);
v___x_1548_ = lean_unbox(v_val_1547_);
lean_dec(v_val_1547_);
return v___x_1548_;
}
}
v___jp_1549_:
{
uint8_t v___x_1552_; 
v___x_1552_ = lean_nat_dec_eq(v___y_1550_, v___y_1551_);
if (v___x_1552_ == 0)
{
lean_dec(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec(v_t_u2082_1542_);
lean_dec(v_t_u2081_1541_);
lean_dec_ref(v_cmp_1540_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v_a_1555_; 
v___x_1553_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___x_1554_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1550_, v___y_1551_, v_cmp_1540_, v_t_u2082_1542_, v___x_1553_, v_t_u2081_1541_);
lean_dec(v___y_1551_);
lean_dec(v___y_1550_);
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1554_);
v___y_1544_ = v_a_1555_;
goto v___jp_1543_;
}
}
v___jp_1556_:
{
if (lean_obj_tag(v_t_u2082_1542_) == 0)
{
lean_object* v_size_1558_; 
v_size_1558_ = lean_ctor_get(v_t_u2082_1542_, 0);
lean_inc(v_size_1558_);
v___y_1550_ = v___y_1557_;
v___y_1551_ = v_size_1558_;
goto v___jp_1549_;
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_unsigned_to_nat(0u);
v___y_1550_ = v___y_1557_;
v___y_1551_ = v___x_1559_;
goto v___jp_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_1562_, lean_object* v_t_u2081_1563_, lean_object* v_t_u2082_1564_){
_start:
{
uint8_t v_res_1565_; lean_object* v_r_1566_; 
v_res_1565_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1562_, v_t_u2081_1563_, v_t_u2082_1564_);
v_r_1566_ = lean_box(v_res_1565_);
return v_r_1566_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_beq___redArg(lean_object* v_cmp_1567_, lean_object* v_t_u2081_1568_, lean_object* v_t_u2082_1569_){
_start:
{
uint8_t v___x_1570_; 
v___x_1570_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1567_, v_t_u2081_1568_, v_t_u2082_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___redArg___boxed(lean_object* v_cmp_1571_, lean_object* v_t_u2081_1572_, lean_object* v_t_u2082_1573_){
_start:
{
uint8_t v_res_1574_; lean_object* v_r_1575_; 
v_res_1574_ = l_Std_TreeSet_Raw_beq___redArg(v_cmp_1571_, v_t_u2081_1572_, v_t_u2082_1573_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_beq(lean_object* v_00_u03b1_1576_, lean_object* v_cmp_1577_, lean_object* v_t_u2081_1578_, lean_object* v_t_u2082_1579_){
_start:
{
uint8_t v___x_1580_; 
v___x_1580_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1577_, v_t_u2081_1578_, v_t_u2082_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___boxed(lean_object* v_00_u03b1_1581_, lean_object* v_cmp_1582_, lean_object* v_t_u2081_1583_, lean_object* v_t_u2082_1584_){
_start:
{
uint8_t v_res_1585_; lean_object* v_r_1586_; 
v_res_1585_ = l_Std_TreeSet_Raw_beq(v_00_u03b1_1581_, v_cmp_1582_, v_t_u2081_1583_, v_t_u2082_1584_);
v_r_1586_ = lean_box(v_res_1585_);
return v_r_1586_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(lean_object* v_cmp_1587_, lean_object* v_t_u2081_1588_, lean_object* v_t_u2082_1589_){
_start:
{
uint8_t v___x_1590_; 
v___x_1590_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1587_, v_t_u2081_1588_, v_t_u2082_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg___boxed(lean_object* v_cmp_1591_, lean_object* v_t_u2081_1592_, lean_object* v_t_u2082_1593_){
_start:
{
uint8_t v_res_1594_; lean_object* v_r_1595_; 
v_res_1594_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(v_cmp_1591_, v_t_u2081_1592_, v_t_u2082_1593_);
v_r_1595_ = lean_box(v_res_1594_);
return v_r_1595_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(lean_object* v_00_u03b1_1596_, lean_object* v_cmp_1597_, lean_object* v_t_u2081_1598_, lean_object* v_t_u2082_1599_){
_start:
{
uint8_t v___x_1600_; 
v___x_1600_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1597_, v_t_u2081_1598_, v_t_u2082_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___boxed(lean_object* v_00_u03b1_1601_, lean_object* v_cmp_1602_, lean_object* v_t_u2081_1603_, lean_object* v_t_u2082_1604_){
_start:
{
uint8_t v_res_1605_; lean_object* v_r_1606_; 
v_res_1605_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(v_00_u03b1_1601_, v_cmp_1602_, v_t_u2081_1603_, v_t_u2082_1604_);
v_r_1606_ = lean_box(v_res_1605_);
return v_r_1606_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(lean_object* v_cmp_1607_, lean_object* v_t_u2081_1608_, lean_object* v_t_u2082_1609_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1607_, v_t_u2081_1608_, v_t_u2082_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_1611_, lean_object* v_t_u2081_1612_, lean_object* v_t_u2082_1613_){
_start:
{
uint8_t v_res_1614_; lean_object* v_r_1615_; 
v_res_1614_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(v_cmp_1611_, v_t_u2081_1612_, v_t_u2082_1613_);
v_r_1615_ = lean_box(v_res_1614_);
return v_r_1615_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(lean_object* v_00_u03b1_1616_, lean_object* v_cmp_1617_, lean_object* v_t_u2081_1618_, lean_object* v_t_u2082_1619_){
_start:
{
uint8_t v___x_1620_; 
v___x_1620_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1617_, v_t_u2081_1618_, v_t_u2082_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1621_, lean_object* v_cmp_1622_, lean_object* v_t_u2081_1623_, lean_object* v_t_u2082_1624_){
_start:
{
uint8_t v_res_1625_; lean_object* v_r_1626_; 
v_res_1625_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(v_00_u03b1_1621_, v_cmp_1622_, v_t_u2081_1623_, v_t_u2082_1624_);
v_r_1626_ = lean_box(v_res_1625_);
return v_r_1626_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1627_, lean_object* v_cmp_1628_, lean_object* v_t_u2081_1629_, lean_object* v_t_u2082_1630_){
_start:
{
uint8_t v___x_1631_; 
v___x_1631_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1628_, v_t_u2081_1629_, v_t_u2082_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1632_, lean_object* v_cmp_1633_, lean_object* v_t_u2081_1634_, lean_object* v_t_u2082_1635_){
_start:
{
uint8_t v_res_1636_; lean_object* v_r_1637_; 
v_res_1636_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(v_00_u03b1_1632_, v_cmp_1633_, v_t_u2081_1634_, v_t_u2082_1635_);
v_r_1637_ = lean_box(v_res_1636_);
return v_r_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1638_, lean_object* v_cmp_1639_, lean_object* v_00_u03b4_1640_, lean_object* v_t_1641_, lean_object* v_k_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1639_, v_t_1641_, v_k_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v_cmp_1647_, lean_object* v_t_u2082_1648_, lean_object* v_init_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1645_, v___y_1646_, v_cmp_1647_, v_t_u2082_1648_, v_init_1649_, v_x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v_cmp_1655_, lean_object* v_t_u2082_1656_, lean_object* v_init_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1652_, v___y_1653_, v___y_1654_, v_cmp_1655_, v_t_u2082_1656_, v_init_1657_, v_x_1658_);
lean_dec(v___y_1654_);
lean_dec(v___y_1653_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq___redArg(lean_object* v_cmp_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_beq___boxed), 4, 2);
lean_closure_set(v___x_1661_, 0, lean_box(0));
lean_closure_set(v___x_1661_, 1, v_cmp_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq(lean_object* v_00_u03b1_1662_, lean_object* v_cmp_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_beq___boxed), 4, 2);
lean_closure_set(v___x_1664_, 0, lean_box(0));
lean_closure_set(v___x_1664_, 1, v_cmp_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff___redArg(lean_object* v_cmp_1665_, lean_object* v_t_u2081_1666_, lean_object* v_t_u2082_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_1665_, v_t_u2081_1666_, v_t_u2082_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff(lean_object* v_00_u03b1_1669_, lean_object* v_cmp_1670_, lean_object* v_t_u2081_1671_, lean_object* v_t_u2082_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_1670_, v_t_u2081_1671_, v_t_u2082_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff___redArg(lean_object* v_cmp_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_diff), 4, 2);
lean_closure_set(v___x_1675_, 0, lean_box(0));
lean_closure_set(v___x_1675_, 1, v_cmp_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff(lean_object* v_00_u03b1_1676_, lean_object* v_cmp_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_diff), 4, 2);
lean_closure_set(v___x_1678_, 0, lean_box(0));
lean_closure_set(v___x_1678_, 1, v_cmp_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_1679_, lean_object* v_a_1680_, lean_object* v_____s_1681_){
_start:
{
lean_object* v_r_1682_; lean_object* v___x_1683_; 
v_r_1682_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_1679_, v_a_1680_, v_____s_1681_);
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_r_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg(lean_object* v_cmp_1684_, lean_object* v_inst_1685_, lean_object* v_t_1686_, lean_object* v_l_1687_){
_start:
{
lean_object* v___f_1688_; lean_object* v___x_1689_; 
v___f_1688_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1688_, 0, v_cmp_1684_);
v___x_1689_ = lean_apply_4(v_inst_1685_, lean_box(0), v_l_1687_, v_t_1686_, v___f_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany(lean_object* v_00_u03b1_1690_, lean_object* v_cmp_1691_, lean_object* v_00_u03c1_1692_, lean_object* v_inst_1693_, lean_object* v_t_1694_, lean_object* v_l_1695_){
_start:
{
lean_object* v___f_1696_; lean_object* v___x_1697_; 
v___f_1696_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1696_, 0, v_cmp_1691_);
v___x_1697_ = lean_apply_4(v_inst_1693_, lean_box(0), v_l_1695_, v_t_1694_, v___f_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1(lean_object* v___f_1701_, lean_object* v_inst_1702_, lean_object* v_m_1703_, lean_object* v_prec_1704_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1705_ = ((lean_object*)(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1));
v___x_1706_ = lean_box(0);
v___x_1707_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1708_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1707_, v___f_1701_, v___x_1706_, v_m_1703_);
v___x_1709_ = l_List_repr___redArg(v_inst_1702_, v___x_1708_);
v___x_1710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1705_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = l_Repr_addAppParen(v___x_1710_, v_prec_1704_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_1712_, lean_object* v_inst_1713_, lean_object* v_m_1714_, lean_object* v_prec_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Std_TreeSet_Raw_instRepr___redArg___lam__1(v___f_1712_, v_inst_1713_, v_m_1714_, v_prec_1715_);
lean_dec(v_prec_1715_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg(lean_object* v_inst_1717_){
_start:
{
lean_object* v___f_1718_; lean_object* v___f_1719_; 
v___f_1718_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___f_1719_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1719_, 0, v___f_1718_);
lean_closure_set(v___f_1719_, 1, v_inst_1717_);
return v___f_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr(lean_object* v_00_u03b1_1720_, lean_object* v_cmp_1721_, lean_object* v_inst_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Std_TreeSet_Raw_instRepr___redArg(v_inst_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_cmp_1725_, lean_object* v_inst_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Std_TreeSet_Raw_instRepr(v_00_u03b1_1724_, v_cmp_1725_, v_inst_1726_);
lean_dec_ref(v_cmp_1725_);
return v_res_1727_;
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
