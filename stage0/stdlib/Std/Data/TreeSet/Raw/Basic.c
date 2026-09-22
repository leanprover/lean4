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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg(){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg___boxed(lean_object* v___dummy_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_TreeSet_Raw_instCoeWFWFUnitInner___redArg();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner(lean_object* v_00_u03b1_79_, lean_object* v_cmp_80_, lean_object* v_t_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instCoeWFWFUnitInner___boxed(lean_object* v_00_u03b1_83_, lean_object* v_cmp_84_, lean_object* v_t_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_TreeSet_Raw_instCoeWFWFUnitInner(v_00_u03b1_83_, v_cmp_84_, v_t_85_);
lean_dec(v_t_85_);
lean_dec_ref(v_cmp_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_empty___redArg(){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(1);
return v___x_88_;
}
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_box(1);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_TreeSet_Raw_instEmptyCollection___redArg();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection(lean_object* v_00_u03b1_101_, lean_object* v_cmp_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_box(1);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instEmptyCollection___boxed(lean_object* v_00_u03b1_104_, lean_object* v_cmp_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_TreeSet_Raw_instEmptyCollection(v_00_u03b1_104_, v_cmp_105_);
lean_dec_ref(v_cmp_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_box(1);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_TreeSet_Raw_instInhabited___redArg();
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited(lean_object* v_00_u03b1_111_, lean_object* v_cmp_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_box(1);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInhabited___boxed(lean_object* v_00_u03b1_114_, lean_object* v_cmp_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_TreeSet_Raw_instInhabited(v_00_u03b1_114_, v_cmp_115_);
lean_dec_ref(v_cmp_115_);
return v_res_116_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3));
v___x_157_ = l_String_toRawSubstring_x27(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(lean_object* v_x_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__4));
lean_inc(v_x_176_);
v___x_180_ = l_Lean_Syntax_isOfKind(v_x_176_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_x_176_);
v___x_181_ = lean_box(1);
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_178_);
return v___x_182_;
}
else
{
lean_object* v_quotContext_183_; lean_object* v_currMacroScope_184_; lean_object* v_ref_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_quotContext_183_ = lean_ctor_get(v_a_177_, 1);
v_currMacroScope_184_ = lean_ctor_get(v_a_177_, 2);
v_ref_185_ = lean_ctor_get(v_a_177_, 5);
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = l_Lean_Syntax_getArg(v_x_176_, v___x_186_);
v___x_188_ = lean_unsigned_to_nat(2u);
v___x_189_ = l_Lean_Syntax_getArg(v_x_176_, v___x_188_);
lean_dec(v_x_176_);
v___x_190_ = 0;
v___x_191_ = l_Lean_SourceInfo_fromRef(v_ref_185_, v___x_190_);
v___x_192_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2));
v___x_193_ = lean_obj_once(&l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4, &l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4_once, _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4);
v___x_194_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_184_);
lean_inc(v_quotContext_183_);
v___x_195_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_194_, v_currMacroScope_184_);
v___x_196_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10));
lean_inc_n(v___x_191_, 2);
v___x_197_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_197_, 0, v___x_191_);
lean_ctor_set(v___x_197_, 1, v___x_193_);
lean_ctor_set(v___x_197_, 2, v___x_195_);
lean_ctor_set(v___x_197_, 3, v___x_196_);
v___x_198_ = ((lean_object*)(l_Std_TreeSet_Raw___auto__1___closed__9));
v___x_199_ = l_Lean_Syntax_node2(v___x_191_, v___x_198_, v___x_187_, v___x_189_);
v___x_200_ = l_Lean_Syntax_node2(v___x_191_, v___x_192_, v___x_197_, v___x_199_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_a_178_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___boxed(lean_object* v_x_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(v_x_202_, v_a_203_, v_a_204_);
lean_dec_ref(v_a_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(lean_object* v_x_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2));
lean_inc(v_x_209_);
v___x_213_ = l_Lean_Syntax_isOfKind(v_x_209_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_x_209_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v_a_211_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = l_Lean_Syntax_getArg(v_x_209_, v___x_216_);
v___x_218_ = ((lean_object*)(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1));
lean_inc(v___x_217_);
v___x_219_ = l_Lean_Syntax_isOfKind(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v___x_217_);
lean_dec(v_x_209_);
v___x_220_ = lean_box(0);
v___x_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v_a_211_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = l_Lean_Syntax_getArg(v_x_209_, v___x_222_);
lean_dec(v_x_209_);
v___x_224_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_223_);
v___x_225_ = l_Lean_Syntax_matchesNull(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec(v___x_223_);
lean_dec(v___x_217_);
v___x_226_ = lean_box(0);
v___x_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_a_211_);
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_ref_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_228_ = l_Lean_Syntax_getArg(v___x_223_, v___x_216_);
v___x_229_ = l_Lean_Syntax_getArg(v___x_223_, v___x_222_);
lean_dec(v___x_223_);
v_ref_230_ = l_Lean_replaceRef(v___x_217_, v_a_210_);
lean_dec(v___x_217_);
v___x_231_ = 0;
v___x_232_ = l_Lean_SourceInfo_fromRef(v_ref_230_, v___x_231_);
lean_dec(v_ref_230_);
v___x_233_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__4));
v___x_234_ = ((lean_object*)(l_Std_TreeSet_Raw_term___x7em___00__closed__7));
lean_inc(v___x_232_);
v___x_235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_232_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = l_Lean_Syntax_node3(v___x_232_, v___x_233_, v___x_228_, v___x_235_, v___x_229_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v_a_211_);
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___boxed(lean_object* v_x_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(v_x_238_, v_a_239_, v_a_240_);
lean_dec(v_a_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert___redArg(lean_object* v_cmp_242_, lean_object* v_l_243_, lean_object* v_a_244_){
_start:
{
uint8_t v___x_245_; 
lean_inc(v_l_243_);
lean_inc(v_a_244_);
lean_inc_ref(v_cmp_242_);
v___x_245_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_242_, v_a_244_, v_l_243_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_box(0);
v___x_247_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_242_, v_a_244_, v___x_246_, v_l_243_);
return v___x_247_;
}
else
{
lean_dec(v_a_244_);
lean_dec_ref(v_cmp_242_);
return v_l_243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insert(lean_object* v_00_u03b1_248_, lean_object* v_cmp_249_, lean_object* v_l_250_, lean_object* v_a_251_){
_start:
{
uint8_t v___x_252_; 
lean_inc(v_l_250_);
lean_inc(v_a_251_);
lean_inc_ref(v_cmp_249_);
v___x_252_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_249_, v_a_251_, v_l_250_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_box(0);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_249_, v_a_251_, v___x_253_, v_l_250_);
return v___x_254_;
}
else
{
lean_dec(v_a_251_);
lean_dec_ref(v_cmp_249_);
return v_l_250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg___lam__0(lean_object* v_cmp_255_, lean_object* v_e_256_){
_start:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_box(1);
lean_inc(v_e_256_);
lean_inc_ref(v_cmp_255_);
v___x_258_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_255_, v_e_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(0);
v___x_260_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_255_, v_e_256_, v___x_259_, v___x_257_);
return v___x_260_;
}
else
{
lean_dec(v_e_256_);
lean_dec_ref(v_cmp_255_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton___redArg(lean_object* v_cmp_261_){
_start:
{
lean_object* v___f_262_; 
v___f_262_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_262_, 0, v_cmp_261_);
return v___f_262_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSingleton(lean_object* v_00_u03b1_263_, lean_object* v_cmp_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instSingleton___redArg___lam__0), 2, 1);
lean_closure_set(v___f_265_, 0, v_cmp_264_);
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg___lam__0(lean_object* v_cmp_266_, lean_object* v_e_267_, lean_object* v_s_268_){
_start:
{
uint8_t v___x_269_; 
lean_inc(v_s_268_);
lean_inc(v_e_267_);
lean_inc_ref(v_cmp_266_);
v___x_269_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_266_, v_e_267_, v_s_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_box(0);
v___x_271_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_266_, v_e_267_, v___x_270_, v_s_268_);
return v___x_271_;
}
else
{
lean_dec(v_e_267_);
lean_dec_ref(v_cmp_266_);
return v_s_268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert___redArg(lean_object* v_cmp_272_){
_start:
{
lean_object* v___f_273_; 
v___f_273_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_273_, 0, v_cmp_272_);
return v___f_273_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInsert(lean_object* v_00_u03b1_274_, lean_object* v_cmp_275_){
_start:
{
lean_object* v___f_276_; 
v___f_276_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instInsert___redArg___lam__0), 3, 1);
lean_closure_set(v___f_276_, 0, v_cmp_275_);
return v___f_276_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert___redArg(lean_object* v_cmp_277_, lean_object* v_t_278_, lean_object* v_a_279_){
_start:
{
uint8_t v___x_280_; 
lean_inc(v_t_278_);
lean_inc(v_a_279_);
lean_inc_ref(v_cmp_277_);
v___x_280_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_277_, v_a_279_, v_t_278_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_281_ = lean_box(0);
v___x_282_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_277_, v_a_279_, v___x_281_, v_t_278_);
v___x_283_ = lean_box(v___x_280_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_282_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec(v_a_279_);
lean_dec_ref(v_cmp_277_);
v___x_285_ = lean_box(v___x_280_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v_t_278_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_containsThenInsert(lean_object* v_00_u03b1_287_, lean_object* v_cmp_288_, lean_object* v_t_289_, lean_object* v_a_290_){
_start:
{
uint8_t v___x_291_; 
lean_inc(v_t_289_);
lean_inc(v_a_290_);
lean_inc_ref(v_cmp_288_);
v___x_291_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_288_, v_a_290_, v_t_289_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_box(0);
v___x_293_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_288_, v_a_290_, v___x_292_, v_t_289_);
v___x_294_ = lean_box(v___x_291_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
return v___x_295_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v_a_290_);
lean_dec_ref(v_cmp_288_);
v___x_296_ = lean_box(v___x_291_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_t_289_);
return v___x_297_;
}
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_contains___redArg(lean_object* v_cmp_298_, lean_object* v_l_299_, lean_object* v_a_300_){
_start:
{
uint8_t v___x_301_; 
v___x_301_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_298_, v_a_300_, v_l_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___redArg___boxed(lean_object* v_cmp_302_, lean_object* v_l_303_, lean_object* v_a_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_Std_TreeSet_Raw_contains___redArg(v_cmp_302_, v_l_303_, v_a_304_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_contains(lean_object* v_00_u03b1_307_, lean_object* v_cmp_308_, lean_object* v_l_309_, lean_object* v_a_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_308_, v_a_310_, v_l_309_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_contains___boxed(lean_object* v_00_u03b1_312_, lean_object* v_cmp_313_, lean_object* v_l_314_, lean_object* v_a_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Std_TreeSet_Raw_contains(v_00_u03b1_312_, v_cmp_313_, v_l_314_, v_a_315_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___redArg(){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_box(0);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___redArg___boxed(lean_object* v___dummy_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Std_TreeSet_Raw_instMembership___redArg();
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership(lean_object* v_00_u03b1_322_, lean_object* v_cmp_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_box(0);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instMembership___boxed(lean_object* v_00_u03b1_325_, lean_object* v_cmp_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_TreeSet_Raw_instMembership(v_00_u03b1_325_, v_cmp_326_);
lean_dec_ref(v_cmp_326_);
return v_res_327_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableMem___redArg(lean_object* v_cmp_328_, lean_object* v_t_329_, lean_object* v_a_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_328_, v_a_330_, v_t_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_332_, lean_object* v_t_333_, lean_object* v_a_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Std_TreeSet_Raw_instDecidableMem___redArg(v_cmp_332_, v_t_333_, v_a_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableMem(lean_object* v_00_u03b1_337_, lean_object* v_cmp_338_, lean_object* v_t_339_, lean_object* v_a_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_338_, v_a_340_, v_t_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_342_, lean_object* v_cmp_343_, lean_object* v_t_344_, lean_object* v_a_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Std_TreeSet_Raw_instDecidableMem(v_00_u03b1_342_, v_cmp_343_, v_t_344_, v_a_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg(lean_object* v_t_348_){
_start:
{
if (lean_obj_tag(v_t_348_) == 0)
{
lean_object* v_size_349_; 
v_size_349_ = lean_ctor_get(v_t_348_, 0);
lean_inc(v_size_349_);
return v_size_349_;
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_unsigned_to_nat(0u);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___redArg___boxed(lean_object* v_t_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_TreeSet_Raw_size___redArg(v_t_351_);
lean_dec(v_t_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size(lean_object* v_00_u03b1_353_, lean_object* v_cmp_354_, lean_object* v_t_355_){
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
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_size___boxed(lean_object* v_00_u03b1_358_, lean_object* v_cmp_359_, lean_object* v_t_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_TreeSet_Raw_size(v_00_u03b1_358_, v_cmp_359_, v_t_360_);
lean_dec(v_t_360_);
lean_dec_ref(v_cmp_359_);
return v_res_361_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_isEmpty___redArg(lean_object* v_t_362_){
_start:
{
if (lean_obj_tag(v_t_362_) == 0)
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = 1;
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___redArg___boxed(lean_object* v_t_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Std_TreeSet_Raw_isEmpty___redArg(v_t_365_);
lean_dec(v_t_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_isEmpty(lean_object* v_00_u03b1_368_, lean_object* v_cmp_369_, lean_object* v_t_370_){
_start:
{
if (lean_obj_tag(v_t_370_) == 0)
{
uint8_t v___x_371_; 
v___x_371_ = 0;
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
v___x_372_ = 1;
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_isEmpty___boxed(lean_object* v_00_u03b1_373_, lean_object* v_cmp_374_, lean_object* v_t_375_){
_start:
{
uint8_t v_res_376_; lean_object* v_r_377_; 
v_res_376_ = l_Std_TreeSet_Raw_isEmpty(v_00_u03b1_373_, v_cmp_374_, v_t_375_);
lean_dec(v_t_375_);
lean_dec_ref(v_cmp_374_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase___redArg(lean_object* v_cmp_378_, lean_object* v_t_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_378_, v_a_380_, v_t_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_erase(lean_object* v_00_u03b1_382_, lean_object* v_cmp_383_, lean_object* v_t_384_, lean_object* v_a_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_383_, v_a_385_, v_t_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f___redArg(lean_object* v_cmp_387_, lean_object* v_t_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_387_, v_t_388_, v_a_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x3f(lean_object* v_00_u03b1_391_, lean_object* v_cmp_392_, lean_object* v_t_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_392_, v_t_393_, v_a_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get___redArg(lean_object* v_cmp_396_, lean_object* v_t_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_396_, v_t_397_, v_a_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get(lean_object* v_00_u03b1_400_, lean_object* v_cmp_401_, lean_object* v_t_402_, lean_object* v_a_403_, lean_object* v_h_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_401_, v_t_402_, v_a_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___redArg(lean_object* v_cmp_406_, lean_object* v_inst_407_, lean_object* v_t_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_406_, v_t_408_, v_a_409_, v_inst_407_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___redArg___boxed(lean_object* v_cmp_411_, lean_object* v_inst_412_, lean_object* v_t_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_TreeSet_Raw_get_x21___redArg(v_cmp_411_, v_inst_412_, v_t_413_, v_a_414_);
lean_dec(v_inst_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21(lean_object* v_00_u03b1_416_, lean_object* v_cmp_417_, lean_object* v_inst_418_, lean_object* v_t_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_417_, v_t_419_, v_a_420_, v_inst_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_get_x21___boxed(lean_object* v_00_u03b1_422_, lean_object* v_cmp_423_, lean_object* v_inst_424_, lean_object* v_t_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_TreeSet_Raw_get_x21(v_00_u03b1_422_, v_cmp_423_, v_inst_424_, v_t_425_, v_a_426_);
lean_dec(v_inst_424_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg(lean_object* v_cmp_428_, lean_object* v_t_429_, lean_object* v_a_430_, lean_object* v_fallback_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_428_, v_t_429_, v_a_430_, v_fallback_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___redArg___boxed(lean_object* v_cmp_433_, lean_object* v_t_434_, lean_object* v_a_435_, lean_object* v_fallback_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_TreeSet_Raw_getD___redArg(v_cmp_433_, v_t_434_, v_a_435_, v_fallback_436_);
lean_dec(v_fallback_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD(lean_object* v_00_u03b1_438_, lean_object* v_cmp_439_, lean_object* v_t_440_, lean_object* v_a_441_, lean_object* v_fallback_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_439_, v_t_440_, v_a_441_, v_fallback_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getD___boxed(lean_object* v_00_u03b1_444_, lean_object* v_cmp_445_, lean_object* v_t_446_, lean_object* v_a_447_, lean_object* v_fallback_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_TreeSet_Raw_getD(v_00_u03b1_444_, v_cmp_445_, v_t_446_, v_a_447_, v_fallback_448_);
lean_dec(v_fallback_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg(lean_object* v_t_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___redArg___boxed(lean_object* v_t_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_TreeSet_Raw_min_x3f___redArg(v_t_452_);
lean_dec(v_t_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f(lean_object* v_00_u03b1_454_, lean_object* v_cmp_455_, lean_object* v_t_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x3f___boxed(lean_object* v_00_u03b1_458_, lean_object* v_cmp_459_, lean_object* v_t_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_TreeSet_Raw_min_x3f(v_00_u03b1_458_, v_cmp_459_, v_t_460_);
lean_dec(v_t_460_);
lean_dec_ref(v_cmp_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg(lean_object* v_inst_462_, lean_object* v_t_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_462_, v_t_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___redArg___boxed(lean_object* v_inst_465_, lean_object* v_t_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_TreeSet_Raw_min_x21___redArg(v_inst_465_, v_t_466_);
lean_dec(v_t_466_);
lean_dec(v_inst_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21(lean_object* v_00_u03b1_468_, lean_object* v_cmp_469_, lean_object* v_inst_470_, lean_object* v_t_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_470_, v_t_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_min_x21___boxed(lean_object* v_00_u03b1_473_, lean_object* v_cmp_474_, lean_object* v_inst_475_, lean_object* v_t_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_TreeSet_Raw_min_x21(v_00_u03b1_473_, v_cmp_474_, v_inst_475_, v_t_476_);
lean_dec(v_t_476_);
lean_dec(v_inst_475_);
lean_dec_ref(v_cmp_474_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg(lean_object* v_t_478_, lean_object* v_fallback_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_478_, v_fallback_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___redArg___boxed(lean_object* v_t_481_, lean_object* v_fallback_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_TreeSet_Raw_minD___redArg(v_t_481_, v_fallback_482_);
lean_dec(v_fallback_482_);
lean_dec(v_t_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD(lean_object* v_00_u03b1_484_, lean_object* v_cmp_485_, lean_object* v_t_486_, lean_object* v_fallback_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_486_, v_fallback_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_minD___boxed(lean_object* v_00_u03b1_489_, lean_object* v_cmp_490_, lean_object* v_t_491_, lean_object* v_fallback_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_TreeSet_Raw_minD(v_00_u03b1_489_, v_cmp_490_, v_t_491_, v_fallback_492_);
lean_dec(v_fallback_492_);
lean_dec(v_t_491_);
lean_dec_ref(v_cmp_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg(lean_object* v_t_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___redArg___boxed(lean_object* v_t_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_TreeSet_Raw_max_x3f___redArg(v_t_496_);
lean_dec(v_t_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f(lean_object* v_00_u03b1_498_, lean_object* v_cmp_499_, lean_object* v_t_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x3f___boxed(lean_object* v_00_u03b1_502_, lean_object* v_cmp_503_, lean_object* v_t_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_TreeSet_Raw_max_x3f(v_00_u03b1_502_, v_cmp_503_, v_t_504_);
lean_dec(v_t_504_);
lean_dec_ref(v_cmp_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg(lean_object* v_inst_506_, lean_object* v_t_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_506_, v_t_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___redArg___boxed(lean_object* v_inst_509_, lean_object* v_t_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_TreeSet_Raw_max_x21___redArg(v_inst_509_, v_t_510_);
lean_dec(v_t_510_);
lean_dec(v_inst_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21(lean_object* v_00_u03b1_512_, lean_object* v_cmp_513_, lean_object* v_inst_514_, lean_object* v_t_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_514_, v_t_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_max_x21___boxed(lean_object* v_00_u03b1_517_, lean_object* v_cmp_518_, lean_object* v_inst_519_, lean_object* v_t_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_TreeSet_Raw_max_x21(v_00_u03b1_517_, v_cmp_518_, v_inst_519_, v_t_520_);
lean_dec(v_t_520_);
lean_dec(v_inst_519_);
lean_dec_ref(v_cmp_518_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg(lean_object* v_t_522_, lean_object* v_fallback_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_522_, v_fallback_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___redArg___boxed(lean_object* v_t_525_, lean_object* v_fallback_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_TreeSet_Raw_maxD___redArg(v_t_525_, v_fallback_526_);
lean_dec(v_fallback_526_);
lean_dec(v_t_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD(lean_object* v_00_u03b1_528_, lean_object* v_cmp_529_, lean_object* v_t_530_, lean_object* v_fallback_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_530_, v_fallback_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_maxD___boxed(lean_object* v_00_u03b1_533_, lean_object* v_cmp_534_, lean_object* v_t_535_, lean_object* v_fallback_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_TreeSet_Raw_maxD(v_00_u03b1_533_, v_cmp_534_, v_t_535_, v_fallback_536_);
lean_dec(v_fallback_536_);
lean_dec(v_t_535_);
lean_dec_ref(v_cmp_534_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg(lean_object* v_t_538_, lean_object* v_n_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_538_, v_n_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___redArg___boxed(lean_object* v_t_541_, lean_object* v_n_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_TreeSet_Raw_atIdx_x3f___redArg(v_t_541_, v_n_542_);
lean_dec(v_t_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f(lean_object* v_00_u03b1_544_, lean_object* v_cmp_545_, lean_object* v_t_546_, lean_object* v_n_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_546_, v_n_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x3f___boxed(lean_object* v_00_u03b1_549_, lean_object* v_cmp_550_, lean_object* v_t_551_, lean_object* v_n_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_TreeSet_Raw_atIdx_x3f(v_00_u03b1_549_, v_cmp_550_, v_t_551_, v_n_552_);
lean_dec(v_t_551_);
lean_dec_ref(v_cmp_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg(lean_object* v_inst_554_, lean_object* v_t_555_, lean_object* v_n_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_554_, v_t_555_, v_n_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___redArg___boxed(lean_object* v_inst_558_, lean_object* v_t_559_, lean_object* v_n_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_TreeSet_Raw_atIdx_x21___redArg(v_inst_558_, v_t_559_, v_n_560_);
lean_dec(v_t_559_);
lean_dec(v_inst_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21(lean_object* v_00_u03b1_562_, lean_object* v_cmp_563_, lean_object* v_inst_564_, lean_object* v_t_565_, lean_object* v_n_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_564_, v_t_565_, v_n_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdx_x21___boxed(lean_object* v_00_u03b1_568_, lean_object* v_cmp_569_, lean_object* v_inst_570_, lean_object* v_t_571_, lean_object* v_n_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_TreeSet_Raw_atIdx_x21(v_00_u03b1_568_, v_cmp_569_, v_inst_570_, v_t_571_, v_n_572_);
lean_dec(v_t_571_);
lean_dec(v_inst_570_);
lean_dec_ref(v_cmp_569_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg(lean_object* v_t_574_, lean_object* v_n_575_, lean_object* v_fallback_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_574_, v_n_575_, v_fallback_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___redArg___boxed(lean_object* v_t_578_, lean_object* v_n_579_, lean_object* v_fallback_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_TreeSet_Raw_atIdxD___redArg(v_t_578_, v_n_579_, v_fallback_580_);
lean_dec(v_fallback_580_);
lean_dec(v_t_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD(lean_object* v_00_u03b1_582_, lean_object* v_cmp_583_, lean_object* v_t_584_, lean_object* v_n_585_, lean_object* v_fallback_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_584_, v_n_585_, v_fallback_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_atIdxD___boxed(lean_object* v_00_u03b1_588_, lean_object* v_cmp_589_, lean_object* v_t_590_, lean_object* v_n_591_, lean_object* v_fallback_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_TreeSet_Raw_atIdxD(v_00_u03b1_588_, v_cmp_589_, v_t_590_, v_n_591_, v_fallback_592_);
lean_dec(v_fallback_592_);
lean_dec(v_t_590_);
lean_dec_ref(v_cmp_589_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f___redArg(lean_object* v_cmp_594_, lean_object* v_t_595_, lean_object* v_k_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_box(0);
v___x_598_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_594_, v_k_596_, v___x_597_, v_t_595_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x3f(lean_object* v_00_u03b1_599_, lean_object* v_cmp_600_, lean_object* v_t_601_, lean_object* v_k_602_){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_box(0);
v___x_604_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_600_, v_k_602_, v___x_603_, v_t_601_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f___redArg(lean_object* v_cmp_605_, lean_object* v_t_606_, lean_object* v_k_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_box(0);
v___x_609_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_605_, v_k_607_, v___x_608_, v_t_606_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x3f(lean_object* v_00_u03b1_610_, lean_object* v_cmp_611_, lean_object* v_t_612_, lean_object* v_k_613_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_box(0);
v___x_615_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_611_, v_k_613_, v___x_614_, v_t_612_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f___redArg(lean_object* v_cmp_616_, lean_object* v_t_617_, lean_object* v_k_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_box(0);
v___x_620_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_616_, v_k_618_, v___x_619_, v_t_617_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x3f(lean_object* v_00_u03b1_621_, lean_object* v_cmp_622_, lean_object* v_t_623_, lean_object* v_k_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_box(0);
v___x_626_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_622_, v_k_624_, v___x_625_, v_t_623_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f___redArg(lean_object* v_cmp_627_, lean_object* v_t_628_, lean_object* v_k_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_box(0);
v___x_631_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_627_, v_k_629_, v___x_630_, v_t_628_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x3f(lean_object* v_00_u03b1_632_, lean_object* v_cmp_633_, lean_object* v_t_634_, lean_object* v_k_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(0);
v___x_637_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_633_, v_k_635_, v___x_636_, v_t_634_);
return v___x_637_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_641_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2));
v___x_642_ = lean_unsigned_to_nat(14u);
v___x_643_ = lean_unsigned_to_nat(22u);
v___x_644_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1));
v___x_645_ = ((lean_object*)(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0));
v___x_646_ = l_mkPanicMessageWithDecl(v___x_645_, v___x_644_, v___x_643_, v___x_642_, v___x_641_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg(lean_object* v_cmp_647_, lean_object* v_inst_648_, lean_object* v_t_649_, lean_object* v_k_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_box(0);
v___x_652_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_647_, v_k_650_, v___x_651_, v_t_649_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_654_ = l_panic___redArg(v_inst_648_, v___x_653_);
return v___x_654_;
}
else
{
lean_object* v_val_655_; 
v_val_655_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_655_);
lean_dec_ref_known(v___x_652_, 1);
return v_val_655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___redArg___boxed(lean_object* v_cmp_656_, lean_object* v_inst_657_, lean_object* v_t_658_, lean_object* v_k_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_TreeSet_Raw_getGE_x21___redArg(v_cmp_656_, v_inst_657_, v_t_658_, v_k_659_);
lean_dec(v_inst_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21(lean_object* v_00_u03b1_661_, lean_object* v_cmp_662_, lean_object* v_inst_663_, lean_object* v_t_664_, lean_object* v_k_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_box(0);
v___x_667_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_662_, v_k_665_, v___x_666_, v_t_664_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_669_ = l_panic___redArg(v_inst_663_, v___x_668_);
return v___x_669_;
}
else
{
lean_object* v_val_670_; 
v_val_670_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v___x_667_, 1);
return v_val_670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGE_x21___boxed(lean_object* v_00_u03b1_671_, lean_object* v_cmp_672_, lean_object* v_inst_673_, lean_object* v_t_674_, lean_object* v_k_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_TreeSet_Raw_getGE_x21(v_00_u03b1_671_, v_cmp_672_, v_inst_673_, v_t_674_, v_k_675_);
lean_dec(v_inst_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg(lean_object* v_cmp_677_, lean_object* v_inst_678_, lean_object* v_t_679_, lean_object* v_k_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_box(0);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_677_, v_k_680_, v___x_681_, v_t_679_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_684_ = l_panic___redArg(v_inst_678_, v___x_683_);
return v___x_684_;
}
else
{
lean_object* v_val_685_; 
v_val_685_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_val_685_);
lean_dec_ref_known(v___x_682_, 1);
return v_val_685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___redArg___boxed(lean_object* v_cmp_686_, lean_object* v_inst_687_, lean_object* v_t_688_, lean_object* v_k_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_TreeSet_Raw_getGT_x21___redArg(v_cmp_686_, v_inst_687_, v_t_688_, v_k_689_);
lean_dec(v_inst_687_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21(lean_object* v_00_u03b1_691_, lean_object* v_cmp_692_, lean_object* v_inst_693_, lean_object* v_t_694_, lean_object* v_k_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_box(0);
v___x_697_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_692_, v_k_695_, v___x_696_, v_t_694_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_699_ = l_panic___redArg(v_inst_693_, v___x_698_);
return v___x_699_;
}
else
{
lean_object* v_val_700_; 
v_val_700_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v___x_697_, 1);
return v_val_700_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGT_x21___boxed(lean_object* v_00_u03b1_701_, lean_object* v_cmp_702_, lean_object* v_inst_703_, lean_object* v_t_704_, lean_object* v_k_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_TreeSet_Raw_getGT_x21(v_00_u03b1_701_, v_cmp_702_, v_inst_703_, v_t_704_, v_k_705_);
lean_dec(v_inst_703_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg(lean_object* v_cmp_707_, lean_object* v_inst_708_, lean_object* v_t_709_, lean_object* v_k_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_box(0);
v___x_712_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_707_, v_k_710_, v___x_711_, v_t_709_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_714_ = l_panic___redArg(v_inst_708_, v___x_713_);
return v___x_714_;
}
else
{
lean_object* v_val_715_; 
v_val_715_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_val_715_);
lean_dec_ref_known(v___x_712_, 1);
return v_val_715_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___redArg___boxed(lean_object* v_cmp_716_, lean_object* v_inst_717_, lean_object* v_t_718_, lean_object* v_k_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_TreeSet_Raw_getLE_x21___redArg(v_cmp_716_, v_inst_717_, v_t_718_, v_k_719_);
lean_dec(v_inst_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21(lean_object* v_00_u03b1_721_, lean_object* v_cmp_722_, lean_object* v_inst_723_, lean_object* v_t_724_, lean_object* v_k_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_box(0);
v___x_727_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_722_, v_k_725_, v___x_726_, v_t_724_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_729_ = l_panic___redArg(v_inst_723_, v___x_728_);
return v___x_729_;
}
else
{
lean_object* v_val_730_; 
v_val_730_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v___x_727_, 1);
return v_val_730_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLE_x21___boxed(lean_object* v_00_u03b1_731_, lean_object* v_cmp_732_, lean_object* v_inst_733_, lean_object* v_t_734_, lean_object* v_k_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Std_TreeSet_Raw_getLE_x21(v_00_u03b1_731_, v_cmp_732_, v_inst_733_, v_t_734_, v_k_735_);
lean_dec(v_inst_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg(lean_object* v_cmp_737_, lean_object* v_inst_738_, lean_object* v_t_739_, lean_object* v_k_740_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_box(0);
v___x_742_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_737_, v_k_740_, v___x_741_, v_t_739_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_744_ = l_panic___redArg(v_inst_738_, v___x_743_);
return v___x_744_;
}
else
{
lean_object* v_val_745_; 
v_val_745_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_val_745_);
lean_dec_ref_known(v___x_742_, 1);
return v_val_745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___redArg___boxed(lean_object* v_cmp_746_, lean_object* v_inst_747_, lean_object* v_t_748_, lean_object* v_k_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_TreeSet_Raw_getLT_x21___redArg(v_cmp_746_, v_inst_747_, v_t_748_, v_k_749_);
lean_dec(v_inst_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21(lean_object* v_00_u03b1_751_, lean_object* v_cmp_752_, lean_object* v_inst_753_, lean_object* v_t_754_, lean_object* v_k_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_box(0);
v___x_757_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_752_, v_k_755_, v___x_756_, v_t_754_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_obj_once(&l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3, &l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once, _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3);
v___x_759_ = l_panic___redArg(v_inst_753_, v___x_758_);
return v___x_759_;
}
else
{
lean_object* v_val_760_; 
v_val_760_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v___x_757_, 1);
return v_val_760_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLT_x21___boxed(lean_object* v_00_u03b1_761_, lean_object* v_cmp_762_, lean_object* v_inst_763_, lean_object* v_t_764_, lean_object* v_k_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_TreeSet_Raw_getLT_x21(v_00_u03b1_761_, v_cmp_762_, v_inst_763_, v_t_764_, v_k_765_);
lean_dec(v_inst_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg(lean_object* v_cmp_767_, lean_object* v_t_768_, lean_object* v_k_769_, lean_object* v_fallback_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_box(0);
v___x_772_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_767_, v_k_769_, v___x_771_, v_t_768_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_inc(v_fallback_770_);
return v_fallback_770_;
}
else
{
lean_object* v_val_773_; 
v_val_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v___x_772_, 1);
return v_val_773_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___redArg___boxed(lean_object* v_cmp_774_, lean_object* v_t_775_, lean_object* v_k_776_, lean_object* v_fallback_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_TreeSet_Raw_getGED___redArg(v_cmp_774_, v_t_775_, v_k_776_, v_fallback_777_);
lean_dec(v_fallback_777_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED(lean_object* v_00_u03b1_779_, lean_object* v_cmp_780_, lean_object* v_t_781_, lean_object* v_k_782_, lean_object* v_fallback_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = lean_box(0);
v___x_785_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_780_, v_k_782_, v___x_784_, v_t_781_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_inc(v_fallback_783_);
return v_fallback_783_;
}
else
{
lean_object* v_val_786_; 
v_val_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_val_786_);
lean_dec_ref_known(v___x_785_, 1);
return v_val_786_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGED___boxed(lean_object* v_00_u03b1_787_, lean_object* v_cmp_788_, lean_object* v_t_789_, lean_object* v_k_790_, lean_object* v_fallback_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_TreeSet_Raw_getGED(v_00_u03b1_787_, v_cmp_788_, v_t_789_, v_k_790_, v_fallback_791_);
lean_dec(v_fallback_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg(lean_object* v_cmp_793_, lean_object* v_t_794_, lean_object* v_k_795_, lean_object* v_fallback_796_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_box(0);
v___x_798_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_793_, v_k_795_, v___x_797_, v_t_794_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_inc(v_fallback_796_);
return v_fallback_796_;
}
else
{
lean_object* v_val_799_; 
v_val_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_798_, 1);
return v_val_799_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___redArg___boxed(lean_object* v_cmp_800_, lean_object* v_t_801_, lean_object* v_k_802_, lean_object* v_fallback_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_TreeSet_Raw_getGTD___redArg(v_cmp_800_, v_t_801_, v_k_802_, v_fallback_803_);
lean_dec(v_fallback_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD(lean_object* v_00_u03b1_805_, lean_object* v_cmp_806_, lean_object* v_t_807_, lean_object* v_k_808_, lean_object* v_fallback_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_box(0);
v___x_811_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_806_, v_k_808_, v___x_810_, v_t_807_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_inc(v_fallback_809_);
return v_fallback_809_;
}
else
{
lean_object* v_val_812_; 
v_val_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v___x_811_, 1);
return v_val_812_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getGTD___boxed(lean_object* v_00_u03b1_813_, lean_object* v_cmp_814_, lean_object* v_t_815_, lean_object* v_k_816_, lean_object* v_fallback_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_TreeSet_Raw_getGTD(v_00_u03b1_813_, v_cmp_814_, v_t_815_, v_k_816_, v_fallback_817_);
lean_dec(v_fallback_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg(lean_object* v_cmp_819_, lean_object* v_t_820_, lean_object* v_k_821_, lean_object* v_fallback_822_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_box(0);
v___x_824_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_819_, v_k_821_, v___x_823_, v_t_820_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_inc(v_fallback_822_);
return v_fallback_822_;
}
else
{
lean_object* v_val_825_; 
v_val_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_val_825_);
lean_dec_ref_known(v___x_824_, 1);
return v_val_825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___redArg___boxed(lean_object* v_cmp_826_, lean_object* v_t_827_, lean_object* v_k_828_, lean_object* v_fallback_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_TreeSet_Raw_getLED___redArg(v_cmp_826_, v_t_827_, v_k_828_, v_fallback_829_);
lean_dec(v_fallback_829_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED(lean_object* v_00_u03b1_831_, lean_object* v_cmp_832_, lean_object* v_t_833_, lean_object* v_k_834_, lean_object* v_fallback_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_box(0);
v___x_837_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_832_, v_k_834_, v___x_836_, v_t_833_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_inc(v_fallback_835_);
return v_fallback_835_;
}
else
{
lean_object* v_val_838_; 
v_val_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_val_838_);
lean_dec_ref_known(v___x_837_, 1);
return v_val_838_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLED___boxed(lean_object* v_00_u03b1_839_, lean_object* v_cmp_840_, lean_object* v_t_841_, lean_object* v_k_842_, lean_object* v_fallback_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_TreeSet_Raw_getLED(v_00_u03b1_839_, v_cmp_840_, v_t_841_, v_k_842_, v_fallback_843_);
lean_dec(v_fallback_843_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg(lean_object* v_cmp_845_, lean_object* v_t_846_, lean_object* v_k_847_, lean_object* v_fallback_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_box(0);
v___x_850_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_845_, v_k_847_, v___x_849_, v_t_846_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_inc(v_fallback_848_);
return v_fallback_848_;
}
else
{
lean_object* v_val_851_; 
v_val_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v___x_850_, 1);
return v_val_851_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___redArg___boxed(lean_object* v_cmp_852_, lean_object* v_t_853_, lean_object* v_k_854_, lean_object* v_fallback_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_TreeSet_Raw_getLTD___redArg(v_cmp_852_, v_t_853_, v_k_854_, v_fallback_855_);
lean_dec(v_fallback_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD(lean_object* v_00_u03b1_857_, lean_object* v_cmp_858_, lean_object* v_t_859_, lean_object* v_k_860_, lean_object* v_fallback_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_box(0);
v___x_863_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_858_, v_k_860_, v___x_862_, v_t_859_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_inc(v_fallback_861_);
return v_fallback_861_;
}
else
{
lean_object* v_val_864_; 
v_val_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v___x_863_, 1);
return v_val_864_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_getLTD___boxed(lean_object* v_00_u03b1_865_, lean_object* v_cmp_866_, lean_object* v_t_867_, lean_object* v_k_868_, lean_object* v_fallback_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_TreeSet_Raw_getLTD(v_00_u03b1_865_, v_cmp_866_, v_t_867_, v_k_868_, v_fallback_869_);
lean_dec(v_fallback_869_);
return v_res_870_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_filter___redArg___lam__0(lean_object* v_f_871_, lean_object* v_a_872_, lean_object* v_x_873_){
_start:
{
lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_874_ = lean_apply_1(v_f_871_, v_a_872_);
v___x_875_ = lean_unbox(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_876_, lean_object* v_a_877_, lean_object* v_x_878_){
_start:
{
uint8_t v_res_879_; lean_object* v_r_880_; 
v_res_879_ = l_Std_TreeSet_Raw_filter___redArg___lam__0(v_f_876_, v_a_877_, v_x_878_);
v_r_880_ = lean_box(v_res_879_);
return v_r_880_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___redArg(lean_object* v_f_881_, lean_object* v_t_882_){
_start:
{
lean_object* v___f_883_; lean_object* v___x_884_; 
v___f_883_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_883_, 0, v_f_881_);
v___x_884_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_883_, v_t_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter(lean_object* v_00_u03b1_885_, lean_object* v_cmp_886_, lean_object* v_f_887_, lean_object* v_t_888_){
_start:
{
lean_object* v___f_889_; lean_object* v___x_890_; 
v___f_889_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_889_, 0, v_f_887_);
v___x_890_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_889_, v_t_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_filter___boxed(lean_object* v_00_u03b1_891_, lean_object* v_cmp_892_, lean_object* v_f_893_, lean_object* v_t_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_TreeSet_Raw_filter(v_00_u03b1_891_, v_cmp_892_, v_f_893_, v_t_894_);
lean_dec_ref(v_cmp_892_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg___lam__0(lean_object* v_f_896_, lean_object* v_c_897_, lean_object* v_a_898_, lean_object* v_x_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_apply_2(v_f_896_, v_c_897_, v_a_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___redArg(lean_object* v_inst_901_, lean_object* v_f_902_, lean_object* v_init_903_, lean_object* v_t_904_){
_start:
{
lean_object* v___f_905_; lean_object* v___x_906_; 
v___f_905_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_905_, 0, v_f_902_);
v___x_906_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_901_, v___f_905_, v_init_903_, v_t_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM(lean_object* v_00_u03b1_907_, lean_object* v_cmp_908_, lean_object* v_00_u03b4_909_, lean_object* v_m_910_, lean_object* v_inst_911_, lean_object* v_f_912_, lean_object* v_init_913_, lean_object* v_t_914_){
_start:
{
lean_object* v___f_915_; lean_object* v___x_916_; 
v___f_915_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_915_, 0, v_f_912_);
v___x_916_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_911_, v___f_915_, v_init_913_, v_t_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldlM___boxed(lean_object* v_00_u03b1_917_, lean_object* v_cmp_918_, lean_object* v_00_u03b4_919_, lean_object* v_m_920_, lean_object* v_inst_921_, lean_object* v_f_922_, lean_object* v_init_923_, lean_object* v_t_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_TreeSet_Raw_foldlM(v_00_u03b1_917_, v_cmp_918_, v_00_u03b4_919_, v_m_920_, v_inst_921_, v_f_922_, v_init_923_, v_t_924_);
lean_dec_ref(v_cmp_918_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___redArg(lean_object* v_f_926_, lean_object* v_init_927_, lean_object* v_t_928_){
_start:
{
lean_object* v___f_929_; lean_object* v___x_930_; 
v___f_929_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_929_, 0, v_f_926_);
v___x_930_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_929_, v_init_927_, v_t_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl(lean_object* v_00_u03b1_931_, lean_object* v_cmp_932_, lean_object* v_00_u03b4_933_, lean_object* v_f_934_, lean_object* v_init_935_, lean_object* v_t_936_){
_start:
{
lean_object* v___f_937_; lean_object* v___x_938_; 
v___f_937_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldlM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_937_, 0, v_f_934_);
v___x_938_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_937_, v_init_935_, v_t_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldl___boxed(lean_object* v_00_u03b1_939_, lean_object* v_cmp_940_, lean_object* v_00_u03b4_941_, lean_object* v_f_942_, lean_object* v_init_943_, lean_object* v_t_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_TreeSet_Raw_foldl(v_00_u03b1_939_, v_cmp_940_, v_00_u03b4_941_, v_f_942_, v_init_943_, v_t_944_);
lean_dec_ref(v_cmp_940_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg___lam__0(lean_object* v_f_946_, lean_object* v_a_947_, lean_object* v_x_948_, lean_object* v_acc_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = lean_apply_2(v_f_946_, v_a_947_, v_acc_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___redArg(lean_object* v_inst_951_, lean_object* v_f_952_, lean_object* v_init_953_, lean_object* v_t_954_){
_start:
{
lean_object* v___f_955_; lean_object* v___x_956_; 
v___f_955_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_955_, 0, v_f_952_);
v___x_956_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_951_, v___f_955_, v_init_953_, v_t_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM(lean_object* v_00_u03b1_957_, lean_object* v_cmp_958_, lean_object* v_00_u03b4_959_, lean_object* v_m_960_, lean_object* v_inst_961_, lean_object* v_f_962_, lean_object* v_init_963_, lean_object* v_t_964_){
_start:
{
lean_object* v___f_965_; lean_object* v___x_966_; 
v___f_965_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldrM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_965_, 0, v_f_962_);
v___x_966_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_961_, v___f_965_, v_init_963_, v_t_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldrM___boxed(lean_object* v_00_u03b1_967_, lean_object* v_cmp_968_, lean_object* v_00_u03b4_969_, lean_object* v_m_970_, lean_object* v_inst_971_, lean_object* v_f_972_, lean_object* v_init_973_, lean_object* v_t_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_TreeSet_Raw_foldrM(v_00_u03b1_967_, v_cmp_968_, v_00_u03b4_969_, v_m_970_, v_inst_971_, v_f_972_, v_init_973_, v_t_974_);
lean_dec_ref(v_cmp_968_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg___lam__0(lean_object* v_f_976_, lean_object* v_x1_977_, lean_object* v_x2_978_, lean_object* v_x3_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = lean_apply_2(v_f_976_, v_x1_977_, v_x3_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___redArg(lean_object* v_f_1000_, lean_object* v_init_1001_, lean_object* v_t_1002_){
_start:
{
lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___f_1003_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1003_, 0, v_f_1000_);
v___x_1004_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1005_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1004_, v___f_1003_, v_init_1001_, v_t_1002_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr(lean_object* v_00_u03b1_1006_, lean_object* v_cmp_1007_, lean_object* v_00_u03b4_1008_, lean_object* v_f_1009_, lean_object* v_init_1010_, lean_object* v_t_1011_){
_start:
{
lean_object* v___f_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___f_1012_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1012_, 0, v_f_1009_);
v___x_1013_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1014_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1013_, v___f_1012_, v_init_1010_, v_t_1011_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_foldr___boxed(lean_object* v_00_u03b1_1015_, lean_object* v_cmp_1016_, lean_object* v_00_u03b4_1017_, lean_object* v_f_1018_, lean_object* v_init_1019_, lean_object* v_t_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Std_TreeSet_Raw_foldr(v_00_u03b1_1015_, v_cmp_1016_, v_00_u03b4_1017_, v_f_1018_, v_init_1019_, v_t_1020_);
lean_dec_ref(v_cmp_1016_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg___lam__0(lean_object* v_f_1022_, lean_object* v_cmp_1023_, lean_object* v_x_1024_, lean_object* v_a_1025_, lean_object* v_b_1026_){
_start:
{
lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1042_; 
v_fst_1027_ = lean_ctor_get(v_x_1024_, 0);
v_snd_1028_ = lean_ctor_get(v_x_1024_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1030_ = v_x_1024_;
v_isShared_1031_ = v_isSharedCheck_1042_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_snd_1028_);
lean_inc(v_fst_1027_);
lean_dec(v_x_1024_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1042_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
lean_inc(v_a_1025_);
v___x_1032_ = lean_apply_1(v_f_1022_, v_a_1025_);
v___x_1033_ = lean_unbox(v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1034_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1023_, v_a_1025_, v_b_1026_, v_snd_1028_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1034_);
v___x_1036_ = v___x_1030_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_fst_1027_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1038_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1023_, v_a_1025_, v_b_1026_, v_fst_1027_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1038_);
v___x_1040_ = v___x_1030_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_snd_1028_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition___redArg(lean_object* v_cmp_1045_, lean_object* v_f_1046_, lean_object* v_t_1047_){
_start:
{
lean_object* v___f_1048_; lean_object* v___x_1049_; lean_object* v_p_1050_; lean_object* v_fst_1051_; lean_object* v_snd_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v___f_1048_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1048_, 0, v_f_1046_);
lean_closure_set(v___f_1048_, 1, v_cmp_1045_);
v___x_1049_ = ((lean_object*)(l_Std_TreeSet_Raw_partition___redArg___closed__0));
v_p_1050_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1048_, v___x_1049_, v_t_1047_);
v_fst_1051_ = lean_ctor_get(v_p_1050_, 0);
v_snd_1052_ = lean_ctor_get(v_p_1050_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_p_1050_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v_p_1050_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_snd_1052_);
lean_inc(v_fst_1051_);
lean_dec(v_p_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_fst_1051_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_snd_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_partition(lean_object* v_00_u03b1_1060_, lean_object* v_cmp_1061_, lean_object* v_f_1062_, lean_object* v_t_1063_){
_start:
{
lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v_p_1066_; lean_object* v_fst_1067_; lean_object* v_snd_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v___f_1064_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1064_, 0, v_f_1062_);
lean_closure_set(v___f_1064_, 1, v_cmp_1061_);
v___x_1065_ = ((lean_object*)(l_Std_TreeSet_Raw_partition___redArg___closed__0));
v_p_1066_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1064_, v___x_1065_, v_t_1063_);
v_fst_1067_ = lean_ctor_get(v_p_1066_, 0);
v_snd_1068_ = lean_ctor_get(v_p_1066_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_p_1066_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v_p_1066_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_snd_1068_);
lean_inc(v_fst_1067_);
lean_dec(v_p_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_fst_1067_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_snd_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg___lam__0(lean_object* v_f_1076_, lean_object* v_x_1077_, lean_object* v_k_1078_, lean_object* v_v_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_apply_1(v_f_1076_, v_k_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___redArg(lean_object* v_inst_1081_, lean_object* v_f_1082_, lean_object* v_t_1083_){
_start:
{
lean_object* v___f_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___f_1084_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1084_, 0, v_f_1082_);
v___x_1085_ = lean_box(0);
v___x_1086_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1081_, v___f_1084_, v___x_1085_, v_t_1083_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM(lean_object* v_00_u03b1_1087_, lean_object* v_cmp_1088_, lean_object* v_m_1089_, lean_object* v_inst_1090_, lean_object* v_f_1091_, lean_object* v_t_1092_){
_start:
{
lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___f_1093_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1093_, 0, v_f_1091_);
v___x_1094_ = lean_box(0);
v___x_1095_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1090_, v___f_1093_, v___x_1094_, v_t_1092_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forM___boxed(lean_object* v_00_u03b1_1096_, lean_object* v_cmp_1097_, lean_object* v_m_1098_, lean_object* v_inst_1099_, lean_object* v_f_1100_, lean_object* v_t_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_TreeSet_Raw_forM(v_00_u03b1_1096_, v_cmp_1097_, v_m_1098_, v_inst_1099_, v_f_1100_, v_t_1101_);
lean_dec_ref(v_cmp_1097_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__0(lean_object* v_f_1103_, lean_object* v_a_1104_, lean_object* v_b_1105_, lean_object* v_c_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_apply_2(v_f_1103_, v_a_1104_, v_c_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg___lam__1(lean_object* v_toPure_1108_, lean_object* v_____do__lift_1109_){
_start:
{
lean_object* v_a_1110_; lean_object* v___x_1111_; 
v_a_1110_ = lean_ctor_get(v_____do__lift_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref(v_____do__lift_1109_);
v___x_1111_ = lean_apply_2(v_toPure_1108_, lean_box(0), v_a_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___redArg(lean_object* v_inst_1112_, lean_object* v_f_1113_, lean_object* v_init_1114_, lean_object* v_t_1115_){
_start:
{
lean_object* v_toApplicative_1116_; lean_object* v_toBind_1117_; lean_object* v_toPure_1118_; lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___f_1121_; lean_object* v___x_1122_; 
v_toApplicative_1116_ = lean_ctor_get(v_inst_1112_, 0);
v_toBind_1117_ = lean_ctor_get(v_inst_1112_, 1);
lean_inc(v_toBind_1117_);
v_toPure_1118_ = lean_ctor_get(v_toApplicative_1116_, 1);
lean_inc(v_toPure_1118_);
v___f_1119_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1119_, 0, v_f_1113_);
v___x_1120_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1112_, v___f_1119_, v_init_1114_, v_t_1115_);
v___f_1121_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1121_, 0, v_toPure_1118_);
v___x_1122_ = lean_apply_4(v_toBind_1117_, lean_box(0), lean_box(0), v___x_1120_, v___f_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn(lean_object* v_00_u03b1_1123_, lean_object* v_cmp_1124_, lean_object* v_00_u03b4_1125_, lean_object* v_m_1126_, lean_object* v_inst_1127_, lean_object* v_f_1128_, lean_object* v_init_1129_, lean_object* v_t_1130_){
_start:
{
lean_object* v_toApplicative_1131_; lean_object* v_toBind_1132_; lean_object* v_toPure_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; 
v_toApplicative_1131_ = lean_ctor_get(v_inst_1127_, 0);
v_toBind_1132_ = lean_ctor_get(v_inst_1127_, 1);
lean_inc(v_toBind_1132_);
v_toPure_1133_ = lean_ctor_get(v_toApplicative_1131_, 1);
lean_inc(v_toPure_1133_);
v___f_1134_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1134_, 0, v_f_1128_);
v___x_1135_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1127_, v___f_1134_, v_init_1129_, v_t_1130_);
v___f_1136_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1136_, 0, v_toPure_1133_);
v___x_1137_ = lean_apply_4(v_toBind_1132_, lean_box(0), lean_box(0), v___x_1135_, v___f_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_forIn___boxed(lean_object* v_00_u03b1_1138_, lean_object* v_cmp_1139_, lean_object* v_00_u03b4_1140_, lean_object* v_m_1141_, lean_object* v_inst_1142_, lean_object* v_f_1143_, lean_object* v_init_1144_, lean_object* v_t_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Std_TreeSet_Raw_forIn(v_00_u03b1_1138_, v_cmp_1139_, v_00_u03b4_1140_, v_m_1141_, v_inst_1142_, v_f_1143_, v_init_1144_, v_t_1145_);
lean_dec_ref(v_cmp_1139_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1(lean_object* v_inst_1147_, lean_object* v_t_1148_, lean_object* v_f_1149_){
_start:
{
lean_object* v___f_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___f_1150_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1150_, 0, v_f_1149_);
v___x_1151_ = lean_box(0);
v___x_1152_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1147_, v___f_1150_, v___x_1151_, v_t_1148_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_1153_){
_start:
{
lean_object* v___f_1154_; 
v___f_1154_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1154_, 0, v_inst_1153_);
return v___f_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_1155_, lean_object* v_cmp_1156_, lean_object* v_m_1157_, lean_object* v_inst_1158_){
_start:
{
lean_object* v___f_1159_; 
v___f_1159_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1159_, 0, v_inst_1158_);
return v___f_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForMOfMonad___boxed(lean_object* v_00_u03b1_1160_, lean_object* v_cmp_1161_, lean_object* v_m_1162_, lean_object* v_inst_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Std_TreeSet_Raw_instForMOfMonad(v_00_u03b1_1160_, v_cmp_1161_, v_m_1162_, v_inst_1163_);
lean_dec_ref(v_cmp_1161_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2(lean_object* v_inst_1165_, lean_object* v_00_u03b2_1166_, lean_object* v_t_1167_, lean_object* v_init_1168_, lean_object* v_f_1169_){
_start:
{
lean_object* v_toApplicative_1170_; lean_object* v_toBind_1171_; lean_object* v_toPure_1172_; lean_object* v___f_1173_; lean_object* v___x_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; 
v_toApplicative_1170_ = lean_ctor_get(v_inst_1165_, 0);
v_toBind_1171_ = lean_ctor_get(v_inst_1165_, 1);
lean_inc(v_toBind_1171_);
v_toPure_1172_ = lean_ctor_get(v_toApplicative_1170_, 1);
lean_inc(v_toPure_1172_);
v___f_1173_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1173_, 0, v_f_1169_);
v___x_1174_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1165_, v___f_1173_, v_init_1168_, v_t_1167_);
v___f_1175_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1175_, 0, v_toPure_1172_);
v___x_1176_ = lean_apply_4(v_toBind_1171_, lean_box(0), lean_box(0), v___x_1174_, v___f_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_1177_){
_start:
{
lean_object* v___f_1178_; 
v___f_1178_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1178_, 0, v_inst_1177_);
return v___f_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_1179_, lean_object* v_cmp_1180_, lean_object* v_m_1181_, lean_object* v_inst_1182_){
_start:
{
lean_object* v___f_1183_; 
v___f_1183_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1183_, 0, v_inst_1182_);
return v___f_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instForInOfMonad___boxed(lean_object* v_00_u03b1_1184_, lean_object* v_cmp_1185_, lean_object* v_m_1186_, lean_object* v_inst_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_TreeSet_Raw_instForInOfMonad(v_00_u03b1_1184_, v_cmp_1185_, v_m_1186_, v_inst_1187_);
lean_dec_ref(v_cmp_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0(lean_object* v_p_1189_, lean_object* v___x_1190_, lean_object* v___x_1191_, lean_object* v_a_1192_, lean_object* v_b_1193_, lean_object* v_acc_1194_){
_start:
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = lean_apply_1(v_p_1189_, v_a_1192_);
v___x_1196_ = lean_unbox(v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1190_);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref(v___x_1190_);
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1195_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___x_1191_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1201_, lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v_a_1204_, lean_object* v_b_1205_, lean_object* v_acc_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_TreeSet_Raw_any___redArg___lam__0(v_p_1201_, v___x_1202_, v___x_1203_, v_a_1204_, v_b_1205_, v_acc_1206_);
lean_dec_ref(v_acc_1206_);
return v_res_1207_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_any___redArg(lean_object* v_t_1211_, lean_object* v_p_1212_){
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
lean_dec_ref_known(v_fst_1215_, 1);
v___x_1218_ = lean_unbox(v_val_1217_);
lean_dec(v_val_1217_);
return v___x_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___redArg___boxed(lean_object* v_t_1225_, lean_object* v_p_1226_){
_start:
{
uint8_t v_res_1227_; lean_object* v_r_1228_; 
v_res_1227_ = l_Std_TreeSet_Raw_any___redArg(v_t_1225_, v_p_1226_);
v_r_1228_ = lean_box(v_res_1227_);
return v_r_1228_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_any(lean_object* v_00_u03b1_1229_, lean_object* v_cmp_1230_, lean_object* v_t_1231_, lean_object* v_p_1232_){
_start:
{
lean_object* v___y_1234_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v_a_1244_; 
v___x_1239_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1240_ = lean_box(0);
v___x_1241_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1242_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1242_, 0, v_p_1232_);
lean_closure_set(v___f_1242_, 1, v___x_1241_);
lean_closure_set(v___f_1242_, 2, v___x_1240_);
v___x_1243_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1239_, v___f_1242_, v___x_1241_, v_t_1231_);
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___y_1234_ = v_a_1244_;
goto v___jp_1233_;
v___jp_1233_:
{
lean_object* v_fst_1235_; 
v_fst_1235_ = lean_ctor_get(v___y_1234_, 0);
lean_inc(v_fst_1235_);
lean_dec_ref(v___y_1234_);
if (lean_obj_tag(v_fst_1235_) == 0)
{
uint8_t v___x_1236_; 
v___x_1236_ = 0;
return v___x_1236_;
}
else
{
lean_object* v_val_1237_; uint8_t v___x_1238_; 
v_val_1237_ = lean_ctor_get(v_fst_1235_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v_fst_1235_, 1);
v___x_1238_ = lean_unbox(v_val_1237_);
lean_dec(v_val_1237_);
return v___x_1238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_any___boxed(lean_object* v_00_u03b1_1245_, lean_object* v_cmp_1246_, lean_object* v_t_1247_, lean_object* v_p_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = l_Std_TreeSet_Raw_any(v_00_u03b1_1245_, v_cmp_1246_, v_t_1247_, v_p_1248_);
lean_dec_ref(v_cmp_1246_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0(lean_object* v_p_1251_, lean_object* v___x_1252_, lean_object* v___x_1253_, lean_object* v_a_1254_, lean_object* v_b_1255_, lean_object* v_acc_1256_){
_start:
{
lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = lean_apply_1(v_p_1251_, v_a_1254_);
v___x_1258_ = lean_unbox(v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_dec_ref(v___x_1253_);
v___x_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___x_1252_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1253_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1263_, lean_object* v___x_1264_, lean_object* v___x_1265_, lean_object* v_a_1266_, lean_object* v_b_1267_, lean_object* v_acc_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Std_TreeSet_Raw_all___redArg___lam__0(v_p_1263_, v___x_1264_, v___x_1265_, v_a_1266_, v_b_1267_, v_acc_1268_);
lean_dec_ref(v_acc_1268_);
return v_res_1269_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_all___redArg(lean_object* v_t_1270_, lean_object* v_p_1271_){
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
lean_dec_ref_known(v_fst_1274_, 1);
v___x_1277_ = lean_unbox(v_val_1276_);
lean_dec(v_val_1276_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___redArg___boxed(lean_object* v_t_1284_, lean_object* v_p_1285_){
_start:
{
uint8_t v_res_1286_; lean_object* v_r_1287_; 
v_res_1286_ = l_Std_TreeSet_Raw_all___redArg(v_t_1284_, v_p_1285_);
v_r_1287_ = lean_box(v_res_1286_);
return v_r_1287_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_all(lean_object* v_00_u03b1_1288_, lean_object* v_cmp_1289_, lean_object* v_t_1290_, lean_object* v_p_1291_){
_start:
{
lean_object* v___y_1293_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___f_1301_; lean_object* v___x_1302_; lean_object* v_a_1303_; 
v___x_1298_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1299_ = lean_box(0);
v___x_1300_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___f_1301_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1301_, 0, v_p_1291_);
lean_closure_set(v___f_1301_, 1, v___x_1299_);
lean_closure_set(v___f_1301_, 2, v___x_1300_);
v___x_1302_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1298_, v___f_1301_, v___x_1300_, v_t_1290_);
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___y_1293_ = v_a_1303_;
goto v___jp_1292_;
v___jp_1292_:
{
lean_object* v_fst_1294_; 
v_fst_1294_ = lean_ctor_get(v___y_1293_, 0);
lean_inc(v_fst_1294_);
lean_dec_ref(v___y_1293_);
if (lean_obj_tag(v_fst_1294_) == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = 1;
return v___x_1295_;
}
else
{
lean_object* v_val_1296_; uint8_t v___x_1297_; 
v_val_1296_ = lean_ctor_get(v_fst_1294_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v_fst_1294_, 1);
v___x_1297_ = lean_unbox(v_val_1296_);
lean_dec(v_val_1296_);
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_all___boxed(lean_object* v_00_u03b1_1304_, lean_object* v_cmp_1305_, lean_object* v_t_1306_, lean_object* v_p_1307_){
_start:
{
uint8_t v_res_1308_; lean_object* v_r_1309_; 
v_res_1308_ = l_Std_TreeSet_Raw_all(v_00_u03b1_1304_, v_cmp_1305_, v_t_1306_, v_p_1307_);
lean_dec_ref(v_cmp_1305_);
v_r_1309_ = lean_box(v_res_1308_);
return v_r_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg___lam__0(lean_object* v_x1_1310_, lean_object* v_x2_1311_, lean_object* v_x3_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_x1_1310_);
lean_ctor_set(v___x_1313_, 1, v_x3_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___redArg(lean_object* v_t_1315_){
_start:
{
lean_object* v___f_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___f_1316_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___x_1317_ = lean_box(0);
v___x_1318_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1319_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1318_, v___f_1316_, v___x_1317_, v_t_1315_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList(lean_object* v_00_u03b1_1320_, lean_object* v_cmp_1321_, lean_object* v_t_1322_){
_start:
{
lean_object* v___f_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___f_1323_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___x_1324_ = lean_box(0);
v___x_1325_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1326_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1325_, v___f_1323_, v___x_1324_, v_t_1322_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_cmp_1328_, lean_object* v_t_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Std_TreeSet_Raw_toList(v_00_u03b1_1327_, v_cmp_1328_, v_t_1329_);
lean_dec_ref(v_cmp_1328_);
return v_res_1330_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__26, &l_Std_TreeSet_Raw___auto__1___closed__26_once, _init_l_Std_TreeSet_Raw___auto__1___closed__26);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg___lam__0(lean_object* v_cmp_1332_, lean_object* v_a_1333_, lean_object* v_x_1334_, lean_object* v___y_1335_){
_start:
{
uint8_t v___x_1336_; 
lean_inc(v___y_1335_);
lean_inc(v_a_1333_);
lean_inc_ref(v_cmp_1332_);
v___x_1336_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1332_, v_a_1333_, v___y_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = lean_box(0);
v___x_1338_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1332_, v_a_1333_, v___x_1337_, v___y_1335_);
v___x_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
return v___x_1339_;
}
else
{
lean_object* v___x_1340_; 
lean_dec(v_a_1333_);
lean_dec_ref(v_cmp_1332_);
v___x_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___y_1335_);
return v___x_1340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg(lean_object* v_l_1341_, lean_object* v_cmp_1342_){
_start:
{
lean_object* v___f_1343_; lean_object* v___x_1344_; lean_object* v_r_1345_; lean_object* v___x_1346_; 
v___f_1343_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1343_, 0, v_cmp_1342_);
v___x_1344_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1345_ = lean_box(1);
v___x_1346_ = l_List_forIn_x27_loop___redArg(v___x_1344_, v___f_1343_, v_l_1341_, v_r_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___redArg___boxed(lean_object* v_l_1347_, lean_object* v_cmp_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Std_TreeSet_Raw_ofList___redArg(v_l_1347_, v_cmp_1348_);
lean_dec(v_l_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList(lean_object* v_00_u03b1_1350_, lean_object* v_l_1351_, lean_object* v_cmp_1352_){
_start:
{
lean_object* v___f_1353_; lean_object* v___x_1354_; lean_object* v_r_1355_; lean_object* v___x_1356_; 
v___f_1353_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1353_, 0, v_cmp_1352_);
v___x_1354_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1355_ = lean_box(1);
v___x_1356_ = l_List_forIn_x27_loop___redArg(v___x_1354_, v___f_1353_, v_l_1351_, v_r_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofList___boxed(lean_object* v_00_u03b1_1357_, lean_object* v_l_1358_, lean_object* v_cmp_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Std_TreeSet_Raw_ofList(v_00_u03b1_1357_, v_l_1358_, v_cmp_1359_);
lean_dec(v_l_1358_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg___lam__0(lean_object* v_c_1361_, lean_object* v_a_1362_, lean_object* v_x_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_array_push(v_c_1361_, v_a_1362_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___redArg(lean_object* v_t_1368_){
_start:
{
lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___f_1369_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__0));
v___x_1370_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__1));
v___x_1371_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1369_, v___x_1370_, v_t_1368_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray(lean_object* v_00_u03b1_1372_, lean_object* v_cmp_1373_, lean_object* v_t_1374_){
_start:
{
lean_object* v___f_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___f_1375_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__0));
v___x_1376_ = ((lean_object*)(l_Std_TreeSet_Raw_toArray___redArg___closed__1));
v___x_1377_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1375_, v___x_1376_, v_t_1374_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toArray___boxed(lean_object* v_00_u03b1_1378_, lean_object* v_cmp_1379_, lean_object* v_t_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_TreeSet_Raw_toArray(v_00_u03b1_1378_, v_cmp_1379_, v_t_1380_);
lean_dec_ref(v_cmp_1379_);
return v_res_1381_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_obj_once(&l_Std_TreeSet_Raw___auto__1___closed__26, &l_Std_TreeSet_Raw___auto__1___closed__26_once, _init_l_Std_TreeSet_Raw___auto__1___closed__26);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray___redArg(lean_object* v_a_1383_, lean_object* v_cmp_1384_){
_start:
{
lean_object* v___f_1385_; lean_object* v___x_1386_; lean_object* v_r_1387_; size_t v_sz_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
v___f_1385_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1385_, 0, v_cmp_1384_);
v___x_1386_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1387_ = lean_box(1);
v_sz_1388_ = lean_array_size(v_a_1383_);
v___x_1389_ = ((size_t)0ULL);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1386_, v_a_1383_, v___f_1385_, v_sz_1388_, v___x_1389_, v_r_1387_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_ofArray(lean_object* v_00_u03b1_1391_, lean_object* v_a_1392_, lean_object* v_cmp_1393_){
_start:
{
lean_object* v___f_1394_; lean_object* v___x_1395_; lean_object* v_r_1396_; size_t v_sz_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v___f_1394_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1394_, 0, v_cmp_1393_);
v___x_1395_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v_r_1396_ = lean_box(1);
v_sz_1397_ = lean_array_size(v_a_1392_);
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1395_, v_a_1392_, v___f_1394_, v_sz_1397_, v___x_1398_, v_r_1396_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0(lean_object* v_b_u2082_1402_, lean_object* v_x_1403_){
_start:
{
if (lean_obj_tag(v_x_1403_) == 0)
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_b_u2082_1402_);
return v___x_1404_;
}
else
{
lean_object* v___x_1405_; 
v___x_1405_ = ((lean_object*)(l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0));
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed(lean_object* v_b_u2082_1406_, lean_object* v_x_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Std_TreeSet_Raw_merge___redArg___lam__0(v_b_u2082_1406_, v_x_1407_);
lean_dec(v_x_1407_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg___lam__1(lean_object* v_cmp_1409_, lean_object* v_t_1410_, lean_object* v_a_1411_, lean_object* v_b_u2082_1412_){
_start:
{
lean_object* v___f_1413_; lean_object* v___x_1414_; 
v___f_1413_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1413_, 0, v_b_u2082_1412_);
v___x_1414_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_1409_, v_a_1411_, v___f_1413_, v_t_1410_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge___redArg(lean_object* v_cmp_1415_, lean_object* v_t_u2081_1416_, lean_object* v_t_u2082_1417_){
_start:
{
lean_object* v___f_1418_; lean_object* v___x_1419_; 
v___f_1418_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1418_, 0, v_cmp_1415_);
v___x_1419_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1418_, v_t_u2081_1416_, v_t_u2082_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_merge(lean_object* v_00_u03b1_1420_, lean_object* v_cmp_1421_, lean_object* v_t_u2081_1422_, lean_object* v_t_u2082_1423_){
_start:
{
lean_object* v___f_1424_; lean_object* v___x_1425_; 
v___f_1424_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_merge___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1424_, 0, v_cmp_1421_);
v___x_1425_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1424_, v_t_u2081_1422_, v_t_u2082_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_1426_, lean_object* v_a_1427_, lean_object* v_____s_1428_){
_start:
{
uint8_t v___x_1429_; 
lean_inc(v_____s_1428_);
lean_inc(v_a_1427_);
lean_inc_ref(v_cmp_1426_);
v___x_1429_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1426_, v_a_1427_, v_____s_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1426_, v_a_1427_, v___x_1430_, v_____s_1428_);
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; 
lean_dec(v_a_1427_);
lean_dec_ref(v_cmp_1426_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_____s_1428_);
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany___redArg(lean_object* v_cmp_1434_, lean_object* v_inst_1435_, lean_object* v_t_1436_, lean_object* v_l_1437_){
_start:
{
lean_object* v___f_1438_; lean_object* v___x_1439_; 
v___f_1438_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1438_, 0, v_cmp_1434_);
v___x_1439_ = lean_apply_4(v_inst_1435_, lean_box(0), v_l_1437_, v_t_1436_, v___f_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_insertMany(lean_object* v_00_u03b1_1440_, lean_object* v_cmp_1441_, lean_object* v_00_u03c1_1442_, lean_object* v_inst_1443_, lean_object* v_t_1444_, lean_object* v_l_1445_){
_start:
{
lean_object* v___f_1446_; lean_object* v___x_1447_; 
v___f_1446_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1446_, 0, v_cmp_1441_);
v___x_1447_ = lean_apply_4(v_inst_1443_, lean_box(0), v_l_1445_, v_t_1444_, v___f_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union___redArg(lean_object* v_cmp_1448_, lean_object* v_t_u2081_1449_, lean_object* v_t_u2082_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_1448_, v_t_u2081_1449_, v_t_u2082_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_union(lean_object* v_00_u03b1_1452_, lean_object* v_cmp_1453_, lean_object* v_t_u2081_1454_, lean_object* v_t_u2082_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_1453_, v_t_u2081_1454_, v_t_u2082_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion___redArg(lean_object* v_cmp_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_union), 4, 2);
lean_closure_set(v___x_1458_, 0, lean_box(0));
lean_closure_set(v___x_1458_, 1, v_cmp_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instUnion(lean_object* v_00_u03b1_1459_, lean_object* v_cmp_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_union), 4, 2);
lean_closure_set(v___x_1461_, 0, lean_box(0));
lean_closure_set(v___x_1461_, 1, v_cmp_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter___redArg(lean_object* v_cmp_1462_, lean_object* v_t_u2081_1463_, lean_object* v_t_u2082_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_1462_, v_t_u2081_1463_, v_t_u2082_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_inter(lean_object* v_00_u03b1_1466_, lean_object* v_cmp_1467_, lean_object* v_t_u2081_1468_, lean_object* v_t_u2082_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_1467_, v_t_u2081_1468_, v_t_u2082_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter___redArg(lean_object* v_cmp_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_inter), 4, 2);
lean_closure_set(v___x_1472_, 0, lean_box(0));
lean_closure_set(v___x_1472_, 1, v_cmp_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instInter(lean_object* v_00_u03b1_1473_, lean_object* v_cmp_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_inter), 4, 2);
lean_closure_set(v___x_1475_, 0, lean_box(0));
lean_closure_set(v___x_1475_, 1, v_cmp_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1476_, lean_object* v_x_1477_){
_start:
{
if (lean_obj_tag(v_x_1476_) == 0)
{
if (lean_obj_tag(v_x_1477_) == 0)
{
uint8_t v___x_1478_; 
v___x_1478_ = 1;
return v___x_1478_;
}
else
{
uint8_t v___x_1479_; 
v___x_1479_ = 0;
return v___x_1479_;
}
}
else
{
if (lean_obj_tag(v_x_1477_) == 0)
{
uint8_t v___x_1480_; 
v___x_1480_ = 0;
return v___x_1480_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = 1;
return v___x_1481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_1482_, lean_object* v_x_1483_){
_start:
{
uint8_t v_res_1484_; lean_object* v_r_1485_; 
v_res_1484_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v_x_1482_, v_x_1483_);
lean_dec(v_x_1483_);
lean_dec(v_x_1482_);
v_r_1485_ = lean_box(v_res_1484_);
return v_r_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_cmp_1486_, lean_object* v_t_1487_, lean_object* v_k_1488_){
_start:
{
if (lean_obj_tag(v_t_1487_) == 0)
{
lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v_l_1491_; lean_object* v_r_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v_k_1489_ = lean_ctor_get(v_t_1487_, 1);
lean_inc(v_k_1489_);
v_v_1490_ = lean_ctor_get(v_t_1487_, 2);
lean_inc(v_v_1490_);
v_l_1491_ = lean_ctor_get(v_t_1487_, 3);
lean_inc(v_l_1491_);
v_r_1492_ = lean_ctor_get(v_t_1487_, 4);
lean_inc(v_r_1492_);
lean_dec_ref_known(v_t_1487_, 5);
lean_inc_ref(v_cmp_1486_);
lean_inc(v_k_1488_);
v___x_1493_ = lean_apply_2(v_cmp_1486_, v_k_1488_, v_k_1489_);
v___x_1494_ = lean_unbox(v___x_1493_);
switch(v___x_1494_)
{
case 0:
{
lean_dec(v_r_1492_);
lean_dec(v_v_1490_);
v_t_1487_ = v_l_1491_;
goto _start;
}
case 1:
{
lean_object* v___x_1496_; 
lean_dec(v_r_1492_);
lean_dec(v_l_1491_);
lean_dec(v_k_1488_);
lean_dec_ref(v_cmp_1486_);
v___x_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_v_1490_);
return v___x_1496_;
}
default: 
{
lean_dec(v_l_1491_);
lean_dec(v_v_1490_);
v_t_1487_ = v_r_1492_;
goto _start;
}
}
}
else
{
lean_object* v___x_1498_; 
lean_dec(v_k_1488_);
lean_dec_ref(v_cmp_1486_);
v___x_1498_ = lean_box(0);
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v_cmp_1501_, lean_object* v_t_u2082_1502_, lean_object* v_init_1503_, lean_object* v_x_1504_){
_start:
{
lean_object* v___x_1505_; uint8_t v___y_1507_; lean_object* v___x_1512_; uint8_t v___y_1514_; uint8_t v___x_1532_; 
v___x_1505_ = lean_box(0);
v___x_1512_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___x_1532_ = lean_nat_dec_eq(v___y_1499_, v___y_1500_);
if (v___x_1532_ == 0)
{
uint8_t v___x_1533_; 
v___x_1533_ = 1;
v___y_1514_ = v___x_1533_;
goto v___jp_1513_;
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = 0;
v___y_1514_ = v___x_1534_;
goto v___jp_1513_;
}
v___jp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1508_ = lean_box(v___y_1507_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___x_1505_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
v___jp_1513_:
{
if (lean_obj_tag(v_x_1504_) == 0)
{
lean_object* v_k_1515_; lean_object* v_v_1516_; lean_object* v_l_1517_; lean_object* v_r_1518_; lean_object* v___x_1519_; 
v_k_1515_ = lean_ctor_get(v_x_1504_, 1);
lean_inc(v_k_1515_);
v_v_1516_ = lean_ctor_get(v_x_1504_, 2);
lean_inc(v_v_1516_);
v_l_1517_ = lean_ctor_get(v_x_1504_, 3);
lean_inc(v_l_1517_);
v_r_1518_ = lean_ctor_get(v_x_1504_, 4);
lean_inc(v_r_1518_);
lean_dec_ref_known(v_x_1504_, 5);
lean_inc(v_t_u2082_1502_);
lean_inc_ref(v_cmp_1501_);
v___x_1519_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1499_, v___y_1500_, v_cmp_1501_, v_t_u2082_1502_, v_init_1503_, v_l_1517_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_dec(v_r_1518_);
lean_dec(v_v_1516_);
lean_dec(v_k_1515_);
lean_dec(v_t_u2082_1502_);
lean_dec_ref(v_cmp_1501_);
return v___x_1519_;
}
else
{
lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1529_; 
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v___x_1519_, 0);
lean_dec(v_unused_1530_);
v___x_1521_ = v___x_1519_;
v_isShared_1522_ = v_isSharedCheck_1529_;
goto v_resetjp_1520_;
}
else
{
lean_dec(v___x_1519_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1529_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
lean_inc(v_t_u2082_1502_);
lean_inc_ref(v_cmp_1501_);
v___x_1523_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1501_, v_t_u2082_1502_, v_k_1515_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v_v_1516_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_v_1516_);
v___x_1525_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
uint8_t v___x_1526_; 
v___x_1526_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v___x_1523_, v___x_1525_);
lean_dec_ref(v___x_1525_);
lean_dec(v___x_1523_);
if (v___x_1526_ == 0)
{
lean_dec(v_r_1518_);
lean_dec(v_t_u2082_1502_);
lean_dec_ref(v_cmp_1501_);
v___y_1507_ = v___y_1514_;
goto v___jp_1506_;
}
else
{
if (v___y_1514_ == 0)
{
v_init_1503_ = v___x_1512_;
v_x_1504_ = v_r_1518_;
goto _start;
}
else
{
lean_dec(v_r_1518_);
lean_dec(v_t_u2082_1502_);
lean_dec_ref(v_cmp_1501_);
v___y_1507_ = v___y_1514_;
goto v___jp_1506_;
}
}
}
}
}
}
else
{
lean_object* v___x_1531_; 
lean_dec(v_t_u2082_1502_);
lean_dec_ref(v_cmp_1501_);
v___x_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1531_, 0, v_init_1503_);
return v___x_1531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v_cmp_1537_, lean_object* v_t_u2082_1538_, lean_object* v_init_1539_, lean_object* v_x_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1535_, v___y_1536_, v_cmp_1537_, v_t_u2082_1538_, v_init_1539_, v_x_1540_);
lean_dec(v___y_1536_);
lean_dec(v___y_1535_);
return v_res_1541_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_1542_, lean_object* v_t_u2081_1543_, lean_object* v_t_u2082_1544_){
_start:
{
lean_object* v___y_1546_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1559_; 
if (lean_obj_tag(v_t_u2081_1543_) == 0)
{
lean_object* v_size_1562_; 
v_size_1562_ = lean_ctor_get(v_t_u2081_1543_, 0);
lean_inc(v_size_1562_);
v___y_1559_ = v_size_1562_;
goto v___jp_1558_;
}
else
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_unsigned_to_nat(0u);
v___y_1559_ = v___x_1563_;
goto v___jp_1558_;
}
v___jp_1545_:
{
lean_object* v_fst_1547_; 
v_fst_1547_ = lean_ctor_get(v___y_1546_, 0);
lean_inc(v_fst_1547_);
lean_dec_ref(v___y_1546_);
if (lean_obj_tag(v_fst_1547_) == 0)
{
uint8_t v___x_1548_; 
v___x_1548_ = 1;
return v___x_1548_;
}
else
{
lean_object* v_val_1549_; uint8_t v___x_1550_; 
v_val_1549_ = lean_ctor_get(v_fst_1547_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_fst_1547_, 1);
v___x_1550_ = lean_unbox(v_val_1549_);
lean_dec(v_val_1549_);
return v___x_1550_;
}
}
v___jp_1551_:
{
uint8_t v___x_1554_; 
v___x_1554_ = lean_nat_dec_eq(v___y_1552_, v___y_1553_);
if (v___x_1554_ == 0)
{
lean_dec(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec(v_t_u2082_1544_);
lean_dec(v_t_u2081_1543_);
lean_dec_ref(v_cmp_1542_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v_a_1557_; 
v___x_1555_ = ((lean_object*)(l_Std_TreeSet_Raw_any___redArg___closed__0));
v___x_1556_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1552_, v___y_1553_, v_cmp_1542_, v_t_u2082_1544_, v___x_1555_, v_t_u2081_1543_);
lean_dec(v___y_1553_);
lean_dec(v___y_1552_);
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___x_1556_);
v___y_1546_ = v_a_1557_;
goto v___jp_1545_;
}
}
v___jp_1558_:
{
if (lean_obj_tag(v_t_u2082_1544_) == 0)
{
lean_object* v_size_1560_; 
v_size_1560_ = lean_ctor_get(v_t_u2082_1544_, 0);
lean_inc(v_size_1560_);
v___y_1552_ = v___y_1559_;
v___y_1553_ = v_size_1560_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_unsigned_to_nat(0u);
v___y_1552_ = v___y_1559_;
v___y_1553_ = v___x_1561_;
goto v___jp_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_1564_, lean_object* v_t_u2081_1565_, lean_object* v_t_u2082_1566_){
_start:
{
uint8_t v_res_1567_; lean_object* v_r_1568_; 
v_res_1567_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1564_, v_t_u2081_1565_, v_t_u2082_1566_);
v_r_1568_ = lean_box(v_res_1567_);
return v_r_1568_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_beq___redArg(lean_object* v_cmp_1569_, lean_object* v_t_u2081_1570_, lean_object* v_t_u2082_1571_){
_start:
{
uint8_t v___x_1572_; 
v___x_1572_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1569_, v_t_u2081_1570_, v_t_u2082_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___redArg___boxed(lean_object* v_cmp_1573_, lean_object* v_t_u2081_1574_, lean_object* v_t_u2082_1575_){
_start:
{
uint8_t v_res_1576_; lean_object* v_r_1577_; 
v_res_1576_ = l_Std_TreeSet_Raw_beq___redArg(v_cmp_1573_, v_t_u2081_1574_, v_t_u2082_1575_);
v_r_1577_ = lean_box(v_res_1576_);
return v_r_1577_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_beq(lean_object* v_00_u03b1_1578_, lean_object* v_cmp_1579_, lean_object* v_t_u2081_1580_, lean_object* v_t_u2082_1581_){
_start:
{
uint8_t v___x_1582_; 
v___x_1582_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1579_, v_t_u2081_1580_, v_t_u2082_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_beq___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_cmp_1584_, lean_object* v_t_u2081_1585_, lean_object* v_t_u2082_1586_){
_start:
{
uint8_t v_res_1587_; lean_object* v_r_1588_; 
v_res_1587_ = l_Std_TreeSet_Raw_beq(v_00_u03b1_1583_, v_cmp_1584_, v_t_u2081_1585_, v_t_u2082_1586_);
v_r_1588_ = lean_box(v_res_1587_);
return v_r_1588_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(lean_object* v_cmp_1589_, lean_object* v_t_u2081_1590_, lean_object* v_t_u2082_1591_){
_start:
{
uint8_t v___x_1592_; 
v___x_1592_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1589_, v_t_u2081_1590_, v_t_u2082_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg___boxed(lean_object* v_cmp_1593_, lean_object* v_t_u2081_1594_, lean_object* v_t_u2082_1595_){
_start:
{
uint8_t v_res_1596_; lean_object* v_r_1597_; 
v_res_1596_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(v_cmp_1593_, v_t_u2081_1594_, v_t_u2082_1595_);
v_r_1597_ = lean_box(v_res_1596_);
return v_r_1597_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(lean_object* v_00_u03b1_1598_, lean_object* v_cmp_1599_, lean_object* v_t_u2081_1600_, lean_object* v_t_u2082_1601_){
_start:
{
uint8_t v___x_1602_; 
v___x_1602_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1599_, v_t_u2081_1600_, v_t_u2082_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___boxed(lean_object* v_00_u03b1_1603_, lean_object* v_cmp_1604_, lean_object* v_t_u2081_1605_, lean_object* v_t_u2082_1606_){
_start:
{
uint8_t v_res_1607_; lean_object* v_r_1608_; 
v_res_1607_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(v_00_u03b1_1603_, v_cmp_1604_, v_t_u2081_1605_, v_t_u2082_1606_);
v_r_1608_ = lean_box(v_res_1607_);
return v_r_1608_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(lean_object* v_cmp_1609_, lean_object* v_t_u2081_1610_, lean_object* v_t_u2082_1611_){
_start:
{
uint8_t v___x_1612_; 
v___x_1612_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1609_, v_t_u2081_1610_, v_t_u2082_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_1613_, lean_object* v_t_u2081_1614_, lean_object* v_t_u2082_1615_){
_start:
{
uint8_t v_res_1616_; lean_object* v_r_1617_; 
v_res_1616_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(v_cmp_1613_, v_t_u2081_1614_, v_t_u2082_1615_);
v_r_1617_ = lean_box(v_res_1616_);
return v_r_1617_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(lean_object* v_00_u03b1_1618_, lean_object* v_cmp_1619_, lean_object* v_t_u2081_1620_, lean_object* v_t_u2082_1621_){
_start:
{
uint8_t v___x_1622_; 
v___x_1622_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1619_, v_t_u2081_1620_, v_t_u2082_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1623_, lean_object* v_cmp_1624_, lean_object* v_t_u2081_1625_, lean_object* v_t_u2082_1626_){
_start:
{
uint8_t v_res_1627_; lean_object* v_r_1628_; 
v_res_1627_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(v_00_u03b1_1623_, v_cmp_1624_, v_t_u2081_1625_, v_t_u2082_1626_);
v_r_1628_ = lean_box(v_res_1627_);
return v_r_1628_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1629_, lean_object* v_cmp_1630_, lean_object* v_t_u2081_1631_, lean_object* v_t_u2082_1632_){
_start:
{
uint8_t v___x_1633_; 
v___x_1633_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_1630_, v_t_u2081_1631_, v_t_u2082_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1634_, lean_object* v_cmp_1635_, lean_object* v_t_u2081_1636_, lean_object* v_t_u2082_1637_){
_start:
{
uint8_t v_res_1638_; lean_object* v_r_1639_; 
v_res_1638_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(v_00_u03b1_1634_, v_cmp_1635_, v_t_u2081_1636_, v_t_u2082_1637_);
v_r_1639_ = lean_box(v_res_1638_);
return v_r_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1640_, lean_object* v_cmp_1641_, lean_object* v_00_u03b4_1642_, lean_object* v_t_1643_, lean_object* v_k_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_1641_, v_t_1643_, v_k_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v_cmp_1649_, lean_object* v_t_u2082_1650_, lean_object* v_init_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v___y_1647_, v___y_1648_, v_cmp_1649_, v_t_u2082_1650_, v_init_1651_, v_x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v_cmp_1657_, lean_object* v_t_u2082_1658_, lean_object* v_init_1659_, lean_object* v_x_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1654_, v___y_1655_, v___y_1656_, v_cmp_1657_, v_t_u2082_1658_, v_init_1659_, v_x_1660_);
lean_dec(v___y_1656_);
lean_dec(v___y_1655_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq___redArg(lean_object* v_cmp_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_beq___boxed), 4, 2);
lean_closure_set(v___x_1663_, 0, lean_box(0));
lean_closure_set(v___x_1663_, 1, v_cmp_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instBEq(lean_object* v_00_u03b1_1664_, lean_object* v_cmp_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_beq___boxed), 4, 2);
lean_closure_set(v___x_1666_, 0, lean_box(0));
lean_closure_set(v___x_1666_, 1, v_cmp_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff___redArg(lean_object* v_cmp_1667_, lean_object* v_t_u2081_1668_, lean_object* v_t_u2082_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_1667_, v_t_u2081_1668_, v_t_u2082_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_diff(lean_object* v_00_u03b1_1671_, lean_object* v_cmp_1672_, lean_object* v_t_u2081_1673_, lean_object* v_t_u2082_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_1672_, v_t_u2081_1673_, v_t_u2082_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff___redArg(lean_object* v_cmp_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_diff), 4, 2);
lean_closure_set(v___x_1677_, 0, lean_box(0));
lean_closure_set(v___x_1677_, 1, v_cmp_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSDiff(lean_object* v_00_u03b1_1678_, lean_object* v_cmp_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_diff), 4, 2);
lean_closure_set(v___x_1680_, 0, lean_box(0));
lean_closure_set(v___x_1680_, 1, v_cmp_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_1681_, lean_object* v_a_1682_, lean_object* v_____s_1683_){
_start:
{
lean_object* v_r_1684_; lean_object* v___x_1685_; 
v_r_1684_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_1681_, v_a_1682_, v_____s_1683_);
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_r_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany___redArg(lean_object* v_cmp_1686_, lean_object* v_inst_1687_, lean_object* v_t_1688_, lean_object* v_l_1689_){
_start:
{
lean_object* v___f_1690_; lean_object* v___x_1691_; 
v___f_1690_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1690_, 0, v_cmp_1686_);
v___x_1691_ = lean_apply_4(v_inst_1687_, lean_box(0), v_l_1689_, v_t_1688_, v___f_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_eraseMany(lean_object* v_00_u03b1_1692_, lean_object* v_cmp_1693_, lean_object* v_00_u03c1_1694_, lean_object* v_inst_1695_, lean_object* v_t_1696_, lean_object* v_l_1697_){
_start:
{
lean_object* v___f_1698_; lean_object* v___x_1699_; 
v___f_1698_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1698_, 0, v_cmp_1693_);
v___x_1699_ = lean_apply_4(v_inst_1695_, lean_box(0), v_l_1697_, v_t_1696_, v___f_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1(lean_object* v___f_1703_, lean_object* v_inst_1704_, lean_object* v_m_1705_, lean_object* v_prec_1706_){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1707_ = ((lean_object*)(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1));
v___x_1708_ = lean_box(0);
v___x_1709_ = ((lean_object*)(l_Std_TreeSet_Raw_foldr___redArg___closed__9));
v___x_1710_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1709_, v___f_1703_, v___x_1708_, v_m_1705_);
v___x_1711_ = l_List_repr___redArg(v_inst_1704_, v___x_1710_);
v___x_1712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1707_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = l_Repr_addAppParen(v___x_1712_, v_prec_1706_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_1714_, lean_object* v_inst_1715_, lean_object* v_m_1716_, lean_object* v_prec_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Std_TreeSet_Raw_instRepr___redArg___lam__1(v___f_1714_, v_inst_1715_, v_m_1716_, v_prec_1717_);
lean_dec(v_prec_1717_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___redArg(lean_object* v_inst_1719_){
_start:
{
lean_object* v___f_1720_; lean_object* v___f_1721_; 
v___f_1720_ = ((lean_object*)(l_Std_TreeSet_Raw_toList___redArg___closed__0));
v___f_1721_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1721_, 0, v___f_1720_);
lean_closure_set(v___f_1721_, 1, v_inst_1719_);
return v___f_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr(lean_object* v_00_u03b1_1722_, lean_object* v_cmp_1723_, lean_object* v_inst_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Std_TreeSet_Raw_instRepr___redArg(v_inst_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instRepr___boxed(lean_object* v_00_u03b1_1726_, lean_object* v_cmp_1727_, lean_object* v_inst_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Std_TreeSet_Raw_instRepr(v_00_u03b1_1726_, v_cmp_1727_, v_inst_1728_);
lean_dec_ref(v_cmp_1727_);
return v_res_1729_;
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
