// Lean compiler output
// Module: Std.Data.ExtTreeMap.Basic
// Imports: public import Std.Data.ExtDTreeMap.Basic
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_map___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_ExtTreeMap___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__0 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__0_value;
static const lean_string_object l_Std_ExtTreeMap___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__1 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__1_value;
static const lean_string_object l_Std_ExtTreeMap___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__2 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__2_value;
static const lean_string_object l_Std_ExtTreeMap___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__3 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__3_value;
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__4 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__4_value;
static const lean_array_object l_Std_ExtTreeMap___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__5 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__5_value;
static const lean_string_object l_Std_ExtTreeMap___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__6 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__6_value;
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__7 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__7_value;
static const lean_string_object l_Std_ExtTreeMap___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__8 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__8_value;
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__9 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__9_value;
static const lean_string_object l_Std_ExtTreeMap___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__10 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__10_value;
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__11 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__11_value;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__12;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__13;
static const lean_string_object l_Std_ExtTreeMap___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__14 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__14_value;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__15;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__16;
static const lean_ctor_object l_Std_ExtTreeMap___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_ExtTreeMap___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_ExtTreeMap___auto__1___closed__17 = (const lean_object*)&l_Std_ExtTreeMap___auto__1___closed__17_value;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__18;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__19;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__20;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__21;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__22;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__23;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__24;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__25;
static lean_once_cell_t l_Std_ExtTreeMap___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0_value;
static const lean_string_object l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1 = (const lean_object*)&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1_value;
static const lean_string_object l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2 = (const lean_object*)&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtTreeMap_foldr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_foldr___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__0_value;
static const lean_closure_object l_Std_ExtTreeMap_foldr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_foldr___redArg___closed__1 = (const lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__1_value;
static const lean_closure_object l_Std_ExtTreeMap_foldr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_foldr___redArg___closed__2 = (const lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__2_value;
static const lean_closure_object l_Std_ExtTreeMap_foldr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_foldr___redArg___closed__3 = (const lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__3_value;
static const lean_closure_object l_Std_ExtTreeMap_foldr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_foldr___redArg___closed__4 = (const lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__4_value;
static const lean_closure_object l_Std_ExtTreeMap_foldr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_foldr___redArg___closed__5 = (const lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__5_value;
static const lean_closure_object l_Std_ExtTreeMap_foldr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_foldr___redArg___closed__6 = (const lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__6_value;
static const lean_ctor_object l_Std_ExtTreeMap_foldr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__0_value),((lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__1_value)}};
static const lean_object* l_Std_ExtTreeMap_foldr___redArg___closed__7 = (const lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__7_value;
static const lean_ctor_object l_Std_ExtTreeMap_foldr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__7_value),((lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__2_value),((lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__3_value),((lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__4_value),((lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__5_value)}};
static const lean_object* l_Std_ExtTreeMap_foldr___redArg___closed__8 = (const lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__8_value;
static const lean_ctor_object l_Std_ExtTreeMap_foldr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__8_value),((lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__6_value)}};
static const lean_object* l_Std_ExtTreeMap_foldr___redArg___closed__9 = (const lean_object*)&l_Std_ExtTreeMap_foldr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_ExtTreeMap_partition___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_ExtTreeMap_partition___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeMap_partition___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_ExtTreeMap_any___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_ExtTreeMap_any___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeMap_any___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtTreeMap_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtTreeMap_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_keys___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeMap_keys___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtTreeMap_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtTreeMap_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeMap_keysArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtTreeMap_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtTreeMap_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_values___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeMap_values___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtTreeMap_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtTreeMap_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeMap_valuesArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtTreeMap_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtTreeMap_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_toList___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeMap_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtTreeMap_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_ExtTreeMap_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtTreeMap_toArray___redArg___closed__0 = (const lean_object*)&l_Std_ExtTreeMap_toArray___redArg___closed__0_value;
static const lean_array_object l_Std_ExtTreeMap_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_ExtTreeMap_toArray___redArg___closed__1 = (const lean_object*)&l_Std_ExtTreeMap_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.ExtTreeMap.ofList "};
static const lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__12, &l_Std_ExtTreeMap___auto__1___closed__12_once, _init_l_Std_ExtTreeMap___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__14));
v___x_34_ = lean_string_utf8_byte_size(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__16(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__15, &l_Std_ExtTreeMap___auto__1___closed__15_once, _init_l_Std_ExtTreeMap___auto__1___closed__15);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__14));
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_box(0);
v___x_42_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__17));
v___x_43_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__16, &l_Std_ExtTreeMap___auto__1___closed__16_once, _init_l_Std_ExtTreeMap___auto__1___closed__16);
v___x_44_ = lean_box(2);
v___x_45_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
lean_ctor_set(v___x_45_, 2, v___x_42_);
lean_ctor_set(v___x_45_, 3, v___x_41_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__18, &l_Std_ExtTreeMap___auto__1___closed__18_once, _init_l_Std_ExtTreeMap___auto__1___closed__18);
v___x_47_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__13, &l_Std_ExtTreeMap___auto__1___closed__13_once, _init_l_Std_ExtTreeMap___auto__1___closed__13);
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__19, &l_Std_ExtTreeMap___auto__1___closed__19_once, _init_l_Std_ExtTreeMap___auto__1___closed__19);
v___x_50_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__11));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__21(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__20, &l_Std_ExtTreeMap___auto__1___closed__20_once, _init_l_Std_ExtTreeMap___auto__1___closed__20);
v___x_54_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__5));
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__22(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__21, &l_Std_ExtTreeMap___auto__1___closed__21_once, _init_l_Std_ExtTreeMap___auto__1___closed__21);
v___x_57_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__9));
v___x_58_ = lean_box(2);
v___x_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__23(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__22, &l_Std_ExtTreeMap___auto__1___closed__22_once, _init_l_Std_ExtTreeMap___auto__1___closed__22);
v___x_61_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__24(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__23, &l_Std_ExtTreeMap___auto__1___closed__23_once, _init_l_Std_ExtTreeMap___auto__1___closed__23);
v___x_64_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__7));
v___x_65_ = lean_box(2);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__25(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__24, &l_Std_ExtTreeMap___auto__1___closed__24_once, _init_l_Std_ExtTreeMap___auto__1___closed__24);
v___x_68_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__5));
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1___closed__26(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__25, &l_Std_ExtTreeMap___auto__1___closed__25_once, _init_l_Std_ExtTreeMap___auto__1___closed__25);
v___x_71_ = ((lean_object*)(l_Std_ExtTreeMap___auto__1___closed__4));
v___x_72_ = lean_box(2);
v___x_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_ExtTreeMap___auto__1(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_cmp_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(1);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_empty___boxed(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_cmp_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_ExtTreeMap_empty(v_00_u03b1_79_, v_00_u03b2_80_, v_cmp_81_);
lean_dec_ref(v_cmp_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_cmp_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(1);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_cmp_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_ExtTreeMap_instEmptyCollection(v_00_u03b1_87_, v_00_u03b2_88_, v_cmp_89_);
lean_dec_ref(v_cmp_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_cmp_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(1);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInhabited___boxed(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_cmp_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_ExtTreeMap_instInhabited(v_00_u03b1_95_, v_00_u03b2_96_, v_cmp_97_);
lean_dec_ref(v_cmp_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insert___redArg(lean_object* v_cmp_99_, lean_object* v_l_100_, lean_object* v_a_101_, lean_object* v_b_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_99_, v_a_101_, v_b_102_, v_l_100_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insert(lean_object* v_00_u03b1_104_, lean_object* v_00_u03b2_105_, lean_object* v_cmp_106_, lean_object* v_inst_107_, lean_object* v_l_108_, lean_object* v_a_109_, lean_object* v_b_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_106_, v_a_109_, v_b_110_, v_l_108_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0(lean_object* v_cmp_112_, lean_object* v_e_113_){
_start:
{
lean_object* v_fst_114_; lean_object* v_snd_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_fst_114_ = lean_ctor_get(v_e_113_, 0);
lean_inc(v_fst_114_);
v_snd_115_ = lean_ctor_get(v_e_113_, 1);
lean_inc(v_snd_115_);
lean_dec_ref(v_e_113_);
v___x_116_ = lean_box(1);
v___x_117_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_112_, v_fst_114_, v_snd_115_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg(lean_object* v_cmp_118_){
_start:
{
lean_object* v___f_119_; 
v___f_119_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_119_, 0, v_cmp_118_);
return v___f_119_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSingletonProdOfTransCmp(lean_object* v_00_u03b1_120_, lean_object* v_00_u03b2_121_, lean_object* v_cmp_122_, lean_object* v_inst_123_){
_start:
{
lean_object* v___f_124_; 
v___f_124_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0), 2, 1);
lean_closure_set(v___f_124_, 0, v_cmp_122_);
return v___f_124_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0(lean_object* v_cmp_125_, lean_object* v_e_126_, lean_object* v_s_127_){
_start:
{
lean_object* v_fst_128_; lean_object* v_snd_129_; lean_object* v___x_130_; 
v_fst_128_ = lean_ctor_get(v_e_126_, 0);
lean_inc(v_fst_128_);
v_snd_129_ = lean_ctor_get(v_e_126_, 1);
lean_inc(v_snd_129_);
lean_dec_ref(v_e_126_);
v___x_130_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_125_, v_fst_128_, v_snd_129_, v_s_127_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg(lean_object* v_cmp_131_){
_start:
{
lean_object* v___f_132_; 
v___f_132_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_132_, 0, v_cmp_131_);
return v___f_132_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInsertProdOfTransCmp(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_cmp_135_, lean_object* v_inst_136_){
_start:
{
lean_object* v___f_137_; 
v___f_137_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0), 3, 1);
lean_closure_set(v___f_137_, 0, v_cmp_135_);
return v___f_137_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertIfNew___redArg(lean_object* v_cmp_138_, lean_object* v_t_139_, lean_object* v_a_140_, lean_object* v_b_141_){
_start:
{
uint8_t v___x_142_; 
lean_inc(v_t_139_);
lean_inc(v_a_140_);
lean_inc_ref(v_cmp_138_);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_138_, v_a_140_, v_t_139_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_138_, v_a_140_, v_b_141_, v_t_139_);
return v___x_143_;
}
else
{
lean_dec(v_b_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_cmp_138_);
return v_t_139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertIfNew(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_cmp_146_, lean_object* v_inst_147_, lean_object* v_t_148_, lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
uint8_t v___x_151_; 
lean_inc(v_t_148_);
lean_inc(v_a_149_);
lean_inc_ref(v_cmp_146_);
v___x_151_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_146_, v_a_149_, v_t_148_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_146_, v_a_149_, v_b_150_, v_t_148_);
return v___x_152_;
}
else
{
lean_dec(v_b_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_cmp_146_);
return v_t_148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsert___redArg(lean_object* v_cmp_153_, lean_object* v_t_154_, lean_object* v_a_155_, lean_object* v_b_156_){
_start:
{
lean_object* v_sz_157_; lean_object* v_m_158_; lean_object* v___y_160_; 
v_sz_157_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_154_);
v_m_158_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_153_, v_a_155_, v_b_156_, v_t_154_);
if (lean_obj_tag(v_m_158_) == 0)
{
lean_object* v_size_164_; 
v_size_164_ = lean_ctor_get(v_m_158_, 0);
lean_inc(v_size_164_);
v___y_160_ = v_size_164_;
goto v___jp_159_;
}
else
{
lean_object* v___x_165_; 
v___x_165_ = lean_unsigned_to_nat(0u);
v___y_160_ = v___x_165_;
goto v___jp_159_;
}
v___jp_159_:
{
uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_nat_dec_eq(v_sz_157_, v___y_160_);
lean_dec(v___y_160_);
lean_dec(v_sz_157_);
v___x_162_ = lean_box(v___x_161_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_m_158_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsert(lean_object* v_00_u03b1_166_, lean_object* v_00_u03b2_167_, lean_object* v_cmp_168_, lean_object* v_inst_169_, lean_object* v_t_170_, lean_object* v_a_171_, lean_object* v_b_172_){
_start:
{
lean_object* v_sz_173_; lean_object* v_m_174_; lean_object* v___y_176_; 
v_sz_173_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_170_);
v_m_174_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_168_, v_a_171_, v_b_172_, v_t_170_);
if (lean_obj_tag(v_m_174_) == 0)
{
lean_object* v_size_180_; 
v_size_180_ = lean_ctor_get(v_m_174_, 0);
lean_inc(v_size_180_);
v___y_176_ = v_size_180_;
goto v___jp_175_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___y_176_ = v___x_181_;
goto v___jp_175_;
}
v___jp_175_:
{
uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_nat_dec_eq(v_sz_173_, v___y_176_);
lean_dec(v___y_176_);
lean_dec(v_sz_173_);
v___x_178_ = lean_box(v___x_177_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v_m_174_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsertIfNew___redArg(lean_object* v_cmp_182_, lean_object* v_t_183_, lean_object* v_a_184_, lean_object* v_b_185_){
_start:
{
uint8_t v___x_186_; 
lean_inc(v_t_183_);
lean_inc(v_a_184_);
lean_inc_ref(v_cmp_182_);
v___x_186_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_182_, v_a_184_, v_t_183_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_182_, v_a_184_, v_b_185_, v_t_183_);
v___x_188_ = lean_box(v___x_186_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_187_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v_b_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_cmp_182_);
v___x_190_ = lean_box(v___x_186_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_t_183_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_containsThenInsertIfNew(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_cmp_194_, lean_object* v_inst_195_, lean_object* v_t_196_, lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
uint8_t v___x_199_; 
lean_inc(v_t_196_);
lean_inc(v_a_197_);
lean_inc_ref(v_cmp_194_);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_194_, v_a_197_, v_t_196_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_194_, v_a_197_, v_b_198_, v_t_196_);
v___x_201_ = lean_box(v___x_199_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_b_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_cmp_194_);
v___x_203_ = lean_box(v___x_199_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_t_196_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_205_, lean_object* v_t_206_, lean_object* v_a_207_, lean_object* v_b_208_){
_start:
{
lean_object* v___x_209_; 
lean_inc(v_a_207_);
lean_inc(v_t_206_);
lean_inc_ref(v_cmp_205_);
v___x_209_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_205_, v_t_206_, v_a_207_);
if (lean_obj_tag(v___x_209_) == 0)
{
uint8_t v___x_210_; 
lean_inc(v_t_206_);
lean_inc(v_a_207_);
lean_inc_ref(v_cmp_205_);
v___x_210_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_205_, v_a_207_, v_t_206_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_205_, v_a_207_, v_b_208_, v_t_206_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_209_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; 
lean_dec(v_b_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_cmp_205_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_209_);
lean_ctor_set(v___x_213_, 1, v_t_206_);
return v___x_213_;
}
}
else
{
lean_object* v___x_214_; 
lean_dec(v_b_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_cmp_205_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_209_);
lean_ctor_set(v___x_214_, 1, v_t_206_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, lean_object* v_cmp_217_, lean_object* v_inst_218_, lean_object* v_t_219_, lean_object* v_a_220_, lean_object* v_b_221_){
_start:
{
lean_object* v___x_222_; 
lean_inc(v_a_220_);
lean_inc(v_t_219_);
lean_inc_ref(v_cmp_217_);
v___x_222_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_217_, v_t_219_, v_a_220_);
if (lean_obj_tag(v___x_222_) == 0)
{
uint8_t v___x_223_; 
lean_inc(v_t_219_);
lean_inc(v_a_220_);
lean_inc_ref(v_cmp_217_);
v___x_223_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_217_, v_a_220_, v_t_219_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_217_, v_a_220_, v_b_221_, v_t_219_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_222_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; 
lean_dec(v_b_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_cmp_217_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_222_);
lean_ctor_set(v___x_226_, 1, v_t_219_);
return v___x_226_;
}
}
else
{
lean_object* v___x_227_; 
lean_dec(v_b_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_cmp_217_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_222_);
lean_ctor_set(v___x_227_, 1, v_t_219_);
return v___x_227_;
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_contains___redArg(lean_object* v_cmp_228_, lean_object* v_l_229_, lean_object* v_a_230_){
_start:
{
uint8_t v___x_231_; 
v___x_231_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_228_, v_a_230_, v_l_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_contains___redArg___boxed(lean_object* v_cmp_232_, lean_object* v_l_233_, lean_object* v_a_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Std_ExtTreeMap_contains___redArg(v_cmp_232_, v_l_233_, v_a_234_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_contains(lean_object* v_00_u03b1_237_, lean_object* v_00_u03b2_238_, lean_object* v_cmp_239_, lean_object* v_inst_240_, lean_object* v_l_241_, lean_object* v_a_242_){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_239_, v_a_242_, v_l_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_contains___boxed(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_cmp_246_, lean_object* v_inst_247_, lean_object* v_l_248_, lean_object* v_a_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Std_ExtTreeMap_contains(v_00_u03b1_244_, v_00_u03b2_245_, v_cmp_246_, v_inst_247_, v_l_248_, v_a_249_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_cmp_254_, lean_object* v_inst_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_box(0);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instMembershipOfTransCmp___boxed(lean_object* v_00_u03b1_257_, lean_object* v_00_u03b2_258_, lean_object* v_cmp_259_, lean_object* v_inst_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_ExtTreeMap_instMembershipOfTransCmp(v_00_u03b1_257_, v_00_u03b2_258_, v_cmp_259_, v_inst_260_);
lean_dec_ref(v_cmp_259_);
return v_res_261_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableMem___redArg(lean_object* v_cmp_262_, lean_object* v_m_263_, lean_object* v_a_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_262_, v_a_264_, v_m_263_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableMem___redArg___boxed(lean_object* v_cmp_266_, lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Std_ExtTreeMap_instDecidableMem___redArg(v_cmp_266_, v_m_267_, v_a_268_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableMem(lean_object* v_00_u03b1_271_, lean_object* v_00_u03b2_272_, lean_object* v_cmp_273_, lean_object* v_inst_274_, lean_object* v_m_275_, lean_object* v_a_276_){
_start:
{
uint8_t v___x_277_; 
v___x_277_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_273_, v_a_276_, v_m_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableMem___boxed(lean_object* v_00_u03b1_278_, lean_object* v_00_u03b2_279_, lean_object* v_cmp_280_, lean_object* v_inst_281_, lean_object* v_m_282_, lean_object* v_a_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Std_ExtTreeMap_instDecidableMem(v_00_u03b1_278_, v_00_u03b2_279_, v_cmp_280_, v_inst_281_, v_m_282_, v_a_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___redArg(lean_object* v_t_286_){
_start:
{
if (lean_obj_tag(v_t_286_) == 0)
{
lean_object* v_size_287_; 
v_size_287_ = lean_ctor_get(v_t_286_, 0);
lean_inc(v_size_287_);
return v_size_287_;
}
else
{
lean_object* v___x_288_; 
v___x_288_ = lean_unsigned_to_nat(0u);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___redArg___boxed(lean_object* v_t_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_ExtTreeMap_size___redArg(v_t_289_);
lean_dec(v_t_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size(lean_object* v_00_u03b1_291_, lean_object* v_00_u03b2_292_, lean_object* v_cmp_293_, lean_object* v_t_294_){
_start:
{
if (lean_obj_tag(v_t_294_) == 0)
{
lean_object* v_size_295_; 
v_size_295_ = lean_ctor_get(v_t_294_, 0);
lean_inc(v_size_295_);
return v_size_295_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = lean_unsigned_to_nat(0u);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_size___boxed(lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_cmp_299_, lean_object* v_t_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_ExtTreeMap_size(v_00_u03b1_297_, v_00_u03b2_298_, v_cmp_299_, v_t_300_);
lean_dec(v_t_300_);
lean_dec_ref(v_cmp_299_);
return v_res_301_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_isEmpty___redArg(lean_object* v_t_302_){
_start:
{
if (lean_obj_tag(v_t_302_) == 0)
{
uint8_t v___x_303_; 
v___x_303_ = 0;
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = 1;
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_isEmpty___redArg___boxed(lean_object* v_t_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Std_ExtTreeMap_isEmpty___redArg(v_t_305_);
lean_dec(v_t_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_isEmpty(lean_object* v_00_u03b1_308_, lean_object* v_00_u03b2_309_, lean_object* v_cmp_310_, lean_object* v_t_311_){
_start:
{
if (lean_obj_tag(v_t_311_) == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 0;
return v___x_312_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = 1;
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_isEmpty___boxed(lean_object* v_00_u03b1_314_, lean_object* v_00_u03b2_315_, lean_object* v_cmp_316_, lean_object* v_t_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_Std_ExtTreeMap_isEmpty(v_00_u03b1_314_, v_00_u03b2_315_, v_cmp_316_, v_t_317_);
lean_dec(v_t_317_);
lean_dec_ref(v_cmp_316_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_erase___redArg(lean_object* v_cmp_320_, lean_object* v_t_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_320_, v_a_322_, v_t_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_erase(lean_object* v_00_u03b1_324_, lean_object* v_00_u03b2_325_, lean_object* v_cmp_326_, lean_object* v_inst_327_, lean_object* v_t_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_326_, v_a_329_, v_t_328_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x3f___redArg(lean_object* v_cmp_331_, lean_object* v_t_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_331_, v_t_332_, v_a_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x3f(lean_object* v_00_u03b1_335_, lean_object* v_00_u03b2_336_, lean_object* v_cmp_337_, lean_object* v_inst_338_, lean_object* v_t_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_337_, v_t_339_, v_a_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get___redArg(lean_object* v_cmp_342_, lean_object* v_t_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_342_, v_t_343_, v_a_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get(lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_cmp_348_, lean_object* v_inst_349_, lean_object* v_t_350_, lean_object* v_a_351_, lean_object* v_h_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_348_, v_t_350_, v_a_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___redArg(lean_object* v_cmp_354_, lean_object* v_inst_355_, lean_object* v_t_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_354_, v_inst_355_, v_t_356_, v_a_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21(lean_object* v_00_u03b1_359_, lean_object* v_00_u03b2_360_, lean_object* v_cmp_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_t_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_361_, v_inst_363_, v_t_364_, v_a_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg(lean_object* v_cmp_367_, lean_object* v_t_368_, lean_object* v_a_369_, lean_object* v_fallback_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_367_, v_t_368_, v_a_369_, v_fallback_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg___boxed(lean_object* v_cmp_372_, lean_object* v_t_373_, lean_object* v_a_374_, lean_object* v_fallback_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_ExtTreeMap_getD___redArg(v_cmp_372_, v_t_373_, v_a_374_, v_fallback_375_);
lean_dec(v_fallback_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD(lean_object* v_00_u03b1_377_, lean_object* v_00_u03b2_378_, lean_object* v_cmp_379_, lean_object* v_inst_380_, lean_object* v_t_381_, lean_object* v_a_382_, lean_object* v_fallback_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_379_, v_t_381_, v_a_382_, v_fallback_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___boxed(lean_object* v_00_u03b1_385_, lean_object* v_00_u03b2_386_, lean_object* v_cmp_387_, lean_object* v_inst_388_, lean_object* v_t_389_, lean_object* v_a_390_, lean_object* v_fallback_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_ExtTreeMap_getD(v_00_u03b1_385_, v_00_u03b2_386_, v_cmp_387_, v_inst_388_, v_t_389_, v_a_390_, v_fallback_391_);
lean_dec(v_fallback_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_cmp_393_, lean_object* v_m_394_, lean_object* v_a_395_, lean_object* v_h_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_393_, v_m_394_, v_a_395_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_cmp_398_, lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_398_, v_m_399_, v_a_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_cmp_402_, lean_object* v_inst_403_, lean_object* v_m_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_402_, v_inst_403_, v_m_404_, v_a_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(lean_object* v_cmp_407_){
_start:
{
lean_object* v___f_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___x_411_; 
lean_inc_ref(v_cmp_407_);
v___f_408_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0), 4, 1);
lean_closure_set(v___f_408_, 0, v_cmp_407_);
lean_inc_ref(v_cmp_407_);
v___f_409_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1), 3, 1);
lean_closure_set(v___f_409_, 0, v_cmp_407_);
v___f_410_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2), 4, 1);
lean_closure_set(v___f_410_, 0, v_cmp_407_);
v___x_411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_411_, 0, v___f_408_);
lean_ctor_set(v___x_411_, 1, v___f_409_);
lean_ctor_set(v___x_411_, 2, v___f_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_cmp_414_, lean_object* v_inst_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(v_cmp_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f___redArg(lean_object* v_cmp_417_, lean_object* v_t_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_417_, v_t_418_, v_a_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_cmp_423_, lean_object* v_inst_424_, lean_object* v_t_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_423_, v_t_425_, v_a_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey___redArg(lean_object* v_cmp_428_, lean_object* v_t_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_428_, v_t_429_, v_a_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey(lean_object* v_00_u03b1_432_, lean_object* v_00_u03b2_433_, lean_object* v_cmp_434_, lean_object* v_inst_435_, lean_object* v_t_436_, lean_object* v_a_437_, lean_object* v_h_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_434_, v_t_436_, v_a_437_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg(lean_object* v_cmp_440_, lean_object* v_inst_441_, lean_object* v_t_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_440_, v_t_442_, v_a_443_, v_inst_441_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21(lean_object* v_00_u03b1_445_, lean_object* v_00_u03b2_446_, lean_object* v_cmp_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_t_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_447_, v_t_450_, v_a_451_, v_inst_449_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg(lean_object* v_cmp_453_, lean_object* v_t_454_, lean_object* v_a_455_, lean_object* v_fallback_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_453_, v_t_454_, v_a_455_, v_fallback_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_458_, lean_object* v_t_459_, lean_object* v_a_460_, lean_object* v_fallback_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_ExtTreeMap_getKeyD___redArg(v_cmp_458_, v_t_459_, v_a_460_, v_fallback_461_);
lean_dec(v_fallback_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD(lean_object* v_00_u03b1_463_, lean_object* v_00_u03b2_464_, lean_object* v_cmp_465_, lean_object* v_inst_466_, lean_object* v_t_467_, lean_object* v_a_468_, lean_object* v_fallback_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_465_, v_t_467_, v_a_468_, v_fallback_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_471_, lean_object* v_00_u03b2_472_, lean_object* v_cmp_473_, lean_object* v_inst_474_, lean_object* v_t_475_, lean_object* v_a_476_, lean_object* v_fallback_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_ExtTreeMap_getKeyD(v_00_u03b1_471_, v_00_u03b2_472_, v_cmp_473_, v_inst_474_, v_t_475_, v_a_476_, v_fallback_477_);
lean_dec(v_fallback_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg(lean_object* v_t_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_ExtTreeMap_minEntry_x3f___redArg(v_t_481_);
lean_dec(v_t_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_cmp_485_, lean_object* v_inst_486_, lean_object* v_t_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_489_, lean_object* v_00_u03b2_490_, lean_object* v_cmp_491_, lean_object* v_inst_492_, lean_object* v_t_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_ExtTreeMap_minEntry_x3f(v_00_u03b1_489_, v_00_u03b2_490_, v_cmp_491_, v_inst_492_, v_t_493_);
lean_dec(v_t_493_);
lean_dec_ref(v_cmp_491_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg(lean_object* v_t_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg___boxed(lean_object* v_t_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_ExtTreeMap_minEntry___redArg(v_t_497_);
lean_dec(v_t_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry(lean_object* v_00_u03b1_499_, lean_object* v_00_u03b2_500_, lean_object* v_cmp_501_, lean_object* v_inst_502_, lean_object* v_t_503_, lean_object* v_h_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___boxed(lean_object* v_00_u03b1_506_, lean_object* v_00_u03b2_507_, lean_object* v_cmp_508_, lean_object* v_inst_509_, lean_object* v_t_510_, lean_object* v_h_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_ExtTreeMap_minEntry(v_00_u03b1_506_, v_00_u03b2_507_, v_cmp_508_, v_inst_509_, v_t_510_, v_h_511_);
lean_dec(v_t_510_);
lean_dec_ref(v_cmp_508_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg(lean_object* v_inst_513_, lean_object* v_t_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_513_, v_t_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_516_, lean_object* v_t_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_ExtTreeMap_minEntry_x21___redArg(v_inst_516_, v_t_517_);
lean_dec(v_t_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_cmp_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_t_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_523_, v_t_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b2_527_, lean_object* v_cmp_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_t_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_ExtTreeMap_minEntry_x21(v_00_u03b1_526_, v_00_u03b2_527_, v_cmp_528_, v_inst_529_, v_inst_530_, v_t_531_);
lean_dec(v_t_531_);
lean_dec_ref(v_cmp_528_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg(lean_object* v_t_533_, lean_object* v_fallback_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_533_, v_fallback_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg___boxed(lean_object* v_t_536_, lean_object* v_fallback_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_ExtTreeMap_minEntryD___redArg(v_t_536_, v_fallback_537_);
lean_dec_ref(v_fallback_537_);
lean_dec(v_t_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD(lean_object* v_00_u03b1_539_, lean_object* v_00_u03b2_540_, lean_object* v_cmp_541_, lean_object* v_inst_542_, lean_object* v_t_543_, lean_object* v_fallback_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_543_, v_fallback_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_cmp_548_, lean_object* v_inst_549_, lean_object* v_t_550_, lean_object* v_fallback_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_ExtTreeMap_minEntryD(v_00_u03b1_546_, v_00_u03b2_547_, v_cmp_548_, v_inst_549_, v_t_550_, v_fallback_551_);
lean_dec_ref(v_fallback_551_);
lean_dec(v_t_550_);
lean_dec_ref(v_cmp_548_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg(lean_object* v_t_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_ExtTreeMap_maxEntry_x3f___redArg(v_t_555_);
lean_dec(v_t_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_557_, lean_object* v_00_u03b2_558_, lean_object* v_cmp_559_, lean_object* v_inst_560_, lean_object* v_t_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_563_, lean_object* v_00_u03b2_564_, lean_object* v_cmp_565_, lean_object* v_inst_566_, lean_object* v_t_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_ExtTreeMap_maxEntry_x3f(v_00_u03b1_563_, v_00_u03b2_564_, v_cmp_565_, v_inst_566_, v_t_567_);
lean_dec(v_t_567_);
lean_dec_ref(v_cmp_565_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg(lean_object* v_t_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg___boxed(lean_object* v_t_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_ExtTreeMap_maxEntry___redArg(v_t_571_);
lean_dec(v_t_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_cmp_575_, lean_object* v_inst_576_, lean_object* v_t_577_, lean_object* v_h_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_580_, lean_object* v_00_u03b2_581_, lean_object* v_cmp_582_, lean_object* v_inst_583_, lean_object* v_t_584_, lean_object* v_h_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_ExtTreeMap_maxEntry(v_00_u03b1_580_, v_00_u03b2_581_, v_cmp_582_, v_inst_583_, v_t_584_, v_h_585_);
lean_dec(v_t_584_);
lean_dec_ref(v_cmp_582_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg(lean_object* v_inst_587_, lean_object* v_t_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_587_, v_t_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_590_, lean_object* v_t_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Std_ExtTreeMap_maxEntry_x21___redArg(v_inst_590_, v_t_591_);
lean_dec(v_t_591_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21(lean_object* v_00_u03b1_593_, lean_object* v_00_u03b2_594_, lean_object* v_cmp_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_t_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_597_, v_t_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_600_, lean_object* v_00_u03b2_601_, lean_object* v_cmp_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_t_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_ExtTreeMap_maxEntry_x21(v_00_u03b1_600_, v_00_u03b2_601_, v_cmp_602_, v_inst_603_, v_inst_604_, v_t_605_);
lean_dec(v_t_605_);
lean_dec_ref(v_cmp_602_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg(lean_object* v_t_607_, lean_object* v_fallback_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_607_, v_fallback_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_610_, lean_object* v_fallback_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_ExtTreeMap_maxEntryD___redArg(v_t_610_, v_fallback_611_);
lean_dec_ref(v_fallback_611_);
lean_dec(v_t_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD(lean_object* v_00_u03b1_613_, lean_object* v_00_u03b2_614_, lean_object* v_cmp_615_, lean_object* v_inst_616_, lean_object* v_t_617_, lean_object* v_fallback_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_617_, v_fallback_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_620_, lean_object* v_00_u03b2_621_, lean_object* v_cmp_622_, lean_object* v_inst_623_, lean_object* v_t_624_, lean_object* v_fallback_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_ExtTreeMap_maxEntryD(v_00_u03b1_620_, v_00_u03b2_621_, v_cmp_622_, v_inst_623_, v_t_624_, v_fallback_625_);
lean_dec_ref(v_fallback_625_);
lean_dec(v_t_624_);
lean_dec_ref(v_cmp_622_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg(lean_object* v_t_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_ExtTreeMap_minKey_x3f___redArg(v_t_629_);
lean_dec(v_t_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f(lean_object* v_00_u03b1_631_, lean_object* v_00_u03b2_632_, lean_object* v_cmp_633_, lean_object* v_inst_634_, lean_object* v_t_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_cmp_639_, lean_object* v_inst_640_, lean_object* v_t_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_ExtTreeMap_minKey_x3f(v_00_u03b1_637_, v_00_u03b2_638_, v_cmp_639_, v_inst_640_, v_t_641_);
lean_dec(v_t_641_);
lean_dec_ref(v_cmp_639_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg(lean_object* v_t_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg___boxed(lean_object* v_t_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_ExtTreeMap_minKey___redArg(v_t_645_);
lean_dec(v_t_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey(lean_object* v_00_u03b1_647_, lean_object* v_00_u03b2_648_, lean_object* v_cmp_649_, lean_object* v_inst_650_, lean_object* v_t_651_, lean_object* v_h_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___boxed(lean_object* v_00_u03b1_654_, lean_object* v_00_u03b2_655_, lean_object* v_cmp_656_, lean_object* v_inst_657_, lean_object* v_t_658_, lean_object* v_h_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_ExtTreeMap_minKey(v_00_u03b1_654_, v_00_u03b2_655_, v_cmp_656_, v_inst_657_, v_t_658_, v_h_659_);
lean_dec(v_t_658_);
lean_dec_ref(v_cmp_656_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg(lean_object* v_inst_661_, lean_object* v_t_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_661_, v_t_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_664_, lean_object* v_t_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_ExtTreeMap_minKey_x21___redArg(v_inst_664_, v_t_665_);
lean_dec(v_t_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21(lean_object* v_00_u03b1_667_, lean_object* v_00_u03b2_668_, lean_object* v_cmp_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_t_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_671_, v_t_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_cmp_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_t_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_ExtTreeMap_minKey_x21(v_00_u03b1_674_, v_00_u03b2_675_, v_cmp_676_, v_inst_677_, v_inst_678_, v_t_679_);
lean_dec(v_t_679_);
lean_dec_ref(v_cmp_676_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg(lean_object* v_t_681_, lean_object* v_fallback_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_681_, v_fallback_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg___boxed(lean_object* v_t_684_, lean_object* v_fallback_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Std_ExtTreeMap_minKeyD___redArg(v_t_684_, v_fallback_685_);
lean_dec(v_fallback_685_);
lean_dec(v_t_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD(lean_object* v_00_u03b1_687_, lean_object* v_00_u03b2_688_, lean_object* v_cmp_689_, lean_object* v_inst_690_, lean_object* v_t_691_, lean_object* v_fallback_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_691_, v_fallback_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_694_, lean_object* v_00_u03b2_695_, lean_object* v_cmp_696_, lean_object* v_inst_697_, lean_object* v_t_698_, lean_object* v_fallback_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Std_ExtTreeMap_minKeyD(v_00_u03b1_694_, v_00_u03b2_695_, v_cmp_696_, v_inst_697_, v_t_698_, v_fallback_699_);
lean_dec(v_fallback_699_);
lean_dec(v_t_698_);
lean_dec_ref(v_cmp_696_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg(lean_object* v_t_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_ExtTreeMap_maxKey_x3f___redArg(v_t_703_);
lean_dec(v_t_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b2_706_, lean_object* v_cmp_707_, lean_object* v_inst_708_, lean_object* v_t_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_711_, lean_object* v_00_u03b2_712_, lean_object* v_cmp_713_, lean_object* v_inst_714_, lean_object* v_t_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_ExtTreeMap_maxKey_x3f(v_00_u03b1_711_, v_00_u03b2_712_, v_cmp_713_, v_inst_714_, v_t_715_);
lean_dec(v_t_715_);
lean_dec_ref(v_cmp_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg(lean_object* v_t_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg___boxed(lean_object* v_t_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_ExtTreeMap_maxKey___redArg(v_t_719_);
lean_dec(v_t_719_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey(lean_object* v_00_u03b1_721_, lean_object* v_00_u03b2_722_, lean_object* v_cmp_723_, lean_object* v_inst_724_, lean_object* v_t_725_, lean_object* v_h_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___boxed(lean_object* v_00_u03b1_728_, lean_object* v_00_u03b2_729_, lean_object* v_cmp_730_, lean_object* v_inst_731_, lean_object* v_t_732_, lean_object* v_h_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_ExtTreeMap_maxKey(v_00_u03b1_728_, v_00_u03b2_729_, v_cmp_730_, v_inst_731_, v_t_732_, v_h_733_);
lean_dec(v_t_732_);
lean_dec_ref(v_cmp_730_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg(lean_object* v_inst_735_, lean_object* v_t_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_735_, v_t_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_738_, lean_object* v_t_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_ExtTreeMap_maxKey_x21___redArg(v_inst_738_, v_t_739_);
lean_dec(v_t_739_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21(lean_object* v_00_u03b1_741_, lean_object* v_00_u03b2_742_, lean_object* v_cmp_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_t_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_745_, v_t_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_748_, lean_object* v_00_u03b2_749_, lean_object* v_cmp_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_t_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_ExtTreeMap_maxKey_x21(v_00_u03b1_748_, v_00_u03b2_749_, v_cmp_750_, v_inst_751_, v_inst_752_, v_t_753_);
lean_dec(v_t_753_);
lean_dec_ref(v_cmp_750_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg(lean_object* v_t_755_, lean_object* v_fallback_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_755_, v_fallback_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_758_, lean_object* v_fallback_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_ExtTreeMap_maxKeyD___redArg(v_t_758_, v_fallback_759_);
lean_dec(v_fallback_759_);
lean_dec(v_t_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD(lean_object* v_00_u03b1_761_, lean_object* v_00_u03b2_762_, lean_object* v_cmp_763_, lean_object* v_inst_764_, lean_object* v_t_765_, lean_object* v_fallback_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_765_, v_fallback_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_768_, lean_object* v_00_u03b2_769_, lean_object* v_cmp_770_, lean_object* v_inst_771_, lean_object* v_t_772_, lean_object* v_fallback_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_ExtTreeMap_maxKeyD(v_00_u03b1_768_, v_00_u03b2_769_, v_cmp_770_, v_inst_771_, v_t_772_, v_fallback_773_);
lean_dec(v_fallback_773_);
lean_dec(v_t_772_);
lean_dec_ref(v_cmp_770_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_775_, lean_object* v_n_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_775_, v_n_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_778_, lean_object* v_n_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(v_t_778_, v_n_779_);
lean_dec(v_t_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_781_, lean_object* v_00_u03b2_782_, lean_object* v_cmp_783_, lean_object* v_inst_784_, lean_object* v_t_785_, lean_object* v_n_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_785_, v_n_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_788_, lean_object* v_00_u03b2_789_, lean_object* v_cmp_790_, lean_object* v_inst_791_, lean_object* v_t_792_, lean_object* v_n_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_ExtTreeMap_entryAtIdx_x3f(v_00_u03b1_788_, v_00_u03b2_789_, v_cmp_790_, v_inst_791_, v_t_792_, v_n_793_);
lean_dec(v_t_792_);
lean_dec_ref(v_cmp_790_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg(lean_object* v_t_795_, lean_object* v_n_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_795_, v_n_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_798_, lean_object* v_n_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_ExtTreeMap_entryAtIdx___redArg(v_t_798_, v_n_799_);
lean_dec(v_t_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_cmp_803_, lean_object* v_inst_804_, lean_object* v_t_805_, lean_object* v_n_806_, lean_object* v_h_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_805_, v_n_806_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_809_, lean_object* v_00_u03b2_810_, lean_object* v_cmp_811_, lean_object* v_inst_812_, lean_object* v_t_813_, lean_object* v_n_814_, lean_object* v_h_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_ExtTreeMap_entryAtIdx(v_00_u03b1_809_, v_00_u03b2_810_, v_cmp_811_, v_inst_812_, v_t_813_, v_n_814_, v_h_815_);
lean_dec(v_t_813_);
lean_dec_ref(v_cmp_811_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_817_, lean_object* v_t_818_, lean_object* v_n_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_817_, v_t_818_, v_n_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_821_, lean_object* v_t_822_, lean_object* v_n_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_ExtTreeMap_entryAtIdx_x21___redArg(v_inst_821_, v_t_822_, v_n_823_);
lean_dec(v_t_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_cmp_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_t_830_, lean_object* v_n_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_829_, v_t_830_, v_n_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_cmp_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_t_838_, lean_object* v_n_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_ExtTreeMap_entryAtIdx_x21(v_00_u03b1_833_, v_00_u03b2_834_, v_cmp_835_, v_inst_836_, v_inst_837_, v_t_838_, v_n_839_);
lean_dec(v_t_838_);
lean_dec_ref(v_cmp_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg(lean_object* v_t_841_, lean_object* v_n_842_, lean_object* v_fallback_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_841_, v_n_842_, v_fallback_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_845_, lean_object* v_n_846_, lean_object* v_fallback_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_ExtTreeMap_entryAtIdxD___redArg(v_t_845_, v_n_846_, v_fallback_847_);
lean_dec_ref(v_fallback_847_);
lean_dec(v_t_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD(lean_object* v_00_u03b1_849_, lean_object* v_00_u03b2_850_, lean_object* v_cmp_851_, lean_object* v_inst_852_, lean_object* v_t_853_, lean_object* v_n_854_, lean_object* v_fallback_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_853_, v_n_854_, v_fallback_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_857_, lean_object* v_00_u03b2_858_, lean_object* v_cmp_859_, lean_object* v_inst_860_, lean_object* v_t_861_, lean_object* v_n_862_, lean_object* v_fallback_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_ExtTreeMap_entryAtIdxD(v_00_u03b1_857_, v_00_u03b2_858_, v_cmp_859_, v_inst_860_, v_t_861_, v_n_862_, v_fallback_863_);
lean_dec_ref(v_fallback_863_);
lean_dec(v_t_861_);
lean_dec_ref(v_cmp_859_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_865_, lean_object* v_n_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_865_, v_n_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_868_, lean_object* v_n_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(v_t_868_, v_n_869_);
lean_dec(v_t_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_cmp_873_, lean_object* v_inst_874_, lean_object* v_t_875_, lean_object* v_n_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_875_, v_n_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_878_, lean_object* v_00_u03b2_879_, lean_object* v_cmp_880_, lean_object* v_inst_881_, lean_object* v_t_882_, lean_object* v_n_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_ExtTreeMap_keyAtIdx_x3f(v_00_u03b1_878_, v_00_u03b2_879_, v_cmp_880_, v_inst_881_, v_t_882_, v_n_883_);
lean_dec(v_t_882_);
lean_dec_ref(v_cmp_880_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg(lean_object* v_t_885_, lean_object* v_n_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_885_, v_n_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_888_, lean_object* v_n_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_ExtTreeMap_keyAtIdx___redArg(v_t_888_, v_n_889_);
lean_dec(v_t_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_cmp_893_, lean_object* v_inst_894_, lean_object* v_t_895_, lean_object* v_n_896_, lean_object* v_h_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_895_, v_n_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_899_, lean_object* v_00_u03b2_900_, lean_object* v_cmp_901_, lean_object* v_inst_902_, lean_object* v_t_903_, lean_object* v_n_904_, lean_object* v_h_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_ExtTreeMap_keyAtIdx(v_00_u03b1_899_, v_00_u03b2_900_, v_cmp_901_, v_inst_902_, v_t_903_, v_n_904_, v_h_905_);
lean_dec(v_t_903_);
lean_dec_ref(v_cmp_901_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_907_, lean_object* v_t_908_, lean_object* v_n_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_907_, v_t_908_, v_n_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_911_, lean_object* v_t_912_, lean_object* v_n_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_ExtTreeMap_keyAtIdx_x21___redArg(v_inst_911_, v_t_912_, v_n_913_);
lean_dec(v_t_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_915_, lean_object* v_00_u03b2_916_, lean_object* v_cmp_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_t_920_, lean_object* v_n_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_919_, v_t_920_, v_n_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_923_, lean_object* v_00_u03b2_924_, lean_object* v_cmp_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_t_928_, lean_object* v_n_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Std_ExtTreeMap_keyAtIdx_x21(v_00_u03b1_923_, v_00_u03b2_924_, v_cmp_925_, v_inst_926_, v_inst_927_, v_t_928_, v_n_929_);
lean_dec(v_t_928_);
lean_dec_ref(v_cmp_925_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg(lean_object* v_t_931_, lean_object* v_n_932_, lean_object* v_fallback_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_931_, v_n_932_, v_fallback_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_935_, lean_object* v_n_936_, lean_object* v_fallback_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_ExtTreeMap_keyAtIdxD___redArg(v_t_935_, v_n_936_, v_fallback_937_);
lean_dec(v_fallback_937_);
lean_dec(v_t_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD(lean_object* v_00_u03b1_939_, lean_object* v_00_u03b2_940_, lean_object* v_cmp_941_, lean_object* v_inst_942_, lean_object* v_t_943_, lean_object* v_n_944_, lean_object* v_fallback_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_943_, v_n_944_, v_fallback_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_947_, lean_object* v_00_u03b2_948_, lean_object* v_cmp_949_, lean_object* v_inst_950_, lean_object* v_t_951_, lean_object* v_n_952_, lean_object* v_fallback_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_ExtTreeMap_keyAtIdxD(v_00_u03b1_947_, v_00_u03b2_948_, v_cmp_949_, v_inst_950_, v_t_951_, v_n_952_, v_fallback_953_);
lean_dec(v_fallback_953_);
lean_dec(v_t_951_);
lean_dec_ref(v_cmp_949_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_955_, lean_object* v_t_956_, lean_object* v_k_957_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_box(0);
v___x_959_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_955_, v_k_957_, v___x_958_, v_t_956_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_960_, lean_object* v_00_u03b2_961_, lean_object* v_cmp_962_, lean_object* v_inst_963_, lean_object* v_t_964_, lean_object* v_k_965_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_box(0);
v___x_967_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_962_, v_k_965_, v___x_966_, v_t_964_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_968_, lean_object* v_t_969_, lean_object* v_k_970_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_box(0);
v___x_972_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_968_, v_k_970_, v___x_971_, v_t_969_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_973_, lean_object* v_00_u03b2_974_, lean_object* v_cmp_975_, lean_object* v_inst_976_, lean_object* v_t_977_, lean_object* v_k_978_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_box(0);
v___x_980_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_975_, v_k_978_, v___x_979_, v_t_977_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_981_, lean_object* v_t_982_, lean_object* v_k_983_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_box(0);
v___x_985_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_981_, v_k_983_, v___x_984_, v_t_982_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_986_, lean_object* v_00_u03b2_987_, lean_object* v_cmp_988_, lean_object* v_inst_989_, lean_object* v_t_990_, lean_object* v_k_991_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_box(0);
v___x_993_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_988_, v_k_991_, v___x_992_, v_t_990_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_994_, lean_object* v_t_995_, lean_object* v_k_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_box(0);
v___x_998_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_994_, v_k_996_, v___x_997_, v_t_995_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_999_, lean_object* v_00_u03b2_1000_, lean_object* v_cmp_1001_, lean_object* v_inst_1002_, lean_object* v_t_1003_, lean_object* v_k_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_box(0);
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1001_, v_k_1004_, v___x_1005_, v_t_1003_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE___redArg(lean_object* v_cmp_1007_, lean_object* v_t_1008_, lean_object* v_k_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_1007_, v_k_1009_, v_t_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE(lean_object* v_00_u03b1_1011_, lean_object* v_00_u03b2_1012_, lean_object* v_cmp_1013_, lean_object* v_inst_1014_, lean_object* v_t_1015_, lean_object* v_k_1016_, lean_object* v_h_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_1013_, v_k_1016_, v_t_1015_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT___redArg(lean_object* v_cmp_1019_, lean_object* v_t_1020_, lean_object* v_k_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_1019_, v_k_1021_, v_t_1020_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT(lean_object* v_00_u03b1_1023_, lean_object* v_00_u03b2_1024_, lean_object* v_cmp_1025_, lean_object* v_inst_1026_, lean_object* v_t_1027_, lean_object* v_k_1028_, lean_object* v_h_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_1025_, v_k_1028_, v_t_1027_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE___redArg(lean_object* v_cmp_1031_, lean_object* v_t_1032_, lean_object* v_k_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_1031_, v_k_1033_, v_t_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE(lean_object* v_00_u03b1_1035_, lean_object* v_00_u03b2_1036_, lean_object* v_cmp_1037_, lean_object* v_inst_1038_, lean_object* v_t_1039_, lean_object* v_k_1040_, lean_object* v_h_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_1037_, v_k_1040_, v_t_1039_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT___redArg(lean_object* v_cmp_1043_, lean_object* v_t_1044_, lean_object* v_k_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_1043_, v_k_1045_, v_t_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT(lean_object* v_00_u03b1_1047_, lean_object* v_00_u03b2_1048_, lean_object* v_cmp_1049_, lean_object* v_inst_1050_, lean_object* v_t_1051_, lean_object* v_k_1052_, lean_object* v_h_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_1049_, v_k_1052_, v_t_1051_);
return v___x_1054_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1058_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1059_ = lean_unsigned_to_nat(14u);
v___x_1060_ = lean_unsigned_to_nat(22u);
v___x_1061_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1062_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1063_ = l_mkPanicMessageWithDecl(v___x_1062_, v___x_1061_, v___x_1060_, v___x_1059_, v___x_1058_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1064_, lean_object* v_inst_1065_, lean_object* v_t_1066_, lean_object* v_k_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1064_, v_k_1067_, v___x_1068_, v_t_1066_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1071_ = l_panic___redArg(v_inst_1065_, v___x_1070_);
return v___x_1071_;
}
else
{
lean_object* v_val_1072_; 
lean_dec_ref(v_inst_1065_);
v_val_1072_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_val_1072_);
lean_dec_ref(v___x_1069_);
return v_val_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1073_, lean_object* v_00_u03b2_1074_, lean_object* v_cmp_1075_, lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_t_1078_, lean_object* v_k_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1075_, v_k_1079_, v___x_1080_, v_t_1078_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1083_ = l_panic___redArg(v_inst_1077_, v___x_1082_);
return v___x_1083_;
}
else
{
lean_object* v_val_1084_; 
lean_dec_ref(v_inst_1077_);
v_val_1084_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_val_1084_);
lean_dec_ref(v___x_1081_);
return v_val_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1085_, lean_object* v_inst_1086_, lean_object* v_t_1087_, lean_object* v_k_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1085_, v_k_1088_, v___x_1089_, v_t_1087_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1092_ = l_panic___redArg(v_inst_1086_, v___x_1091_);
return v___x_1092_;
}
else
{
lean_object* v_val_1093_; 
lean_dec_ref(v_inst_1086_);
v_val_1093_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_val_1093_);
lean_dec_ref(v___x_1090_);
return v_val_1093_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1094_, lean_object* v_00_u03b2_1095_, lean_object* v_cmp_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_t_1099_, lean_object* v_k_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_box(0);
v___x_1102_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1096_, v_k_1100_, v___x_1101_, v_t_1099_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1104_ = l_panic___redArg(v_inst_1098_, v___x_1103_);
return v___x_1104_;
}
else
{
lean_object* v_val_1105_; 
lean_dec_ref(v_inst_1098_);
v_val_1105_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_val_1105_);
lean_dec_ref(v___x_1102_);
return v_val_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1106_, lean_object* v_inst_1107_, lean_object* v_t_1108_, lean_object* v_k_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1106_, v_k_1109_, v___x_1110_, v_t_1108_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1113_ = l_panic___redArg(v_inst_1107_, v___x_1112_);
return v___x_1113_;
}
else
{
lean_object* v_val_1114_; 
lean_dec_ref(v_inst_1107_);
v_val_1114_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_val_1114_);
lean_dec_ref(v___x_1111_);
return v_val_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1115_, lean_object* v_00_u03b2_1116_, lean_object* v_cmp_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_t_1120_, lean_object* v_k_1121_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_box(0);
v___x_1123_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1117_, v_k_1121_, v___x_1122_, v_t_1120_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1125_ = l_panic___redArg(v_inst_1119_, v___x_1124_);
return v___x_1125_;
}
else
{
lean_object* v_val_1126_; 
lean_dec_ref(v_inst_1119_);
v_val_1126_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_val_1126_);
lean_dec_ref(v___x_1123_);
return v_val_1126_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1127_, lean_object* v_inst_1128_, lean_object* v_t_1129_, lean_object* v_k_1130_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_box(0);
v___x_1132_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1127_, v_k_1130_, v___x_1131_, v_t_1129_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1134_ = l_panic___redArg(v_inst_1128_, v___x_1133_);
return v___x_1134_;
}
else
{
lean_object* v_val_1135_; 
lean_dec_ref(v_inst_1128_);
v_val_1135_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_val_1135_);
lean_dec_ref(v___x_1132_);
return v_val_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_cmp_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_t_1141_, lean_object* v_k_1142_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_box(0);
v___x_1144_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1138_, v_k_1142_, v___x_1143_, v_t_1141_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1146_ = l_panic___redArg(v_inst_1140_, v___x_1145_);
return v___x_1146_;
}
else
{
lean_object* v_val_1147_; 
lean_dec_ref(v_inst_1140_);
v_val_1147_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_val_1147_);
lean_dec_ref(v___x_1144_);
return v_val_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg(lean_object* v_cmp_1148_, lean_object* v_t_1149_, lean_object* v_k_1150_, lean_object* v_fallback_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_box(0);
v___x_1153_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1148_, v_k_1150_, v___x_1152_, v_t_1149_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_inc_ref(v_fallback_1151_);
return v_fallback_1151_;
}
else
{
lean_object* v_val_1154_; 
v_val_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_val_1154_);
lean_dec_ref(v___x_1153_);
return v_val_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1155_, lean_object* v_t_1156_, lean_object* v_k_1157_, lean_object* v_fallback_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Std_ExtTreeMap_getEntryGED___redArg(v_cmp_1155_, v_t_1156_, v_k_1157_, v_fallback_1158_);
lean_dec_ref(v_fallback_1158_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED(lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_cmp_1162_, lean_object* v_inst_1163_, lean_object* v_t_1164_, lean_object* v_k_1165_, lean_object* v_fallback_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1162_, v_k_1165_, v___x_1167_, v_t_1164_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_inc_ref(v_fallback_1166_);
return v_fallback_1166_;
}
else
{
lean_object* v_val_1169_; 
v_val_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_val_1169_);
lean_dec_ref(v___x_1168_);
return v_val_1169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1170_, lean_object* v_00_u03b2_1171_, lean_object* v_cmp_1172_, lean_object* v_inst_1173_, lean_object* v_t_1174_, lean_object* v_k_1175_, lean_object* v_fallback_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_ExtTreeMap_getEntryGED(v_00_u03b1_1170_, v_00_u03b2_1171_, v_cmp_1172_, v_inst_1173_, v_t_1174_, v_k_1175_, v_fallback_1176_);
lean_dec_ref(v_fallback_1176_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1178_, lean_object* v_t_1179_, lean_object* v_k_1180_, lean_object* v_fallback_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1178_, v_k_1180_, v___x_1182_, v_t_1179_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_inc_ref(v_fallback_1181_);
return v_fallback_1181_;
}
else
{
lean_object* v_val_1184_; 
v_val_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_val_1184_);
lean_dec_ref(v___x_1183_);
return v_val_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1185_, lean_object* v_t_1186_, lean_object* v_k_1187_, lean_object* v_fallback_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Std_ExtTreeMap_getEntryGTD___redArg(v_cmp_1185_, v_t_1186_, v_k_1187_, v_fallback_1188_);
lean_dec_ref(v_fallback_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD(lean_object* v_00_u03b1_1190_, lean_object* v_00_u03b2_1191_, lean_object* v_cmp_1192_, lean_object* v_inst_1193_, lean_object* v_t_1194_, lean_object* v_k_1195_, lean_object* v_fallback_1196_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_box(0);
v___x_1198_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1192_, v_k_1195_, v___x_1197_, v_t_1194_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_inc_ref(v_fallback_1196_);
return v_fallback_1196_;
}
else
{
lean_object* v_val_1199_; 
v_val_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_val_1199_);
lean_dec_ref(v___x_1198_);
return v_val_1199_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1200_, lean_object* v_00_u03b2_1201_, lean_object* v_cmp_1202_, lean_object* v_inst_1203_, lean_object* v_t_1204_, lean_object* v_k_1205_, lean_object* v_fallback_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_ExtTreeMap_getEntryGTD(v_00_u03b1_1200_, v_00_u03b2_1201_, v_cmp_1202_, v_inst_1203_, v_t_1204_, v_k_1205_, v_fallback_1206_);
lean_dec_ref(v_fallback_1206_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg(lean_object* v_cmp_1208_, lean_object* v_t_1209_, lean_object* v_k_1210_, lean_object* v_fallback_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1208_, v_k_1210_, v___x_1212_, v_t_1209_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_inc_ref(v_fallback_1211_);
return v_fallback_1211_;
}
else
{
lean_object* v_val_1214_; 
v_val_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_val_1214_);
lean_dec_ref(v___x_1213_);
return v_val_1214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1215_, lean_object* v_t_1216_, lean_object* v_k_1217_, lean_object* v_fallback_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_ExtTreeMap_getEntryLED___redArg(v_cmp_1215_, v_t_1216_, v_k_1217_, v_fallback_1218_);
lean_dec_ref(v_fallback_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED(lean_object* v_00_u03b1_1220_, lean_object* v_00_u03b2_1221_, lean_object* v_cmp_1222_, lean_object* v_inst_1223_, lean_object* v_t_1224_, lean_object* v_k_1225_, lean_object* v_fallback_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_box(0);
v___x_1228_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1222_, v_k_1225_, v___x_1227_, v_t_1224_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_inc_ref(v_fallback_1226_);
return v_fallback_1226_;
}
else
{
lean_object* v_val_1229_; 
v_val_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_val_1229_);
lean_dec_ref(v___x_1228_);
return v_val_1229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1230_, lean_object* v_00_u03b2_1231_, lean_object* v_cmp_1232_, lean_object* v_inst_1233_, lean_object* v_t_1234_, lean_object* v_k_1235_, lean_object* v_fallback_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Std_ExtTreeMap_getEntryLED(v_00_u03b1_1230_, v_00_u03b2_1231_, v_cmp_1232_, v_inst_1233_, v_t_1234_, v_k_1235_, v_fallback_1236_);
lean_dec_ref(v_fallback_1236_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1238_, lean_object* v_t_1239_, lean_object* v_k_1240_, lean_object* v_fallback_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_box(0);
v___x_1243_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1238_, v_k_1240_, v___x_1242_, v_t_1239_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_inc_ref(v_fallback_1241_);
return v_fallback_1241_;
}
else
{
lean_object* v_val_1244_; 
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1244_);
lean_dec_ref(v___x_1243_);
return v_val_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1245_, lean_object* v_t_1246_, lean_object* v_k_1247_, lean_object* v_fallback_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_ExtTreeMap_getEntryLTD___redArg(v_cmp_1245_, v_t_1246_, v_k_1247_, v_fallback_1248_);
lean_dec_ref(v_fallback_1248_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD(lean_object* v_00_u03b1_1250_, lean_object* v_00_u03b2_1251_, lean_object* v_cmp_1252_, lean_object* v_inst_1253_, lean_object* v_t_1254_, lean_object* v_k_1255_, lean_object* v_fallback_1256_){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_box(0);
v___x_1258_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1252_, v_k_1255_, v___x_1257_, v_t_1254_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_inc_ref(v_fallback_1256_);
return v_fallback_1256_;
}
else
{
lean_object* v_val_1259_; 
v_val_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_val_1259_);
lean_dec_ref(v___x_1258_);
return v_val_1259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_00_u03b2_1261_, lean_object* v_cmp_1262_, lean_object* v_inst_1263_, lean_object* v_t_1264_, lean_object* v_k_1265_, lean_object* v_fallback_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_ExtTreeMap_getEntryLTD(v_00_u03b1_1260_, v_00_u03b2_1261_, v_cmp_1262_, v_inst_1263_, v_t_1264_, v_k_1265_, v_fallback_1266_);
lean_dec_ref(v_fallback_1266_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1268_, lean_object* v_t_1269_, lean_object* v_k_1270_){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_box(0);
v___x_1272_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1268_, v_k_1270_, v___x_1271_, v_t_1269_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1273_, lean_object* v_00_u03b2_1274_, lean_object* v_cmp_1275_, lean_object* v_inst_1276_, lean_object* v_t_1277_, lean_object* v_k_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_box(0);
v___x_1280_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1275_, v_k_1278_, v___x_1279_, v_t_1277_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1281_, lean_object* v_t_1282_, lean_object* v_k_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_box(0);
v___x_1285_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1281_, v_k_1283_, v___x_1284_, v_t_1282_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1286_, lean_object* v_00_u03b2_1287_, lean_object* v_cmp_1288_, lean_object* v_inst_1289_, lean_object* v_t_1290_, lean_object* v_k_1291_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_box(0);
v___x_1293_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1288_, v_k_1291_, v___x_1292_, v_t_1290_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1294_, lean_object* v_t_1295_, lean_object* v_k_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_box(0);
v___x_1298_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1294_, v_k_1296_, v___x_1297_, v_t_1295_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1299_, lean_object* v_00_u03b2_1300_, lean_object* v_cmp_1301_, lean_object* v_inst_1302_, lean_object* v_t_1303_, lean_object* v_k_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_box(0);
v___x_1306_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1301_, v_k_1304_, v___x_1305_, v_t_1303_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1307_, lean_object* v_t_1308_, lean_object* v_k_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_box(0);
v___x_1311_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1307_, v_k_1309_, v___x_1310_, v_t_1308_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1312_, lean_object* v_00_u03b2_1313_, lean_object* v_cmp_1314_, lean_object* v_inst_1315_, lean_object* v_t_1316_, lean_object* v_k_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_box(0);
v___x_1319_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1314_, v_k_1317_, v___x_1318_, v_t_1316_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE___redArg(lean_object* v_cmp_1320_, lean_object* v_t_1321_, lean_object* v_k_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1320_, v_k_1322_, v_t_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE(lean_object* v_00_u03b1_1324_, lean_object* v_00_u03b2_1325_, lean_object* v_cmp_1326_, lean_object* v_inst_1327_, lean_object* v_t_1328_, lean_object* v_k_1329_, lean_object* v_h_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1326_, v_k_1329_, v_t_1328_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT___redArg(lean_object* v_cmp_1332_, lean_object* v_t_1333_, lean_object* v_k_1334_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1332_, v_k_1334_, v_t_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT(lean_object* v_00_u03b1_1336_, lean_object* v_00_u03b2_1337_, lean_object* v_cmp_1338_, lean_object* v_inst_1339_, lean_object* v_t_1340_, lean_object* v_k_1341_, lean_object* v_h_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1338_, v_k_1341_, v_t_1340_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE___redArg(lean_object* v_cmp_1344_, lean_object* v_t_1345_, lean_object* v_k_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1344_, v_k_1346_, v_t_1345_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE(lean_object* v_00_u03b1_1348_, lean_object* v_00_u03b2_1349_, lean_object* v_cmp_1350_, lean_object* v_inst_1351_, lean_object* v_t_1352_, lean_object* v_k_1353_, lean_object* v_h_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1350_, v_k_1353_, v_t_1352_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT___redArg(lean_object* v_cmp_1356_, lean_object* v_t_1357_, lean_object* v_k_1358_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1356_, v_k_1358_, v_t_1357_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT(lean_object* v_00_u03b1_1360_, lean_object* v_00_u03b2_1361_, lean_object* v_cmp_1362_, lean_object* v_inst_1363_, lean_object* v_t_1364_, lean_object* v_k_1365_, lean_object* v_h_1366_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1362_, v_k_1365_, v_t_1364_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1368_, lean_object* v_inst_1369_, lean_object* v_t_1370_, lean_object* v_k_1371_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_box(0);
v___x_1373_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1368_, v_k_1371_, v___x_1372_, v_t_1370_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1375_ = l_panic___redArg(v_inst_1369_, v___x_1374_);
return v___x_1375_;
}
else
{
lean_object* v_val_1376_; 
lean_dec(v_inst_1369_);
v_val_1376_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_val_1376_);
lean_dec_ref(v___x_1373_);
return v_val_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_cmp_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_t_1382_, lean_object* v_k_1383_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_box(0);
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1379_, v_k_1383_, v___x_1384_, v_t_1382_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1387_ = l_panic___redArg(v_inst_1381_, v___x_1386_);
return v___x_1387_;
}
else
{
lean_object* v_val_1388_; 
lean_dec(v_inst_1381_);
v_val_1388_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_val_1388_);
lean_dec_ref(v___x_1385_);
return v_val_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1389_, lean_object* v_inst_1390_, lean_object* v_t_1391_, lean_object* v_k_1392_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_box(0);
v___x_1394_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1389_, v_k_1392_, v___x_1393_, v_t_1391_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1396_ = l_panic___redArg(v_inst_1390_, v___x_1395_);
return v___x_1396_;
}
else
{
lean_object* v_val_1397_; 
lean_dec(v_inst_1390_);
v_val_1397_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_val_1397_);
lean_dec_ref(v___x_1394_);
return v_val_1397_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1398_, lean_object* v_00_u03b2_1399_, lean_object* v_cmp_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_t_1403_, lean_object* v_k_1404_){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_box(0);
v___x_1406_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1400_, v_k_1404_, v___x_1405_, v_t_1403_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1408_ = l_panic___redArg(v_inst_1402_, v___x_1407_);
return v___x_1408_;
}
else
{
lean_object* v_val_1409_; 
lean_dec(v_inst_1402_);
v_val_1409_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_val_1409_);
lean_dec_ref(v___x_1406_);
return v_val_1409_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1410_, lean_object* v_inst_1411_, lean_object* v_t_1412_, lean_object* v_k_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1410_, v_k_1413_, v___x_1414_, v_t_1412_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1417_ = l_panic___redArg(v_inst_1411_, v___x_1416_);
return v___x_1417_;
}
else
{
lean_object* v_val_1418_; 
lean_dec(v_inst_1411_);
v_val_1418_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1418_);
lean_dec_ref(v___x_1415_);
return v_val_1418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1419_, lean_object* v_00_u03b2_1420_, lean_object* v_cmp_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_t_1424_, lean_object* v_k_1425_){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_box(0);
v___x_1427_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1421_, v_k_1425_, v___x_1426_, v_t_1424_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1429_ = l_panic___redArg(v_inst_1423_, v___x_1428_);
return v___x_1429_;
}
else
{
lean_object* v_val_1430_; 
lean_dec(v_inst_1423_);
v_val_1430_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_val_1430_);
lean_dec_ref(v___x_1427_);
return v_val_1430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1431_, lean_object* v_inst_1432_, lean_object* v_t_1433_, lean_object* v_k_1434_){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_box(0);
v___x_1436_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1431_, v_k_1434_, v___x_1435_, v_t_1433_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1438_ = l_panic___redArg(v_inst_1432_, v___x_1437_);
return v___x_1438_;
}
else
{
lean_object* v_val_1439_; 
lean_dec(v_inst_1432_);
v_val_1439_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_val_1439_);
lean_dec_ref(v___x_1436_);
return v_val_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_cmp_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_t_1445_, lean_object* v_k_1446_){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_box(0);
v___x_1448_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1442_, v_k_1446_, v___x_1447_, v_t_1445_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1450_ = l_panic___redArg(v_inst_1444_, v___x_1449_);
return v___x_1450_;
}
else
{
lean_object* v_val_1451_; 
lean_dec(v_inst_1444_);
v_val_1451_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_val_1451_);
lean_dec_ref(v___x_1448_);
return v_val_1451_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg(lean_object* v_cmp_1452_, lean_object* v_t_1453_, lean_object* v_k_1454_, lean_object* v_fallback_1455_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_box(0);
v___x_1457_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1452_, v_k_1454_, v___x_1456_, v_t_1453_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_inc(v_fallback_1455_);
return v_fallback_1455_;
}
else
{
lean_object* v_val_1458_; 
v_val_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_val_1458_);
lean_dec_ref(v___x_1457_);
return v_val_1458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1459_, lean_object* v_t_1460_, lean_object* v_k_1461_, lean_object* v_fallback_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Std_ExtTreeMap_getKeyGED___redArg(v_cmp_1459_, v_t_1460_, v_k_1461_, v_fallback_1462_);
lean_dec(v_fallback_1462_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED(lean_object* v_00_u03b1_1464_, lean_object* v_00_u03b2_1465_, lean_object* v_cmp_1466_, lean_object* v_inst_1467_, lean_object* v_t_1468_, lean_object* v_k_1469_, lean_object* v_fallback_1470_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1466_, v_k_1469_, v___x_1471_, v_t_1468_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_inc(v_fallback_1470_);
return v_fallback_1470_;
}
else
{
lean_object* v_val_1473_; 
v_val_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_val_1473_);
lean_dec_ref(v___x_1472_);
return v_val_1473_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1474_, lean_object* v_00_u03b2_1475_, lean_object* v_cmp_1476_, lean_object* v_inst_1477_, lean_object* v_t_1478_, lean_object* v_k_1479_, lean_object* v_fallback_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Std_ExtTreeMap_getKeyGED(v_00_u03b1_1474_, v_00_u03b2_1475_, v_cmp_1476_, v_inst_1477_, v_t_1478_, v_k_1479_, v_fallback_1480_);
lean_dec(v_fallback_1480_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1482_, lean_object* v_t_1483_, lean_object* v_k_1484_, lean_object* v_fallback_1485_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_box(0);
v___x_1487_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1482_, v_k_1484_, v___x_1486_, v_t_1483_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_inc(v_fallback_1485_);
return v_fallback_1485_;
}
else
{
lean_object* v_val_1488_; 
v_val_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_val_1488_);
lean_dec_ref(v___x_1487_);
return v_val_1488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1489_, lean_object* v_t_1490_, lean_object* v_k_1491_, lean_object* v_fallback_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Std_ExtTreeMap_getKeyGTD___redArg(v_cmp_1489_, v_t_1490_, v_k_1491_, v_fallback_1492_);
lean_dec(v_fallback_1492_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD(lean_object* v_00_u03b1_1494_, lean_object* v_00_u03b2_1495_, lean_object* v_cmp_1496_, lean_object* v_inst_1497_, lean_object* v_t_1498_, lean_object* v_k_1499_, lean_object* v_fallback_1500_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_box(0);
v___x_1502_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1496_, v_k_1499_, v___x_1501_, v_t_1498_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_inc(v_fallback_1500_);
return v_fallback_1500_;
}
else
{
lean_object* v_val_1503_; 
v_val_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_val_1503_);
lean_dec_ref(v___x_1502_);
return v_val_1503_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1504_, lean_object* v_00_u03b2_1505_, lean_object* v_cmp_1506_, lean_object* v_inst_1507_, lean_object* v_t_1508_, lean_object* v_k_1509_, lean_object* v_fallback_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Std_ExtTreeMap_getKeyGTD(v_00_u03b1_1504_, v_00_u03b2_1505_, v_cmp_1506_, v_inst_1507_, v_t_1508_, v_k_1509_, v_fallback_1510_);
lean_dec(v_fallback_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg(lean_object* v_cmp_1512_, lean_object* v_t_1513_, lean_object* v_k_1514_, lean_object* v_fallback_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_box(0);
v___x_1517_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1512_, v_k_1514_, v___x_1516_, v_t_1513_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_inc(v_fallback_1515_);
return v_fallback_1515_;
}
else
{
lean_object* v_val_1518_; 
v_val_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_val_1518_);
lean_dec_ref(v___x_1517_);
return v_val_1518_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1519_, lean_object* v_t_1520_, lean_object* v_k_1521_, lean_object* v_fallback_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Std_ExtTreeMap_getKeyLED___redArg(v_cmp_1519_, v_t_1520_, v_k_1521_, v_fallback_1522_);
lean_dec(v_fallback_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED(lean_object* v_00_u03b1_1524_, lean_object* v_00_u03b2_1525_, lean_object* v_cmp_1526_, lean_object* v_inst_1527_, lean_object* v_t_1528_, lean_object* v_k_1529_, lean_object* v_fallback_1530_){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = lean_box(0);
v___x_1532_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1526_, v_k_1529_, v___x_1531_, v_t_1528_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_inc(v_fallback_1530_);
return v_fallback_1530_;
}
else
{
lean_object* v_val_1533_; 
v_val_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1533_);
lean_dec_ref(v___x_1532_);
return v_val_1533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1534_, lean_object* v_00_u03b2_1535_, lean_object* v_cmp_1536_, lean_object* v_inst_1537_, lean_object* v_t_1538_, lean_object* v_k_1539_, lean_object* v_fallback_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Std_ExtTreeMap_getKeyLED(v_00_u03b1_1534_, v_00_u03b2_1535_, v_cmp_1536_, v_inst_1537_, v_t_1538_, v_k_1539_, v_fallback_1540_);
lean_dec(v_fallback_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1542_, lean_object* v_t_1543_, lean_object* v_k_1544_, lean_object* v_fallback_1545_){
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
lean_dec_ref(v___x_1547_);
return v_val_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1549_, lean_object* v_t_1550_, lean_object* v_k_1551_, lean_object* v_fallback_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Std_ExtTreeMap_getKeyLTD___redArg(v_cmp_1549_, v_t_1550_, v_k_1551_, v_fallback_1552_);
lean_dec(v_fallback_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD(lean_object* v_00_u03b1_1554_, lean_object* v_00_u03b2_1555_, lean_object* v_cmp_1556_, lean_object* v_inst_1557_, lean_object* v_t_1558_, lean_object* v_k_1559_, lean_object* v_fallback_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_box(0);
v___x_1562_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1556_, v_k_1559_, v___x_1561_, v_t_1558_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_inc(v_fallback_1560_);
return v_fallback_1560_;
}
else
{
lean_object* v_val_1563_; 
v_val_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_val_1563_);
lean_dec_ref(v___x_1562_);
return v_val_1563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1564_, lean_object* v_00_u03b2_1565_, lean_object* v_cmp_1566_, lean_object* v_inst_1567_, lean_object* v_t_1568_, lean_object* v_k_1569_, lean_object* v_fallback_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_ExtTreeMap_getKeyLTD(v_00_u03b1_1564_, v_00_u03b2_1565_, v_cmp_1566_, v_inst_1567_, v_t_1568_, v_k_1569_, v_fallback_1570_);
lean_dec(v_fallback_1570_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___redArg(lean_object* v_f_1572_, lean_object* v_m_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_1572_, v_m_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter(lean_object* v_00_u03b1_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_cmp_1577_, lean_object* v_f_1578_, lean_object* v_m_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_1578_, v_m_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___boxed(lean_object* v_00_u03b1_1581_, lean_object* v_00_u03b2_1582_, lean_object* v_cmp_1583_, lean_object* v_f_1584_, lean_object* v_m_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Std_ExtTreeMap_filter(v_00_u03b1_1581_, v_00_u03b2_1582_, v_cmp_1583_, v_f_1584_, v_m_1585_);
lean_dec_ref(v_cmp_1583_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___redArg(lean_object* v_f_1587_, lean_object* v_m_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_1587_, v_m_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap(lean_object* v_00_u03b1_1590_, lean_object* v_00_u03b2_1591_, lean_object* v_00_u03b3_1592_, lean_object* v_cmp_1593_, lean_object* v_f_1594_, lean_object* v_m_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_1594_, v_m_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___boxed(lean_object* v_00_u03b1_1597_, lean_object* v_00_u03b2_1598_, lean_object* v_00_u03b3_1599_, lean_object* v_cmp_1600_, lean_object* v_f_1601_, lean_object* v_m_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Std_ExtTreeMap_filterMap(v_00_u03b1_1597_, v_00_u03b2_1598_, v_00_u03b3_1599_, v_cmp_1600_, v_f_1601_, v_m_1602_);
lean_dec_ref(v_cmp_1600_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___redArg(lean_object* v_f_1604_, lean_object* v_t_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_1604_, v_t_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map(lean_object* v_00_u03b1_1607_, lean_object* v_00_u03b2_1608_, lean_object* v_00_u03b3_1609_, lean_object* v_cmp_1610_, lean_object* v_f_1611_, lean_object* v_t_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_1611_, v_t_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___boxed(lean_object* v_00_u03b1_1614_, lean_object* v_00_u03b2_1615_, lean_object* v_00_u03b3_1616_, lean_object* v_cmp_1617_, lean_object* v_f_1618_, lean_object* v_t_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Std_ExtTreeMap_map(v_00_u03b1_1614_, v_00_u03b2_1615_, v_00_u03b3_1616_, v_cmp_1617_, v_f_1618_, v_t_1619_);
lean_dec_ref(v_cmp_1617_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___redArg(lean_object* v_inst_1621_, lean_object* v_f_1622_, lean_object* v_init_1623_, lean_object* v_t_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1621_, v_f_1622_, v_init_1623_, v_t_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM(lean_object* v_00_u03b1_1626_, lean_object* v_00_u03b2_1627_, lean_object* v_cmp_1628_, lean_object* v_00_u03b4_1629_, lean_object* v_m_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_f_1634_, lean_object* v_init_1635_, lean_object* v_t_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1631_, v_f_1634_, v_init_1635_, v_t_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___boxed(lean_object* v_00_u03b1_1638_, lean_object* v_00_u03b2_1639_, lean_object* v_cmp_1640_, lean_object* v_00_u03b4_1641_, lean_object* v_m_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_f_1646_, lean_object* v_init_1647_, lean_object* v_t_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Std_ExtTreeMap_foldlM(v_00_u03b1_1638_, v_00_u03b2_1639_, v_cmp_1640_, v_00_u03b4_1641_, v_m_1642_, v_inst_1643_, v_inst_1644_, v_inst_1645_, v_f_1646_, v_init_1647_, v_t_1648_);
lean_dec_ref(v_cmp_1640_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___redArg(lean_object* v_f_1650_, lean_object* v_init_1651_, lean_object* v_t_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1650_, v_init_1651_, v_t_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl(lean_object* v_00_u03b1_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_cmp_1656_, lean_object* v_00_u03b4_1657_, lean_object* v_inst_1658_, lean_object* v_f_1659_, lean_object* v_init_1660_, lean_object* v_t_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1659_, v_init_1660_, v_t_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___boxed(lean_object* v_00_u03b1_1663_, lean_object* v_00_u03b2_1664_, lean_object* v_cmp_1665_, lean_object* v_00_u03b4_1666_, lean_object* v_inst_1667_, lean_object* v_f_1668_, lean_object* v_init_1669_, lean_object* v_t_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Std_ExtTreeMap_foldl(v_00_u03b1_1663_, v_00_u03b2_1664_, v_cmp_1665_, v_00_u03b4_1666_, v_inst_1667_, v_f_1668_, v_init_1669_, v_t_1670_);
lean_dec_ref(v_cmp_1665_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___redArg(lean_object* v_inst_1672_, lean_object* v_f_1673_, lean_object* v_init_1674_, lean_object* v_t_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1672_, v_f_1673_, v_init_1674_, v_t_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM(lean_object* v_00_u03b1_1677_, lean_object* v_00_u03b2_1678_, lean_object* v_cmp_1679_, lean_object* v_00_u03b4_1680_, lean_object* v_m_1681_, lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_f_1685_, lean_object* v_init_1686_, lean_object* v_t_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1682_, v_f_1685_, v_init_1686_, v_t_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___boxed(lean_object* v_00_u03b1_1689_, lean_object* v_00_u03b2_1690_, lean_object* v_cmp_1691_, lean_object* v_00_u03b4_1692_, lean_object* v_m_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_f_1697_, lean_object* v_init_1698_, lean_object* v_t_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_ExtTreeMap_foldrM(v_00_u03b1_1689_, v_00_u03b2_1690_, v_cmp_1691_, v_00_u03b4_1692_, v_m_1693_, v_inst_1694_, v_inst_1695_, v_inst_1696_, v_f_1697_, v_init_1698_, v_t_1699_);
lean_dec_ref(v_cmp_1691_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg___lam__0(lean_object* v_f_1701_, lean_object* v_x1_1702_, lean_object* v_x2_1703_, lean_object* v_x3_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_apply_3(v_f_1701_, v_x1_1702_, v_x2_1703_, v_x3_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg(lean_object* v_f_1725_, lean_object* v_init_1726_, lean_object* v_t_1727_){
_start:
{
lean_object* v___f_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___f_1728_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1728_, 0, v_f_1725_);
v___x_1729_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_1730_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1729_, v___f_1728_, v_init_1726_, v_t_1727_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr(lean_object* v_00_u03b1_1731_, lean_object* v_00_u03b2_1732_, lean_object* v_cmp_1733_, lean_object* v_00_u03b4_1734_, lean_object* v_inst_1735_, lean_object* v_f_1736_, lean_object* v_init_1737_, lean_object* v_t_1738_){
_start:
{
lean_object* v___f_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___f_1739_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1739_, 0, v_f_1736_);
v___x_1740_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_1741_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1740_, v___f_1739_, v_init_1737_, v_t_1738_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___boxed(lean_object* v_00_u03b1_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_cmp_1744_, lean_object* v_00_u03b4_1745_, lean_object* v_inst_1746_, lean_object* v_f_1747_, lean_object* v_init_1748_, lean_object* v_t_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Std_ExtTreeMap_foldr(v_00_u03b1_1742_, v_00_u03b2_1743_, v_cmp_1744_, v_00_u03b4_1745_, v_inst_1746_, v_f_1747_, v_init_1748_, v_t_1749_);
lean_dec_ref(v_cmp_1744_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg___lam__0(lean_object* v_f_1751_, lean_object* v_cmp_1752_, lean_object* v_x_1753_, lean_object* v_a_1754_, lean_object* v_b_1755_){
_start:
{
lean_object* v_fst_1756_; lean_object* v_snd_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1771_; 
v_fst_1756_ = lean_ctor_get(v_x_1753_, 0);
v_snd_1757_ = lean_ctor_get(v_x_1753_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_x_1753_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1759_ = v_x_1753_;
v_isShared_1760_ = v_isSharedCheck_1771_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_snd_1757_);
lean_inc(v_fst_1756_);
lean_dec(v_x_1753_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1771_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
lean_inc(v_b_1755_);
lean_inc(v_a_1754_);
v___x_1761_ = lean_apply_2(v_f_1751_, v_a_1754_, v_b_1755_);
v___x_1762_ = lean_unbox(v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1763_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1752_, v_a_1754_, v_b_1755_, v_snd_1757_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 1, v___x_1763_);
v___x_1765_ = v___x_1759_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_fst_1756_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1752_, v_a_1754_, v_b_1755_, v_fst_1756_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1767_);
v___x_1769_ = v___x_1759_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_snd_1757_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg(lean_object* v_cmp_1774_, lean_object* v_f_1775_, lean_object* v_t_1776_){
_start:
{
lean_object* v___f_1777_; lean_object* v___x_1778_; lean_object* v_p_1779_; lean_object* v_fst_1780_; lean_object* v_snd_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v___f_1777_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1777_, 0, v_f_1775_);
lean_closure_set(v___f_1777_, 1, v_cmp_1774_);
v___x_1778_ = ((lean_object*)(l_Std_ExtTreeMap_partition___redArg___closed__0));
v_p_1779_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1777_, v___x_1778_, v_t_1776_);
v_fst_1780_ = lean_ctor_get(v_p_1779_, 0);
v_snd_1781_ = lean_ctor_get(v_p_1779_, 1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_p_1779_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v_p_1779_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_snd_1781_);
lean_inc(v_fst_1780_);
lean_dec(v_p_1779_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_fst_1780_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_snd_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition(lean_object* v_00_u03b1_1789_, lean_object* v_00_u03b2_1790_, lean_object* v_cmp_1791_, lean_object* v_inst_1792_, lean_object* v_f_1793_, lean_object* v_t_1794_){
_start:
{
lean_object* v___f_1795_; lean_object* v___x_1796_; lean_object* v_p_1797_; lean_object* v_fst_1798_; lean_object* v_snd_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
v___f_1795_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1795_, 0, v_f_1793_);
lean_closure_set(v___f_1795_, 1, v_cmp_1791_);
v___x_1796_ = ((lean_object*)(l_Std_ExtTreeMap_partition___redArg___closed__0));
v_p_1797_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1795_, v___x_1796_, v_t_1794_);
v_fst_1798_ = lean_ctor_get(v_p_1797_, 0);
v_snd_1799_ = lean_ctor_get(v_p_1797_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_p_1797_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v_p_1797_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_snd_1799_);
lean_inc(v_fst_1798_);
lean_dec(v_p_1797_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_fst_1798_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_snd_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg___lam__0(lean_object* v_f_1807_, lean_object* v_x_1808_, lean_object* v_k_1809_, lean_object* v_v_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_apply_2(v_f_1807_, v_k_1809_, v_v_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg(lean_object* v_inst_1812_, lean_object* v_f_1813_, lean_object* v_t_1814_){
_start:
{
lean_object* v___f_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___f_1815_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1815_, 0, v_f_1813_);
v___x_1816_ = lean_box(0);
v___x_1817_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1812_, v___f_1815_, v___x_1816_, v_t_1814_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM(lean_object* v_00_u03b1_1818_, lean_object* v_00_u03b2_1819_, lean_object* v_cmp_1820_, lean_object* v_m_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_f_1825_, lean_object* v_t_1826_){
_start:
{
lean_object* v___f_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___f_1827_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1827_, 0, v_f_1825_);
v___x_1828_ = lean_box(0);
v___x_1829_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1822_, v___f_1827_, v___x_1828_, v_t_1826_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___boxed(lean_object* v_00_u03b1_1830_, lean_object* v_00_u03b2_1831_, lean_object* v_cmp_1832_, lean_object* v_m_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_f_1837_, lean_object* v_t_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Std_ExtTreeMap_forM(v_00_u03b1_1830_, v_00_u03b2_1831_, v_cmp_1832_, v_m_1833_, v_inst_1834_, v_inst_1835_, v_inst_1836_, v_f_1837_, v_t_1838_);
lean_dec_ref(v_cmp_1832_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__0(lean_object* v_f_1840_, lean_object* v_a_1841_, lean_object* v_b_1842_, lean_object* v_c_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_apply_3(v_f_1840_, v_a_1841_, v_b_1842_, v_c_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__1(lean_object* v_toPure_1845_, lean_object* v_____do__lift_1846_){
_start:
{
lean_object* v_a_1847_; lean_object* v___x_1848_; 
v_a_1847_ = lean_ctor_get(v_____do__lift_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v_____do__lift_1846_);
v___x_1848_ = lean_apply_2(v_toPure_1845_, lean_box(0), v_a_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg(lean_object* v_inst_1849_, lean_object* v_f_1850_, lean_object* v_init_1851_, lean_object* v_t_1852_){
_start:
{
lean_object* v_toApplicative_1853_; lean_object* v_toBind_1854_; lean_object* v_toPure_1855_; lean_object* v___f_1856_; lean_object* v___x_1857_; lean_object* v___f_1858_; lean_object* v___x_1859_; 
v_toApplicative_1853_ = lean_ctor_get(v_inst_1849_, 0);
v_toBind_1854_ = lean_ctor_get(v_inst_1849_, 1);
lean_inc(v_toBind_1854_);
v_toPure_1855_ = lean_ctor_get(v_toApplicative_1853_, 1);
lean_inc(v_toPure_1855_);
v___f_1856_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1856_, 0, v_f_1850_);
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1849_, v___f_1856_, v_init_1851_, v_t_1852_);
v___f_1858_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1858_, 0, v_toPure_1855_);
v___x_1859_ = lean_apply_4(v_toBind_1854_, lean_box(0), lean_box(0), v___x_1857_, v___f_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn(lean_object* v_00_u03b1_1860_, lean_object* v_00_u03b2_1861_, lean_object* v_cmp_1862_, lean_object* v_00_u03b4_1863_, lean_object* v_m_1864_, lean_object* v_inst_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_f_1868_, lean_object* v_init_1869_, lean_object* v_t_1870_){
_start:
{
lean_object* v_toApplicative_1871_; lean_object* v_toBind_1872_; lean_object* v_toPure_1873_; lean_object* v___f_1874_; lean_object* v___x_1875_; lean_object* v___f_1876_; lean_object* v___x_1877_; 
v_toApplicative_1871_ = lean_ctor_get(v_inst_1865_, 0);
v_toBind_1872_ = lean_ctor_get(v_inst_1865_, 1);
lean_inc(v_toBind_1872_);
v_toPure_1873_ = lean_ctor_get(v_toApplicative_1871_, 1);
lean_inc(v_toPure_1873_);
v___f_1874_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1874_, 0, v_f_1868_);
v___x_1875_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1865_, v___f_1874_, v_init_1869_, v_t_1870_);
v___f_1876_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1876_, 0, v_toPure_1873_);
v___x_1877_ = lean_apply_4(v_toBind_1872_, lean_box(0), lean_box(0), v___x_1875_, v___f_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___boxed(lean_object* v_00_u03b1_1878_, lean_object* v_00_u03b2_1879_, lean_object* v_cmp_1880_, lean_object* v_00_u03b4_1881_, lean_object* v_m_1882_, lean_object* v_inst_1883_, lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v_f_1886_, lean_object* v_init_1887_, lean_object* v_t_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Std_ExtTreeMap_forIn(v_00_u03b1_1878_, v_00_u03b2_1879_, v_cmp_1880_, v_00_u03b4_1881_, v_m_1882_, v_inst_1883_, v_inst_1884_, v_inst_1885_, v_f_1886_, v_init_1887_, v_t_1888_);
lean_dec_ref(v_cmp_1880_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_1890_, lean_object* v_x_1891_, lean_object* v_k_1892_, lean_object* v_v_1893_){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_k_1892_);
lean_ctor_set(v___x_1894_, 1, v_v_1893_);
v___x_1895_ = lean_apply_1(v_f_1890_, v___x_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_1896_, lean_object* v_t_1897_, lean_object* v_f_1898_){
_start:
{
lean_object* v___f_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___f_1899_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1899_, 0, v_f_1898_);
v___x_1900_ = lean_box(0);
v___x_1901_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1896_, v___f_1899_, v___x_1900_, v_t_1897_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1902_){
_start:
{
lean_object* v___f_1903_; 
v___f_1903_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1903_, 0, v_inst_1902_);
return v___f_1903_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1904_, lean_object* v_00_u03b2_1905_, lean_object* v_cmp_1906_, lean_object* v_m_1907_, lean_object* v_inst_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_){
_start:
{
lean_object* v___f_1911_; 
v___f_1911_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1911_, 0, v_inst_1909_);
return v___f_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1912_, lean_object* v_00_u03b2_1913_, lean_object* v_cmp_1914_, lean_object* v_m_1915_, lean_object* v_inst_1916_, lean_object* v_inst_1917_, lean_object* v_inst_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(v_00_u03b1_1912_, v_00_u03b2_1913_, v_cmp_1914_, v_m_1915_, v_inst_1916_, v_inst_1917_, v_inst_1918_);
lean_dec_ref(v_cmp_1914_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_1920_, lean_object* v_a_1921_, lean_object* v_b_1922_, lean_object* v_c_1923_){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_a_1921_);
lean_ctor_set(v___x_1924_, 1, v_b_1922_);
v___x_1925_ = lean_apply_2(v_f_1920_, v___x_1924_, v_c_1923_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_1926_, lean_object* v_00_u03b2_1927_, lean_object* v_m_1928_, lean_object* v_init_1929_, lean_object* v_f_1930_){
_start:
{
lean_object* v_toApplicative_1931_; lean_object* v_toBind_1932_; lean_object* v_toPure_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; lean_object* v___f_1936_; lean_object* v___x_1937_; 
v_toApplicative_1931_ = lean_ctor_get(v_inst_1926_, 0);
v_toBind_1932_ = lean_ctor_get(v_inst_1926_, 1);
lean_inc(v_toBind_1932_);
v_toPure_1933_ = lean_ctor_get(v_toApplicative_1931_, 1);
lean_inc(v_toPure_1933_);
v___f_1934_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1934_, 0, v_f_1930_);
v___x_1935_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1926_, v___f_1934_, v_init_1929_, v_m_1928_);
v___f_1936_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1936_, 0, v_toPure_1933_);
v___x_1937_ = lean_apply_4(v_toBind_1932_, lean_box(0), lean_box(0), v___x_1935_, v___f_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_1938_){
_start:
{
lean_object* v___f_1939_; 
v___f_1939_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1939_, 0, v_inst_1938_);
return v___f_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_1940_, lean_object* v_00_u03b2_1941_, lean_object* v_cmp_1942_, lean_object* v_m_1943_, lean_object* v_inst_1944_, lean_object* v_inst_1945_, lean_object* v_inst_1946_){
_start:
{
lean_object* v___f_1947_; 
v___f_1947_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1947_, 0, v_inst_1945_);
return v___f_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_1948_, lean_object* v_00_u03b2_1949_, lean_object* v_cmp_1950_, lean_object* v_m_1951_, lean_object* v_inst_1952_, lean_object* v_inst_1953_, lean_object* v_inst_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(v_00_u03b1_1948_, v_00_u03b2_1949_, v_cmp_1950_, v_m_1951_, v_inst_1952_, v_inst_1953_, v_inst_1954_);
lean_dec_ref(v_cmp_1950_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0(lean_object* v_p_1956_, lean_object* v___x_1957_, lean_object* v___x_1958_, lean_object* v_a_1959_, lean_object* v_b_1960_, lean_object* v_acc_1961_){
_start:
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = lean_apply_2(v_p_1956_, v_a_1959_, v_b_1960_);
v___x_1963_ = lean_unbox(v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1957_);
return v___x_1964_;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec_ref(v___x_1957_);
v___x_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1962_);
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
lean_ctor_set(v___x_1966_, 1, v___x_1958_);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_1968_, lean_object* v___x_1969_, lean_object* v___x_1970_, lean_object* v_a_1971_, lean_object* v_b_1972_, lean_object* v_acc_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Std_ExtTreeMap_any___redArg___lam__0(v_p_1968_, v___x_1969_, v___x_1970_, v_a_1971_, v_b_1972_, v_acc_1973_);
lean_dec_ref(v_acc_1973_);
return v_res_1974_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_any___redArg(lean_object* v_t_1978_, lean_object* v_p_1979_){
_start:
{
lean_object* v___y_1981_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___f_1989_; lean_object* v___x_1990_; lean_object* v_a_1991_; 
v___x_1986_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_1987_ = lean_box(0);
v___x_1988_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_1989_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1989_, 0, v_p_1979_);
lean_closure_set(v___f_1989_, 1, v___x_1988_);
lean_closure_set(v___f_1989_, 2, v___x_1987_);
v___x_1990_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1986_, v___f_1989_, v___x_1988_, v_t_1978_);
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___y_1981_ = v_a_1991_;
goto v___jp_1980_;
v___jp_1980_:
{
lean_object* v_fst_1982_; 
v_fst_1982_ = lean_ctor_get(v___y_1981_, 0);
lean_inc(v_fst_1982_);
lean_dec_ref(v___y_1981_);
if (lean_obj_tag(v_fst_1982_) == 0)
{
uint8_t v___x_1983_; 
v___x_1983_ = 0;
return v___x_1983_;
}
else
{
lean_object* v_val_1984_; uint8_t v___x_1985_; 
v_val_1984_ = lean_ctor_get(v_fst_1982_, 0);
lean_inc(v_val_1984_);
lean_dec_ref(v_fst_1982_);
v___x_1985_ = lean_unbox(v_val_1984_);
lean_dec(v_val_1984_);
return v___x_1985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___boxed(lean_object* v_t_1992_, lean_object* v_p_1993_){
_start:
{
uint8_t v_res_1994_; lean_object* v_r_1995_; 
v_res_1994_ = l_Std_ExtTreeMap_any___redArg(v_t_1992_, v_p_1993_);
v_r_1995_ = lean_box(v_res_1994_);
return v_r_1995_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_any(lean_object* v_00_u03b1_1996_, lean_object* v_00_u03b2_1997_, lean_object* v_cmp_1998_, lean_object* v_inst_1999_, lean_object* v_t_2000_, lean_object* v_p_2001_){
_start:
{
lean_object* v___y_2003_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___f_2011_; lean_object* v___x_2012_; lean_object* v_a_2013_; 
v___x_2008_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2009_ = lean_box(0);
v___x_2010_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2011_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2011_, 0, v_p_2001_);
lean_closure_set(v___f_2011_, 1, v___x_2010_);
lean_closure_set(v___f_2011_, 2, v___x_2009_);
v___x_2012_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2008_, v___f_2011_, v___x_2010_, v_t_2000_);
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___y_2003_ = v_a_2013_;
goto v___jp_2002_;
v___jp_2002_:
{
lean_object* v_fst_2004_; 
v_fst_2004_ = lean_ctor_get(v___y_2003_, 0);
lean_inc(v_fst_2004_);
lean_dec_ref(v___y_2003_);
if (lean_obj_tag(v_fst_2004_) == 0)
{
uint8_t v___x_2005_; 
v___x_2005_ = 0;
return v___x_2005_;
}
else
{
lean_object* v_val_2006_; uint8_t v___x_2007_; 
v_val_2006_ = lean_ctor_get(v_fst_2004_, 0);
lean_inc(v_val_2006_);
lean_dec_ref(v_fst_2004_);
v___x_2007_ = lean_unbox(v_val_2006_);
lean_dec(v_val_2006_);
return v___x_2007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___boxed(lean_object* v_00_u03b1_2014_, lean_object* v_00_u03b2_2015_, lean_object* v_cmp_2016_, lean_object* v_inst_2017_, lean_object* v_t_2018_, lean_object* v_p_2019_){
_start:
{
uint8_t v_res_2020_; lean_object* v_r_2021_; 
v_res_2020_ = l_Std_ExtTreeMap_any(v_00_u03b1_2014_, v_00_u03b2_2015_, v_cmp_2016_, v_inst_2017_, v_t_2018_, v_p_2019_);
lean_dec_ref(v_cmp_2016_);
v_r_2021_ = lean_box(v_res_2020_);
return v_r_2021_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0(lean_object* v_p_2022_, lean_object* v___x_2023_, lean_object* v___x_2024_, lean_object* v_a_2025_, lean_object* v_b_2026_, lean_object* v_acc_2027_){
_start:
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = lean_apply_2(v_p_2022_, v_a_2025_, v_b_2026_);
v___x_2029_ = lean_unbox(v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec_ref(v___x_2024_);
v___x_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
v___x_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
lean_ctor_set(v___x_2031_, 1, v___x_2023_);
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2024_);
return v___x_2033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2034_, lean_object* v___x_2035_, lean_object* v___x_2036_, lean_object* v_a_2037_, lean_object* v_b_2038_, lean_object* v_acc_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Std_ExtTreeMap_all___redArg___lam__0(v_p_2034_, v___x_2035_, v___x_2036_, v_a_2037_, v_b_2038_, v_acc_2039_);
lean_dec_ref(v_acc_2039_);
return v_res_2040_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_all___redArg(lean_object* v_t_2041_, lean_object* v_p_2042_){
_start:
{
lean_object* v___y_2044_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___f_2052_; lean_object* v___x_2053_; lean_object* v_a_2054_; 
v___x_2049_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2050_ = lean_box(0);
v___x_2051_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2052_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2052_, 0, v_p_2042_);
lean_closure_set(v___f_2052_, 1, v___x_2050_);
lean_closure_set(v___f_2052_, 2, v___x_2051_);
v___x_2053_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2049_, v___f_2052_, v___x_2051_, v_t_2041_);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___y_2044_ = v_a_2054_;
goto v___jp_2043_;
v___jp_2043_:
{
lean_object* v_fst_2045_; 
v_fst_2045_ = lean_ctor_get(v___y_2044_, 0);
lean_inc(v_fst_2045_);
lean_dec_ref(v___y_2044_);
if (lean_obj_tag(v_fst_2045_) == 0)
{
uint8_t v___x_2046_; 
v___x_2046_ = 1;
return v___x_2046_;
}
else
{
lean_object* v_val_2047_; uint8_t v___x_2048_; 
v_val_2047_ = lean_ctor_get(v_fst_2045_, 0);
lean_inc(v_val_2047_);
lean_dec_ref(v_fst_2045_);
v___x_2048_ = lean_unbox(v_val_2047_);
lean_dec(v_val_2047_);
return v___x_2048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___boxed(lean_object* v_t_2055_, lean_object* v_p_2056_){
_start:
{
uint8_t v_res_2057_; lean_object* v_r_2058_; 
v_res_2057_ = l_Std_ExtTreeMap_all___redArg(v_t_2055_, v_p_2056_);
v_r_2058_ = lean_box(v_res_2057_);
return v_r_2058_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_all(lean_object* v_00_u03b1_2059_, lean_object* v_00_u03b2_2060_, lean_object* v_cmp_2061_, lean_object* v_inst_2062_, lean_object* v_t_2063_, lean_object* v_p_2064_){
_start:
{
lean_object* v___y_2066_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; lean_object* v_a_2076_; 
v___x_2071_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2072_ = lean_box(0);
v___x_2073_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2074_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2074_, 0, v_p_2064_);
lean_closure_set(v___f_2074_, 1, v___x_2072_);
lean_closure_set(v___f_2074_, 2, v___x_2073_);
v___x_2075_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2071_, v___f_2074_, v___x_2073_, v_t_2063_);
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___y_2066_ = v_a_2076_;
goto v___jp_2065_;
v___jp_2065_:
{
lean_object* v_fst_2067_; 
v_fst_2067_ = lean_ctor_get(v___y_2066_, 0);
lean_inc(v_fst_2067_);
lean_dec_ref(v___y_2066_);
if (lean_obj_tag(v_fst_2067_) == 0)
{
uint8_t v___x_2068_; 
v___x_2068_ = 1;
return v___x_2068_;
}
else
{
lean_object* v_val_2069_; uint8_t v___x_2070_; 
v_val_2069_ = lean_ctor_get(v_fst_2067_, 0);
lean_inc(v_val_2069_);
lean_dec_ref(v_fst_2067_);
v___x_2070_ = lean_unbox(v_val_2069_);
lean_dec(v_val_2069_);
return v___x_2070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___boxed(lean_object* v_00_u03b1_2077_, lean_object* v_00_u03b2_2078_, lean_object* v_cmp_2079_, lean_object* v_inst_2080_, lean_object* v_t_2081_, lean_object* v_p_2082_){
_start:
{
uint8_t v_res_2083_; lean_object* v_r_2084_; 
v_res_2083_ = l_Std_ExtTreeMap_all(v_00_u03b1_2077_, v_00_u03b2_2078_, v_cmp_2079_, v_inst_2080_, v_t_2081_, v_p_2082_);
lean_dec_ref(v_cmp_2079_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0(lean_object* v_x1_2085_, lean_object* v_x2_2086_, lean_object* v_x3_2087_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2088_, 0, v_x1_2085_);
lean_ctor_set(v___x_2088_, 1, v_x3_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_2089_, lean_object* v_x2_2090_, lean_object* v_x3_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Std_ExtTreeMap_keys___redArg___lam__0(v_x1_2089_, v_x2_2090_, v_x3_2091_);
lean_dec(v_x2_2090_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg(lean_object* v_t_2094_){
_start:
{
lean_object* v___f_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___f_2095_ = ((lean_object*)(l_Std_ExtTreeMap_keys___redArg___closed__0));
v___x_2096_ = lean_box(0);
v___x_2097_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2098_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2097_, v___f_2095_, v___x_2096_, v_t_2094_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys(lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_cmp_2101_, lean_object* v_inst_2102_, lean_object* v_t_2103_){
_start:
{
lean_object* v___f_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___f_2104_ = ((lean_object*)(l_Std_ExtTreeMap_keys___redArg___closed__0));
v___x_2105_ = lean_box(0);
v___x_2106_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2107_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2106_, v___f_2104_, v___x_2105_, v_t_2103_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___boxed(lean_object* v_00_u03b1_2108_, lean_object* v_00_u03b2_2109_, lean_object* v_cmp_2110_, lean_object* v_inst_2111_, lean_object* v_t_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Std_ExtTreeMap_keys(v_00_u03b1_2108_, v_00_u03b2_2109_, v_cmp_2110_, v_inst_2111_, v_t_2112_);
lean_dec_ref(v_cmp_2110_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0(lean_object* v_l_2114_, lean_object* v_k_2115_, lean_object* v_x_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_array_push(v_l_2114_, v_k_2115_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_2118_, lean_object* v_k_2119_, lean_object* v_x_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Std_ExtTreeMap_keysArray___redArg___lam__0(v_l_2118_, v_k_2119_, v_x_2120_);
lean_dec(v_x_2120_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg(lean_object* v_t_2123_){
_start:
{
lean_object* v___f_2124_; lean_object* v___y_2126_; 
v___f_2124_ = ((lean_object*)(l_Std_ExtTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2123_) == 0)
{
lean_object* v_size_2129_; 
v_size_2129_ = lean_ctor_get(v_t_2123_, 0);
lean_inc(v_size_2129_);
v___y_2126_ = v_size_2129_;
goto v___jp_2125_;
}
else
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_unsigned_to_nat(0u);
v___y_2126_ = v___x_2130_;
goto v___jp_2125_;
}
v___jp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_mk_empty_array_with_capacity(v___y_2126_);
lean_dec(v___y_2126_);
v___x_2128_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2124_, v___x_2127_, v_t_2123_);
return v___x_2128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray(lean_object* v_00_u03b1_2131_, lean_object* v_00_u03b2_2132_, lean_object* v_cmp_2133_, lean_object* v_inst_2134_, lean_object* v_t_2135_){
_start:
{
lean_object* v___f_2136_; lean_object* v___y_2138_; 
v___f_2136_ = ((lean_object*)(l_Std_ExtTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2135_) == 0)
{
lean_object* v_size_2141_; 
v_size_2141_ = lean_ctor_get(v_t_2135_, 0);
lean_inc(v_size_2141_);
v___y_2138_ = v_size_2141_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_unsigned_to_nat(0u);
v___y_2138_ = v___x_2142_;
goto v___jp_2137_;
}
v___jp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_mk_empty_array_with_capacity(v___y_2138_);
lean_dec(v___y_2138_);
v___x_2140_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2136_, v___x_2139_, v_t_2135_);
return v___x_2140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___boxed(lean_object* v_00_u03b1_2143_, lean_object* v_00_u03b2_2144_, lean_object* v_cmp_2145_, lean_object* v_inst_2146_, lean_object* v_t_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Std_ExtTreeMap_keysArray(v_00_u03b1_2143_, v_00_u03b2_2144_, v_cmp_2145_, v_inst_2146_, v_t_2147_);
lean_dec_ref(v_cmp_2145_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0(lean_object* v_x1_2149_, lean_object* v_x2_2150_, lean_object* v_x3_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2152_, 0, v_x2_2150_);
lean_ctor_set(v___x_2152_, 1, v_x3_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_2153_, lean_object* v_x2_2154_, lean_object* v_x3_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Std_ExtTreeMap_values___redArg___lam__0(v_x1_2153_, v_x2_2154_, v_x3_2155_);
lean_dec(v_x1_2153_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg(lean_object* v_t_2158_){
_start:
{
lean_object* v___f_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___f_2159_ = ((lean_object*)(l_Std_ExtTreeMap_values___redArg___closed__0));
v___x_2160_ = lean_box(0);
v___x_2161_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2162_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2161_, v___f_2159_, v___x_2160_, v_t_2158_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values(lean_object* v_00_u03b1_2163_, lean_object* v_00_u03b2_2164_, lean_object* v_cmp_2165_, lean_object* v_inst_2166_, lean_object* v_t_2167_){
_start:
{
lean_object* v___f_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___f_2168_ = ((lean_object*)(l_Std_ExtTreeMap_values___redArg___closed__0));
v___x_2169_ = lean_box(0);
v___x_2170_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2171_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2170_, v___f_2168_, v___x_2169_, v_t_2167_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___boxed(lean_object* v_00_u03b1_2172_, lean_object* v_00_u03b2_2173_, lean_object* v_cmp_2174_, lean_object* v_inst_2175_, lean_object* v_t_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Std_ExtTreeMap_values(v_00_u03b1_2172_, v_00_u03b2_2173_, v_cmp_2174_, v_inst_2175_, v_t_2176_);
lean_dec_ref(v_cmp_2174_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_2178_, lean_object* v_x_2179_, lean_object* v_v_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_array_push(v_l_2178_, v_v_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2182_, lean_object* v_x_2183_, lean_object* v_v_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Std_ExtTreeMap_valuesArray___redArg___lam__0(v_l_2182_, v_x_2183_, v_v_2184_);
lean_dec(v_x_2183_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg(lean_object* v_t_2187_){
_start:
{
lean_object* v___f_2188_; lean_object* v___y_2190_; 
v___f_2188_ = ((lean_object*)(l_Std_ExtTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2187_) == 0)
{
lean_object* v_size_2193_; 
v_size_2193_ = lean_ctor_get(v_t_2187_, 0);
lean_inc(v_size_2193_);
v___y_2190_ = v_size_2193_;
goto v___jp_2189_;
}
else
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_unsigned_to_nat(0u);
v___y_2190_ = v___x_2194_;
goto v___jp_2189_;
}
v___jp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = lean_mk_empty_array_with_capacity(v___y_2190_);
lean_dec(v___y_2190_);
v___x_2192_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2188_, v___x_2191_, v_t_2187_);
return v___x_2192_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray(lean_object* v_00_u03b1_2195_, lean_object* v_00_u03b2_2196_, lean_object* v_cmp_2197_, lean_object* v_inst_2198_, lean_object* v_t_2199_){
_start:
{
lean_object* v___f_2200_; lean_object* v___y_2202_; 
v___f_2200_ = ((lean_object*)(l_Std_ExtTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2199_) == 0)
{
lean_object* v_size_2205_; 
v_size_2205_ = lean_ctor_get(v_t_2199_, 0);
lean_inc(v_size_2205_);
v___y_2202_ = v_size_2205_;
goto v___jp_2201_;
}
else
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_unsigned_to_nat(0u);
v___y_2202_ = v___x_2206_;
goto v___jp_2201_;
}
v___jp_2201_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_mk_empty_array_with_capacity(v___y_2202_);
lean_dec(v___y_2202_);
v___x_2204_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2200_, v___x_2203_, v_t_2199_);
return v___x_2204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_2207_, lean_object* v_00_u03b2_2208_, lean_object* v_cmp_2209_, lean_object* v_inst_2210_, lean_object* v_t_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Std_ExtTreeMap_valuesArray(v_00_u03b1_2207_, v_00_u03b2_2208_, v_cmp_2209_, v_inst_2210_, v_t_2211_);
lean_dec_ref(v_cmp_2209_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg___lam__0(lean_object* v_x1_2213_, lean_object* v_x2_2214_, lean_object* v_x3_2215_){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v_x1_2213_);
lean_ctor_set(v___x_2216_, 1, v_x2_2214_);
v___x_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v_x3_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg(lean_object* v_t_2219_){
_start:
{
lean_object* v___f_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___f_2220_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___x_2221_ = lean_box(0);
v___x_2222_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2223_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2222_, v___f_2220_, v___x_2221_, v_t_2219_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList(lean_object* v_00_u03b1_2224_, lean_object* v_00_u03b2_2225_, lean_object* v_cmp_2226_, lean_object* v_inst_2227_, lean_object* v_t_2228_){
_start:
{
lean_object* v___f_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___f_2229_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___x_2230_ = lean_box(0);
v___x_2231_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2232_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2231_, v___f_2229_, v___x_2230_, v_t_2228_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___boxed(lean_object* v_00_u03b1_2233_, lean_object* v_00_u03b2_2234_, lean_object* v_cmp_2235_, lean_object* v_inst_2236_, lean_object* v_t_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Std_ExtTreeMap_toList(v_00_u03b1_2233_, v_00_u03b2_2234_, v_cmp_2235_, v_inst_2236_, v_t_2237_);
lean_dec_ref(v_cmp_2235_);
return v_res_2238_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_2240_, lean_object* v_a_2241_, lean_object* v_x_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_fst_2244_; lean_object* v_snd_2245_; lean_object* v_r_2246_; lean_object* v___x_2247_; 
v_fst_2244_ = lean_ctor_get(v_a_2241_, 0);
lean_inc(v_fst_2244_);
v_snd_2245_ = lean_ctor_get(v_a_2241_, 1);
lean_inc(v_snd_2245_);
lean_dec_ref(v_a_2241_);
v_r_2246_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2240_, v_fst_2244_, v_snd_2245_, v___y_2243_);
v___x_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_r_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg(lean_object* v_l_2248_, lean_object* v_cmp_2249_){
_start:
{
lean_object* v___f_2250_; lean_object* v___x_2251_; lean_object* v_r_2252_; lean_object* v___x_2253_; 
v___f_2250_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2250_, 0, v_cmp_2249_);
v___x_2251_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2252_ = lean_box(1);
v___x_2253_ = l_List_forIn_x27_loop___redArg(v___x_2251_, v___f_2250_, v_l_2248_, v_r_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList(lean_object* v_00_u03b1_2254_, lean_object* v_00_u03b2_2255_, lean_object* v_l_2256_, lean_object* v_cmp_2257_){
_start:
{
lean_object* v___f_2258_; lean_object* v___x_2259_; lean_object* v_r_2260_; lean_object* v___x_2261_; 
v___f_2258_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2258_, 0, v_cmp_2257_);
v___x_2259_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2260_ = lean_box(1);
v___x_2261_ = l_List_forIn_x27_loop___redArg(v___x_2259_, v___f_2258_, v_l_2256_, v_r_2260_);
return v___x_2261_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___lam__0(lean_object* v_cmp_2263_, lean_object* v_a_2264_, lean_object* v_x_2265_, lean_object* v___y_2266_){
_start:
{
uint8_t v___x_2267_; 
lean_inc(v___y_2266_);
lean_inc(v_a_2264_);
lean_inc_ref(v_cmp_2263_);
v___x_2267_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2263_, v_a_2264_, v___y_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = lean_box(0);
v___x_2269_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2263_, v_a_2264_, v___x_2268_, v___y_2266_);
v___x_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; 
lean_dec(v_a_2264_);
lean_dec_ref(v_cmp_2263_);
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___y_2266_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg(lean_object* v_l_2272_, lean_object* v_cmp_2273_){
_start:
{
lean_object* v___f_2274_; lean_object* v___x_2275_; lean_object* v_r_2276_; lean_object* v___x_2277_; 
v___f_2274_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2274_, 0, v_cmp_2273_);
v___x_2275_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2276_ = lean_box(1);
v___x_2277_ = l_List_forIn_x27_loop___redArg(v___x_2275_, v___f_2274_, v_l_2272_, v_r_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList(lean_object* v_00_u03b1_2278_, lean_object* v_l_2279_, lean_object* v_cmp_2280_){
_start:
{
lean_object* v___f_2281_; lean_object* v___x_2282_; lean_object* v_r_2283_; lean_object* v___x_2284_; 
v___f_2281_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2281_, 0, v_cmp_2280_);
v___x_2282_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2283_ = lean_box(1);
v___x_2284_ = l_List_forIn_x27_loop___redArg(v___x_2282_, v___f_2281_, v_l_2279_, v_r_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg___lam__0(lean_object* v_acc_2285_, lean_object* v_k_2286_, lean_object* v_v_2287_){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v_k_2286_);
lean_ctor_set(v___x_2288_, 1, v_v_2287_);
v___x_2289_ = lean_array_push(v_acc_2285_, v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg(lean_object* v_t_2293_){
_start:
{
lean_object* v___f_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___f_2294_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__0));
v___x_2295_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__1));
v___x_2296_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2294_, v___x_2295_, v_t_2293_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray(lean_object* v_00_u03b1_2297_, lean_object* v_00_u03b2_2298_, lean_object* v_cmp_2299_, lean_object* v_inst_2300_, lean_object* v_t_2301_){
_start:
{
lean_object* v___f_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___f_2302_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__0));
v___x_2303_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__1));
v___x_2304_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2302_, v___x_2303_, v_t_2301_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___boxed(lean_object* v_00_u03b1_2305_, lean_object* v_00_u03b2_2306_, lean_object* v_cmp_2307_, lean_object* v_inst_2308_, lean_object* v_t_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Std_ExtTreeMap_toArray(v_00_u03b1_2305_, v_00_u03b2_2306_, v_cmp_2307_, v_inst_2308_, v_t_2309_);
lean_dec_ref(v_cmp_2307_);
return v_res_2310_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray___redArg(lean_object* v_a_2312_, lean_object* v_cmp_2313_){
_start:
{
lean_object* v___f_2314_; lean_object* v___x_2315_; lean_object* v_r_2316_; size_t v_sz_2317_; size_t v___x_2318_; lean_object* v___x_2319_; 
v___f_2314_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2314_, 0, v_cmp_2313_);
v___x_2315_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2316_ = lean_box(1);
v_sz_2317_ = lean_array_size(v_a_2312_);
v___x_2318_ = ((size_t)0ULL);
v___x_2319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2315_, v_a_2312_, v___f_2314_, v_sz_2317_, v___x_2318_, v_r_2316_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray(lean_object* v_00_u03b1_2320_, lean_object* v_00_u03b2_2321_, lean_object* v_a_2322_, lean_object* v_cmp_2323_){
_start:
{
lean_object* v___f_2324_; lean_object* v___x_2325_; lean_object* v_r_2326_; size_t v_sz_2327_; size_t v___x_2328_; lean_object* v___x_2329_; 
v___f_2324_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2324_, 0, v_cmp_2323_);
v___x_2325_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2326_ = lean_box(1);
v_sz_2327_ = lean_array_size(v_a_2322_);
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2325_, v_a_2322_, v___f_2324_, v_sz_2327_, v___x_2328_, v_r_2326_);
return v___x_2329_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray___redArg(lean_object* v_a_2331_, lean_object* v_cmp_2332_){
_start:
{
lean_object* v___f_2333_; lean_object* v___x_2334_; lean_object* v_r_2335_; size_t v_sz_2336_; size_t v___x_2337_; lean_object* v___x_2338_; 
v___f_2333_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2333_, 0, v_cmp_2332_);
v___x_2334_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2335_ = lean_box(1);
v_sz_2336_ = lean_array_size(v_a_2331_);
v___x_2337_ = ((size_t)0ULL);
v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2334_, v_a_2331_, v___f_2333_, v_sz_2336_, v___x_2337_, v_r_2335_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray(lean_object* v_00_u03b1_2339_, lean_object* v_a_2340_, lean_object* v_cmp_2341_){
_start:
{
lean_object* v___f_2342_; lean_object* v___x_2343_; lean_object* v_r_2344_; size_t v_sz_2345_; size_t v___x_2346_; lean_object* v___x_2347_; 
v___f_2342_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2342_, 0, v_cmp_2341_);
v___x_2343_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2344_ = lean_box(1);
v_sz_2345_ = lean_array_size(v_a_2340_);
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2343_, v_a_2340_, v___f_2342_, v_sz_2345_, v___x_2346_, v_r_2344_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify___redArg(lean_object* v_cmp_2348_, lean_object* v_t_2349_, lean_object* v_a_2350_, lean_object* v_f_2351_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2348_, v_a_2350_, v_f_2351_, v_t_2349_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify(lean_object* v_00_u03b1_2353_, lean_object* v_00_u03b2_2354_, lean_object* v_cmp_2355_, lean_object* v_inst_2356_, lean_object* v_t_2357_, lean_object* v_a_2358_, lean_object* v_f_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2355_, v_a_2358_, v_f_2359_, v_t_2357_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter___redArg(lean_object* v_cmp_2361_, lean_object* v_t_2362_, lean_object* v_a_2363_, lean_object* v_f_2364_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2361_, v_a_2363_, v_f_2364_, v_t_2362_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter(lean_object* v_00_u03b1_2366_, lean_object* v_00_u03b2_2367_, lean_object* v_cmp_2368_, lean_object* v_inst_2369_, lean_object* v_t_2370_, lean_object* v_a_2371_, lean_object* v_f_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2368_, v_a_2371_, v_f_2372_, v_t_2370_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2374_, lean_object* v_mergeFn_2375_, lean_object* v_a_2376_, lean_object* v_x_2377_){
_start:
{
if (lean_obj_tag(v_x_2377_) == 0)
{
lean_object* v___x_2378_; 
lean_dec(v_a_2376_);
lean_dec(v_mergeFn_2375_);
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_b_u2082_2374_);
return v___x_2378_;
}
else
{
lean_object* v_val_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2387_; 
v_val_2379_ = lean_ctor_get(v_x_2377_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_x_2377_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2381_ = v_x_2377_;
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_val_2379_);
lean_dec(v_x_2377_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2383_ = lean_apply_3(v_mergeFn_2375_, v_a_2376_, v_val_2379_, v_b_u2082_2374_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2383_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2388_, lean_object* v_cmp_2389_, lean_object* v_t_2390_, lean_object* v_a_2391_, lean_object* v_b_u2082_2392_){
_start:
{
lean_object* v___f_2393_; lean_object* v___x_2394_; 
lean_inc(v_a_2391_);
v___f_2393_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2393_, 0, v_b_u2082_2392_);
lean_closure_set(v___f_2393_, 1, v_mergeFn_2388_);
lean_closure_set(v___f_2393_, 2, v_a_2391_);
v___x_2394_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2389_, v_a_2391_, v___f_2393_, v_t_2390_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg(lean_object* v_cmp_2395_, lean_object* v_mergeFn_2396_, lean_object* v_t_u2081_2397_, lean_object* v_t_u2082_2398_){
_start:
{
lean_object* v___f_2399_; lean_object* v___x_2400_; 
v___f_2399_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2399_, 0, v_mergeFn_2396_);
lean_closure_set(v___f_2399_, 1, v_cmp_2395_);
v___x_2400_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2399_, v_t_u2081_2397_, v_t_u2082_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith(lean_object* v_00_u03b1_2401_, lean_object* v_00_u03b2_2402_, lean_object* v_cmp_2403_, lean_object* v_inst_2404_, lean_object* v_mergeFn_2405_, lean_object* v_t_u2081_2406_, lean_object* v_t_u2082_2407_){
_start:
{
lean_object* v___f_2408_; lean_object* v___x_2409_; 
v___f_2408_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2408_, 0, v_mergeFn_2405_);
lean_closure_set(v___f_2408_, 1, v_cmp_2403_);
v___x_2409_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2408_, v_t_u2081_2406_, v_t_u2082_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_2410_, lean_object* v_x_2411_, lean_object* v_____s_2412_){
_start:
{
lean_object* v_fst_2413_; lean_object* v_snd_2414_; lean_object* v_acc_2415_; lean_object* v___x_2416_; 
v_fst_2413_ = lean_ctor_get(v_x_2411_, 0);
lean_inc(v_fst_2413_);
v_snd_2414_ = lean_ctor_get(v_x_2411_, 1);
lean_inc(v_snd_2414_);
lean_dec_ref(v_x_2411_);
v_acc_2415_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2410_, v_fst_2413_, v_snd_2414_, v_____s_2412_);
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_acc_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg(lean_object* v_cmp_2417_, lean_object* v_inst_2418_, lean_object* v_t_2419_, lean_object* v_l_2420_){
_start:
{
lean_object* v___f_2421_; lean_object* v___x_2422_; 
v___f_2421_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2421_, 0, v_cmp_2417_);
v___x_2422_ = lean_apply_4(v_inst_2418_, lean_box(0), v_l_2420_, v_t_2419_, v___f_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany(lean_object* v_00_u03b1_2423_, lean_object* v_00_u03b2_2424_, lean_object* v_cmp_2425_, lean_object* v_inst_2426_, lean_object* v_00_u03c1_2427_, lean_object* v_inst_2428_, lean_object* v_t_2429_, lean_object* v_l_2430_){
_start:
{
lean_object* v___f_2431_; lean_object* v___x_2432_; 
v___f_2431_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2431_, 0, v_cmp_2425_);
v___x_2432_ = lean_apply_4(v_inst_2428_, lean_box(0), v_l_2430_, v_t_2429_, v___f_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_2433_, lean_object* v_a_2434_, lean_object* v_____s_2435_){
_start:
{
uint8_t v___x_2436_; 
lean_inc(v_____s_2435_);
lean_inc(v_a_2434_);
lean_inc_ref(v_cmp_2433_);
v___x_2436_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2433_, v_a_2434_, v_____s_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = lean_box(0);
v___x_2438_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2433_, v_a_2434_, v___x_2437_, v_____s_2435_);
v___x_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
else
{
lean_object* v___x_2440_; 
lean_dec(v_a_2434_);
lean_dec_ref(v_cmp_2433_);
v___x_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_____s_2435_);
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg(lean_object* v_cmp_2441_, lean_object* v_inst_2442_, lean_object* v_t_2443_, lean_object* v_l_2444_){
_start:
{
lean_object* v___f_2445_; lean_object* v___x_2446_; 
v___f_2445_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2445_, 0, v_cmp_2441_);
v___x_2446_ = lean_apply_4(v_inst_2442_, lean_box(0), v_l_2444_, v_t_2443_, v___f_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit(lean_object* v_00_u03b1_2447_, lean_object* v_cmp_2448_, lean_object* v_inst_2449_, lean_object* v_00_u03c1_2450_, lean_object* v_inst_2451_, lean_object* v_t_2452_, lean_object* v_l_2453_){
_start:
{
lean_object* v___f_2454_; lean_object* v___x_2455_; 
v___f_2454_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2454_, 0, v_cmp_2448_);
v___x_2455_ = lean_apply_4(v_inst_2451_, lean_box(0), v_l_2453_, v_t_2452_, v___f_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union___redArg(lean_object* v_cmp_2456_, lean_object* v_t_u2081_2457_, lean_object* v_t_u2082_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_2456_, v_t_u2081_2457_, v_t_u2082_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union(lean_object* v_00_u03b1_2460_, lean_object* v_00_u03b2_2461_, lean_object* v_cmp_2462_, lean_object* v_inst_2463_, lean_object* v_t_u2081_2464_, lean_object* v_t_u2082_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_2462_, v_t_u2081_2464_, v_t_u2082_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp___redArg(lean_object* v_cmp_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_union), 6, 4);
lean_closure_set(v___x_2468_, 0, lean_box(0));
lean_closure_set(v___x_2468_, 1, lean_box(0));
lean_closure_set(v___x_2468_, 2, v_cmp_2467_);
lean_closure_set(v___x_2468_, 3, lean_box(0));
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp(lean_object* v_00_u03b1_2469_, lean_object* v_00_u03b2_2470_, lean_object* v_cmp_2471_, lean_object* v_inst_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_union), 6, 4);
lean_closure_set(v___x_2473_, 0, lean_box(0));
lean_closure_set(v___x_2473_, 1, lean_box(0));
lean_closure_set(v___x_2473_, 2, v_cmp_2471_);
lean_closure_set(v___x_2473_, 3, lean_box(0));
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter___redArg(lean_object* v_cmp_2474_, lean_object* v_t_u2081_2475_, lean_object* v_t_u2082_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_2474_, v_t_u2081_2475_, v_t_u2082_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter(lean_object* v_00_u03b1_2478_, lean_object* v_00_u03b2_2479_, lean_object* v_cmp_2480_, lean_object* v_inst_2481_, lean_object* v_t_u2081_2482_, lean_object* v_t_u2082_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_2480_, v_t_u2081_2482_, v_t_u2082_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp___redArg(lean_object* v_cmp_2485_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_inter), 6, 4);
lean_closure_set(v___x_2486_, 0, lean_box(0));
lean_closure_set(v___x_2486_, 1, lean_box(0));
lean_closure_set(v___x_2486_, 2, v_cmp_2485_);
lean_closure_set(v___x_2486_, 3, lean_box(0));
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp(lean_object* v_00_u03b1_2487_, lean_object* v_00_u03b2_2488_, lean_object* v_cmp_2489_, lean_object* v_inst_2490_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_inter), 6, 4);
lean_closure_set(v___x_2491_, 0, lean_box(0));
lean_closure_set(v___x_2491_, 1, lean_box(0));
lean_closure_set(v___x_2491_, 2, v_cmp_2489_);
lean_closure_set(v___x_2491_, 3, lean_box(0));
return v___x_2491_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(lean_object* v_cmp_2492_, lean_object* v_inst_2493_, lean_object* v_m_u2081_2494_, lean_object* v_m_u2082_2495_){
_start:
{
uint8_t v___x_2496_; 
v___x_2496_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2492_, v_inst_2493_, v_m_u2081_2494_, v_m_u2082_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_2497_, lean_object* v_inst_2498_, lean_object* v_m_u2081_2499_, lean_object* v_m_u2082_2500_){
_start:
{
uint8_t v_res_2501_; lean_object* v_r_2502_; 
v_res_2501_ = l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(v_cmp_2497_, v_inst_2498_, v_m_u2081_2499_, v_m_u2082_2500_);
v_r_2502_ = lean_box(v_res_2501_);
return v_r_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg(lean_object* v_cmp_2503_, lean_object* v_inst_2504_){
_start:
{
lean_object* v___f_2505_; 
v___f_2505_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2505_, 0, v_cmp_2503_);
lean_closure_set(v___f_2505_, 1, v_inst_2504_);
return v___f_2505_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp(lean_object* v_00_u03b1_2506_, lean_object* v_00_u03b2_2507_, lean_object* v_cmp_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_){
_start:
{
lean_object* v___f_2511_; 
v___f_2511_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2511_, 0, v_cmp_2508_);
lean_closure_set(v___f_2511_, 1, v_inst_2510_);
return v___f_2511_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff___redArg(lean_object* v_cmp_2512_, lean_object* v_t_u2081_2513_, lean_object* v_t_u2082_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2512_, v_t_u2081_2513_, v_t_u2082_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff(lean_object* v_00_u03b1_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_cmp_2518_, lean_object* v_inst_2519_, lean_object* v_t_u2081_2520_, lean_object* v_t_u2082_2521_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2518_, v_t_u2081_2520_, v_t_u2082_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp___redArg(lean_object* v_cmp_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_diff), 6, 4);
lean_closure_set(v___x_2524_, 0, lean_box(0));
lean_closure_set(v___x_2524_, 1, lean_box(0));
lean_closure_set(v___x_2524_, 2, v_cmp_2523_);
lean_closure_set(v___x_2524_, 3, lean_box(0));
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp(lean_object* v_00_u03b1_2525_, lean_object* v_00_u03b2_2526_, lean_object* v_cmp_2527_, lean_object* v_inst_2528_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_diff), 6, 4);
lean_closure_set(v___x_2529_, 0, lean_box(0));
lean_closure_set(v___x_2529_, 1, lean_box(0));
lean_closure_set(v___x_2529_, 2, v_cmp_2527_);
lean_closure_set(v___x_2529_, 3, lean_box(0));
return v___x_2529_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(lean_object* v_cmp_2530_, lean_object* v_inst_2531_, lean_object* v_x_2532_, lean_object* v_x_2533_){
_start:
{
uint8_t v___x_2534_; 
v___x_2534_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2530_, v_inst_2531_, v_x_2532_, v_x_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_2535_, lean_object* v_inst_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_){
_start:
{
uint8_t v_res_2539_; lean_object* v_r_2540_; 
v_res_2539_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(v_cmp_2535_, v_inst_2536_, v_x_2537_, v_x_2538_);
v_r_2540_ = lean_box(v_res_2539_);
return v_r_2540_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(lean_object* v_00_u03b1_2541_, lean_object* v_00_u03b2_2542_, lean_object* v_cmp_2543_, lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_x_2548_, lean_object* v_x_2549_){
_start:
{
uint8_t v___x_2550_; 
v___x_2550_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2543_, v_inst_2546_, v_x_2548_, v_x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_2551_, lean_object* v_00_u03b2_2552_, lean_object* v_cmp_2553_, lean_object* v_inst_2554_, lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_){
_start:
{
uint8_t v_res_2560_; lean_object* v_r_2561_; 
v_res_2560_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(v_00_u03b1_2551_, v_00_u03b2_2552_, v_cmp_2553_, v_inst_2554_, v_inst_2555_, v_inst_2556_, v_inst_2557_, v_x_2558_, v_x_2559_);
v_r_2561_ = lean_box(v_res_2560_);
return v_r_2561_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_2562_, lean_object* v_a_2563_, lean_object* v_____s_2564_){
_start:
{
lean_object* v_acc_2565_; lean_object* v___x_2566_; 
v_acc_2565_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2562_, v_a_2563_, v_____s_2564_);
v___x_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2566_, 0, v_acc_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg(lean_object* v_cmp_2567_, lean_object* v_inst_2568_, lean_object* v_t_2569_, lean_object* v_l_2570_){
_start:
{
lean_object* v___f_2571_; lean_object* v___x_2572_; 
v___f_2571_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2571_, 0, v_cmp_2567_);
v___x_2572_ = lean_apply_4(v_inst_2568_, lean_box(0), v_l_2570_, v_t_2569_, v___f_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany(lean_object* v_00_u03b1_2573_, lean_object* v_00_u03b2_2574_, lean_object* v_cmp_2575_, lean_object* v_inst_2576_, lean_object* v_00_u03c1_2577_, lean_object* v_inst_2578_, lean_object* v_t_2579_, lean_object* v_l_2580_){
_start:
{
lean_object* v___f_2581_; lean_object* v___x_2582_; 
v___f_2581_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2581_, 0, v_cmp_2575_);
v___x_2582_ = lean_apply_4(v_inst_2578_, lean_box(0), v_l_2580_, v_t_2579_, v___f_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_2586_, lean_object* v___x_2587_, lean_object* v_m_2588_, lean_object* v_prec_2589_){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2590_ = ((lean_object*)(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_2591_ = lean_box(0);
v___x_2592_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2593_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2592_, v___f_2586_, v___x_2591_, v_m_2588_);
v___x_2594_ = l_List_repr___redArg(v___x_2587_, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2590_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = l_Repr_addAppParen(v___x_2595_, v_prec_2589_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_2597_, lean_object* v___x_2598_, lean_object* v_m_2599_, lean_object* v_prec_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(v___f_2597_, v___x_2598_, v_m_2599_, v_prec_2600_);
lean_dec(v_prec_2600_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg(lean_object* v_inst_2602_, lean_object* v_inst_2603_){
_start:
{
lean_object* v___f_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___f_2607_; 
v___f_2604_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___f_2605_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2605_, 0, v_inst_2603_);
v___x_2606_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2606_, 0, lean_box(0));
lean_closure_set(v___x_2606_, 1, lean_box(0));
lean_closure_set(v___x_2606_, 2, v_inst_2602_);
lean_closure_set(v___x_2606_, 3, v___f_2605_);
v___f_2607_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2607_, 0, v___f_2604_);
lean_closure_set(v___f_2607_, 1, v___x_2606_);
return v___f_2607_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp(lean_object* v_00_u03b1_2608_, lean_object* v_00_u03b2_2609_, lean_object* v_cmp_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_, lean_object* v_inst_2613_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg(v_inst_2612_, v_inst_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_2615_, lean_object* v_00_u03b2_2616_, lean_object* v_cmp_2617_, lean_object* v_inst_2618_, lean_object* v_inst_2619_, lean_object* v_inst_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Std_ExtTreeMap_instReprOfTransCmp(v_00_u03b1_2615_, v_00_u03b2_2616_, v_cmp_2617_, v_inst_2618_, v_inst_2619_, v_inst_2620_);
lean_dec_ref(v_cmp_2617_);
return v_res_2621_;
}
}
lean_object* runtime_initialize_Std_Data_ExtDTreeMap_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_ExtDTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_ExtTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_ExtTreeMap___auto__1 = _init_l_Std_ExtTreeMap___auto__1();
lean_mark_persistent(l_Std_ExtTreeMap___auto__1);
l_Std_ExtTreeMap_ofList___auto__1 = _init_l_Std_ExtTreeMap_ofList___auto__1();
lean_mark_persistent(l_Std_ExtTreeMap_ofList___auto__1);
l_Std_ExtTreeMap_unitOfList___auto__1 = _init_l_Std_ExtTreeMap_unitOfList___auto__1();
lean_mark_persistent(l_Std_ExtTreeMap_unitOfList___auto__1);
l_Std_ExtTreeMap_ofArray___auto__1 = _init_l_Std_ExtTreeMap_ofArray___auto__1();
lean_mark_persistent(l_Std_ExtTreeMap_ofArray___auto__1);
l_Std_ExtTreeMap_unitOfArray___auto__1 = _init_l_Std_ExtTreeMap_unitOfArray___auto__1();
lean_mark_persistent(l_Std_ExtTreeMap_unitOfArray___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_ExtDTreeMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_ExtTreeMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_ExtDTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_ExtTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_ExtTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_ExtTreeMap_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
