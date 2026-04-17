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
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___auto__1;
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___redArg___boxed(lean_object* v_cmp_359_, lean_object* v_inst_360_, lean_object* v_t_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_ExtTreeMap_get_x21___redArg(v_cmp_359_, v_inst_360_, v_t_361_, v_a_362_);
lean_dec(v_inst_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21(lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_cmp_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_t_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_366_, v_inst_368_, v_t_369_, v_a_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_get_x21___boxed(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_cmp_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_t_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_ExtTreeMap_get_x21(v_00_u03b1_372_, v_00_u03b2_373_, v_cmp_374_, v_inst_375_, v_inst_376_, v_t_377_, v_a_378_);
lean_dec(v_inst_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg(lean_object* v_cmp_380_, lean_object* v_t_381_, lean_object* v_a_382_, lean_object* v_fallback_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_380_, v_t_381_, v_a_382_, v_fallback_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___redArg___boxed(lean_object* v_cmp_385_, lean_object* v_t_386_, lean_object* v_a_387_, lean_object* v_fallback_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_ExtTreeMap_getD___redArg(v_cmp_385_, v_t_386_, v_a_387_, v_fallback_388_);
lean_dec(v_fallback_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD(lean_object* v_00_u03b1_390_, lean_object* v_00_u03b2_391_, lean_object* v_cmp_392_, lean_object* v_inst_393_, lean_object* v_t_394_, lean_object* v_a_395_, lean_object* v_fallback_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_392_, v_t_394_, v_a_395_, v_fallback_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getD___boxed(lean_object* v_00_u03b1_398_, lean_object* v_00_u03b2_399_, lean_object* v_cmp_400_, lean_object* v_inst_401_, lean_object* v_t_402_, lean_object* v_a_403_, lean_object* v_fallback_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_ExtTreeMap_getD(v_00_u03b1_398_, v_00_u03b2_399_, v_cmp_400_, v_inst_401_, v_t_402_, v_a_403_, v_fallback_404_);
lean_dec(v_fallback_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_cmp_406_, lean_object* v_m_407_, lean_object* v_a_408_, lean_object* v_h_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_406_, v_m_407_, v_a_408_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_cmp_411_, lean_object* v_m_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_411_, v_m_412_, v_a_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_cmp_415_, lean_object* v_inst_416_, lean_object* v_m_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_415_, v_inst_416_, v_m_417_, v_a_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_cmp_420_, lean_object* v_inst_421_, lean_object* v_m_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(v_cmp_420_, v_inst_421_, v_m_422_, v_a_423_);
lean_dec(v_inst_421_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(lean_object* v_cmp_425_){
_start:
{
lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___f_428_; lean_object* v___x_429_; 
lean_inc_ref_n(v_cmp_425_, 2);
v___f_426_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0), 4, 1);
lean_closure_set(v___f_426_, 0, v_cmp_425_);
v___f_427_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1), 3, 1);
lean_closure_set(v___f_427_, 0, v_cmp_425_);
v___f_428_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_428_, 0, v_cmp_425_);
v___x_429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_429_, 0, v___f_426_);
lean_ctor_set(v___x_429_, 1, v___f_427_);
lean_ctor_set(v___x_429_, 2, v___f_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instGetElem_x3fMem(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b2_431_, lean_object* v_cmp_432_, lean_object* v_inst_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(v_cmp_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f___redArg(lean_object* v_cmp_435_, lean_object* v_t_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_435_, v_t_436_, v_a_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x3f(lean_object* v_00_u03b1_439_, lean_object* v_00_u03b2_440_, lean_object* v_cmp_441_, lean_object* v_inst_442_, lean_object* v_t_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_441_, v_t_443_, v_a_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey___redArg(lean_object* v_cmp_446_, lean_object* v_t_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_446_, v_t_447_, v_a_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey(lean_object* v_00_u03b1_450_, lean_object* v_00_u03b2_451_, lean_object* v_cmp_452_, lean_object* v_inst_453_, lean_object* v_t_454_, lean_object* v_a_455_, lean_object* v_h_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_452_, v_t_454_, v_a_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg(lean_object* v_cmp_458_, lean_object* v_inst_459_, lean_object* v_t_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_458_, v_t_460_, v_a_461_, v_inst_459_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___redArg___boxed(lean_object* v_cmp_463_, lean_object* v_inst_464_, lean_object* v_t_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_ExtTreeMap_getKey_x21___redArg(v_cmp_463_, v_inst_464_, v_t_465_, v_a_466_);
lean_dec(v_inst_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21(lean_object* v_00_u03b1_468_, lean_object* v_00_u03b2_469_, lean_object* v_cmp_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_t_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_470_, v_t_473_, v_a_474_, v_inst_472_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKey_x21___boxed(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_cmp_478_, lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_t_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_ExtTreeMap_getKey_x21(v_00_u03b1_476_, v_00_u03b2_477_, v_cmp_478_, v_inst_479_, v_inst_480_, v_t_481_, v_a_482_);
lean_dec(v_inst_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg(lean_object* v_cmp_484_, lean_object* v_t_485_, lean_object* v_a_486_, lean_object* v_fallback_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_484_, v_t_485_, v_a_486_, v_fallback_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___redArg___boxed(lean_object* v_cmp_489_, lean_object* v_t_490_, lean_object* v_a_491_, lean_object* v_fallback_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_ExtTreeMap_getKeyD___redArg(v_cmp_489_, v_t_490_, v_a_491_, v_fallback_492_);
lean_dec(v_fallback_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_cmp_496_, lean_object* v_inst_497_, lean_object* v_t_498_, lean_object* v_a_499_, lean_object* v_fallback_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_496_, v_t_498_, v_a_499_, v_fallback_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyD___boxed(lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_cmp_504_, lean_object* v_inst_505_, lean_object* v_t_506_, lean_object* v_a_507_, lean_object* v_fallback_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_ExtTreeMap_getKeyD(v_00_u03b1_502_, v_00_u03b2_503_, v_cmp_504_, v_inst_505_, v_t_506_, v_a_507_, v_fallback_508_);
lean_dec(v_fallback_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg(lean_object* v_t_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___redArg___boxed(lean_object* v_t_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_ExtTreeMap_minEntry_x3f___redArg(v_t_512_);
lean_dec(v_t_512_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f(lean_object* v_00_u03b1_514_, lean_object* v_00_u03b2_515_, lean_object* v_cmp_516_, lean_object* v_inst_517_, lean_object* v_t_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x3f___boxed(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_cmp_522_, lean_object* v_inst_523_, lean_object* v_t_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_ExtTreeMap_minEntry_x3f(v_00_u03b1_520_, v_00_u03b2_521_, v_cmp_522_, v_inst_523_, v_t_524_);
lean_dec(v_t_524_);
lean_dec_ref(v_cmp_522_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg(lean_object* v_t_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___redArg___boxed(lean_object* v_t_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_ExtTreeMap_minEntry___redArg(v_t_528_);
lean_dec(v_t_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_cmp_532_, lean_object* v_inst_533_, lean_object* v_t_534_, lean_object* v_h_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry___boxed(lean_object* v_00_u03b1_537_, lean_object* v_00_u03b2_538_, lean_object* v_cmp_539_, lean_object* v_inst_540_, lean_object* v_t_541_, lean_object* v_h_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_ExtTreeMap_minEntry(v_00_u03b1_537_, v_00_u03b2_538_, v_cmp_539_, v_inst_540_, v_t_541_, v_h_542_);
lean_dec(v_t_541_);
lean_dec_ref(v_cmp_539_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg(lean_object* v_inst_544_, lean_object* v_t_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_544_, v_t_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___redArg___boxed(lean_object* v_inst_547_, lean_object* v_t_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_ExtTreeMap_minEntry_x21___redArg(v_inst_547_, v_t_548_);
lean_dec(v_t_548_);
lean_dec_ref(v_inst_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21(lean_object* v_00_u03b1_550_, lean_object* v_00_u03b2_551_, lean_object* v_cmp_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_t_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_554_, v_t_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntry_x21___boxed(lean_object* v_00_u03b1_557_, lean_object* v_00_u03b2_558_, lean_object* v_cmp_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_t_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_ExtTreeMap_minEntry_x21(v_00_u03b1_557_, v_00_u03b2_558_, v_cmp_559_, v_inst_560_, v_inst_561_, v_t_562_);
lean_dec(v_t_562_);
lean_dec_ref(v_inst_561_);
lean_dec_ref(v_cmp_559_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg(lean_object* v_t_564_, lean_object* v_fallback_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_564_, v_fallback_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___redArg___boxed(lean_object* v_t_567_, lean_object* v_fallback_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_ExtTreeMap_minEntryD___redArg(v_t_567_, v_fallback_568_);
lean_dec_ref(v_fallback_568_);
lean_dec(v_t_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD(lean_object* v_00_u03b1_570_, lean_object* v_00_u03b2_571_, lean_object* v_cmp_572_, lean_object* v_inst_573_, lean_object* v_t_574_, lean_object* v_fallback_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_574_, v_fallback_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minEntryD___boxed(lean_object* v_00_u03b1_577_, lean_object* v_00_u03b2_578_, lean_object* v_cmp_579_, lean_object* v_inst_580_, lean_object* v_t_581_, lean_object* v_fallback_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_ExtTreeMap_minEntryD(v_00_u03b1_577_, v_00_u03b2_578_, v_cmp_579_, v_inst_580_, v_t_581_, v_fallback_582_);
lean_dec_ref(v_fallback_582_);
lean_dec(v_t_581_);
lean_dec_ref(v_cmp_579_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg(lean_object* v_t_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___redArg___boxed(lean_object* v_t_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_ExtTreeMap_maxEntry_x3f___redArg(v_t_586_);
lean_dec(v_t_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_cmp_590_, lean_object* v_inst_591_, lean_object* v_t_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x3f___boxed(lean_object* v_00_u03b1_594_, lean_object* v_00_u03b2_595_, lean_object* v_cmp_596_, lean_object* v_inst_597_, lean_object* v_t_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_ExtTreeMap_maxEntry_x3f(v_00_u03b1_594_, v_00_u03b2_595_, v_cmp_596_, v_inst_597_, v_t_598_);
lean_dec(v_t_598_);
lean_dec_ref(v_cmp_596_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg(lean_object* v_t_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___redArg___boxed(lean_object* v_t_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_ExtTreeMap_maxEntry___redArg(v_t_602_);
lean_dec(v_t_602_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry(lean_object* v_00_u03b1_604_, lean_object* v_00_u03b2_605_, lean_object* v_cmp_606_, lean_object* v_inst_607_, lean_object* v_t_608_, lean_object* v_h_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry___boxed(lean_object* v_00_u03b1_611_, lean_object* v_00_u03b2_612_, lean_object* v_cmp_613_, lean_object* v_inst_614_, lean_object* v_t_615_, lean_object* v_h_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_ExtTreeMap_maxEntry(v_00_u03b1_611_, v_00_u03b2_612_, v_cmp_613_, v_inst_614_, v_t_615_, v_h_616_);
lean_dec(v_t_615_);
lean_dec_ref(v_cmp_613_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg(lean_object* v_inst_618_, lean_object* v_t_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_618_, v_t_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___redArg___boxed(lean_object* v_inst_621_, lean_object* v_t_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_ExtTreeMap_maxEntry_x21___redArg(v_inst_621_, v_t_622_);
lean_dec(v_t_622_);
lean_dec_ref(v_inst_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21(lean_object* v_00_u03b1_624_, lean_object* v_00_u03b2_625_, lean_object* v_cmp_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_t_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_628_, v_t_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntry_x21___boxed(lean_object* v_00_u03b1_631_, lean_object* v_00_u03b2_632_, lean_object* v_cmp_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_t_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_ExtTreeMap_maxEntry_x21(v_00_u03b1_631_, v_00_u03b2_632_, v_cmp_633_, v_inst_634_, v_inst_635_, v_t_636_);
lean_dec(v_t_636_);
lean_dec_ref(v_inst_635_);
lean_dec_ref(v_cmp_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg(lean_object* v_t_638_, lean_object* v_fallback_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_638_, v_fallback_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___redArg___boxed(lean_object* v_t_641_, lean_object* v_fallback_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_ExtTreeMap_maxEntryD___redArg(v_t_641_, v_fallback_642_);
lean_dec_ref(v_fallback_642_);
lean_dec(v_t_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD(lean_object* v_00_u03b1_644_, lean_object* v_00_u03b2_645_, lean_object* v_cmp_646_, lean_object* v_inst_647_, lean_object* v_t_648_, lean_object* v_fallback_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_648_, v_fallback_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxEntryD___boxed(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b2_652_, lean_object* v_cmp_653_, lean_object* v_inst_654_, lean_object* v_t_655_, lean_object* v_fallback_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_ExtTreeMap_maxEntryD(v_00_u03b1_651_, v_00_u03b2_652_, v_cmp_653_, v_inst_654_, v_t_655_, v_fallback_656_);
lean_dec_ref(v_fallback_656_);
lean_dec(v_t_655_);
lean_dec_ref(v_cmp_653_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg(lean_object* v_t_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___redArg___boxed(lean_object* v_t_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_ExtTreeMap_minKey_x3f___redArg(v_t_660_);
lean_dec(v_t_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_cmp_664_, lean_object* v_inst_665_, lean_object* v_t_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x3f___boxed(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_cmp_670_, lean_object* v_inst_671_, lean_object* v_t_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_ExtTreeMap_minKey_x3f(v_00_u03b1_668_, v_00_u03b2_669_, v_cmp_670_, v_inst_671_, v_t_672_);
lean_dec(v_t_672_);
lean_dec_ref(v_cmp_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg(lean_object* v_t_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___redArg___boxed(lean_object* v_t_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_ExtTreeMap_minKey___redArg(v_t_676_);
lean_dec(v_t_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_cmp_680_, lean_object* v_inst_681_, lean_object* v_t_682_, lean_object* v_h_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey___boxed(lean_object* v_00_u03b1_685_, lean_object* v_00_u03b2_686_, lean_object* v_cmp_687_, lean_object* v_inst_688_, lean_object* v_t_689_, lean_object* v_h_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_ExtTreeMap_minKey(v_00_u03b1_685_, v_00_u03b2_686_, v_cmp_687_, v_inst_688_, v_t_689_, v_h_690_);
lean_dec(v_t_689_);
lean_dec_ref(v_cmp_687_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg(lean_object* v_inst_692_, lean_object* v_t_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_692_, v_t_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___redArg___boxed(lean_object* v_inst_695_, lean_object* v_t_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_ExtTreeMap_minKey_x21___redArg(v_inst_695_, v_t_696_);
lean_dec(v_t_696_);
lean_dec(v_inst_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_cmp_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_t_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_702_, v_t_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKey_x21___boxed(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b2_706_, lean_object* v_cmp_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_t_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_ExtTreeMap_minKey_x21(v_00_u03b1_705_, v_00_u03b2_706_, v_cmp_707_, v_inst_708_, v_inst_709_, v_t_710_);
lean_dec(v_t_710_);
lean_dec(v_inst_709_);
lean_dec_ref(v_cmp_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg(lean_object* v_t_712_, lean_object* v_fallback_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_712_, v_fallback_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___redArg___boxed(lean_object* v_t_715_, lean_object* v_fallback_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_ExtTreeMap_minKeyD___redArg(v_t_715_, v_fallback_716_);
lean_dec(v_fallback_716_);
lean_dec(v_t_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD(lean_object* v_00_u03b1_718_, lean_object* v_00_u03b2_719_, lean_object* v_cmp_720_, lean_object* v_inst_721_, lean_object* v_t_722_, lean_object* v_fallback_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_722_, v_fallback_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_minKeyD___boxed(lean_object* v_00_u03b1_725_, lean_object* v_00_u03b2_726_, lean_object* v_cmp_727_, lean_object* v_inst_728_, lean_object* v_t_729_, lean_object* v_fallback_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_ExtTreeMap_minKeyD(v_00_u03b1_725_, v_00_u03b2_726_, v_cmp_727_, v_inst_728_, v_t_729_, v_fallback_730_);
lean_dec(v_fallback_730_);
lean_dec(v_t_729_);
lean_dec_ref(v_cmp_727_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg(lean_object* v_t_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___redArg___boxed(lean_object* v_t_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_ExtTreeMap_maxKey_x3f___redArg(v_t_734_);
lean_dec(v_t_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f(lean_object* v_00_u03b1_736_, lean_object* v_00_u03b2_737_, lean_object* v_cmp_738_, lean_object* v_inst_739_, lean_object* v_t_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x3f___boxed(lean_object* v_00_u03b1_742_, lean_object* v_00_u03b2_743_, lean_object* v_cmp_744_, lean_object* v_inst_745_, lean_object* v_t_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_ExtTreeMap_maxKey_x3f(v_00_u03b1_742_, v_00_u03b2_743_, v_cmp_744_, v_inst_745_, v_t_746_);
lean_dec(v_t_746_);
lean_dec_ref(v_cmp_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg(lean_object* v_t_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___redArg___boxed(lean_object* v_t_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_ExtTreeMap_maxKey___redArg(v_t_750_);
lean_dec(v_t_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey(lean_object* v_00_u03b1_752_, lean_object* v_00_u03b2_753_, lean_object* v_cmp_754_, lean_object* v_inst_755_, lean_object* v_t_756_, lean_object* v_h_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey___boxed(lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_cmp_761_, lean_object* v_inst_762_, lean_object* v_t_763_, lean_object* v_h_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_ExtTreeMap_maxKey(v_00_u03b1_759_, v_00_u03b2_760_, v_cmp_761_, v_inst_762_, v_t_763_, v_h_764_);
lean_dec(v_t_763_);
lean_dec_ref(v_cmp_761_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg(lean_object* v_inst_766_, lean_object* v_t_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_766_, v_t_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___redArg___boxed(lean_object* v_inst_769_, lean_object* v_t_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_ExtTreeMap_maxKey_x21___redArg(v_inst_769_, v_t_770_);
lean_dec(v_t_770_);
lean_dec(v_inst_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_cmp_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_t_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_776_, v_t_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKey_x21___boxed(lean_object* v_00_u03b1_779_, lean_object* v_00_u03b2_780_, lean_object* v_cmp_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_t_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_ExtTreeMap_maxKey_x21(v_00_u03b1_779_, v_00_u03b2_780_, v_cmp_781_, v_inst_782_, v_inst_783_, v_t_784_);
lean_dec(v_t_784_);
lean_dec(v_inst_783_);
lean_dec_ref(v_cmp_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg(lean_object* v_t_786_, lean_object* v_fallback_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_786_, v_fallback_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___redArg___boxed(lean_object* v_t_789_, lean_object* v_fallback_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_ExtTreeMap_maxKeyD___redArg(v_t_789_, v_fallback_790_);
lean_dec(v_fallback_790_);
lean_dec(v_t_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_cmp_794_, lean_object* v_inst_795_, lean_object* v_t_796_, lean_object* v_fallback_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_796_, v_fallback_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_maxKeyD___boxed(lean_object* v_00_u03b1_799_, lean_object* v_00_u03b2_800_, lean_object* v_cmp_801_, lean_object* v_inst_802_, lean_object* v_t_803_, lean_object* v_fallback_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_ExtTreeMap_maxKeyD(v_00_u03b1_799_, v_00_u03b2_800_, v_cmp_801_, v_inst_802_, v_t_803_, v_fallback_804_);
lean_dec(v_fallback_804_);
lean_dec(v_t_803_);
lean_dec_ref(v_cmp_801_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(lean_object* v_t_806_, lean_object* v_n_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_806_, v_n_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_809_, lean_object* v_n_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(v_t_809_, v_n_810_);
lean_dec(v_t_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f(lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_cmp_814_, lean_object* v_inst_815_, lean_object* v_t_816_, lean_object* v_n_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_816_, v_n_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_819_, lean_object* v_00_u03b2_820_, lean_object* v_cmp_821_, lean_object* v_inst_822_, lean_object* v_t_823_, lean_object* v_n_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_ExtTreeMap_entryAtIdx_x3f(v_00_u03b1_819_, v_00_u03b2_820_, v_cmp_821_, v_inst_822_, v_t_823_, v_n_824_);
lean_dec(v_t_823_);
lean_dec_ref(v_cmp_821_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg(lean_object* v_t_826_, lean_object* v_n_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_826_, v_n_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___redArg___boxed(lean_object* v_t_829_, lean_object* v_n_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_ExtTreeMap_entryAtIdx___redArg(v_t_829_, v_n_830_);
lean_dec(v_t_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx(lean_object* v_00_u03b1_832_, lean_object* v_00_u03b2_833_, lean_object* v_cmp_834_, lean_object* v_inst_835_, lean_object* v_t_836_, lean_object* v_n_837_, lean_object* v_h_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_836_, v_n_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx___boxed(lean_object* v_00_u03b1_840_, lean_object* v_00_u03b2_841_, lean_object* v_cmp_842_, lean_object* v_inst_843_, lean_object* v_t_844_, lean_object* v_n_845_, lean_object* v_h_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_ExtTreeMap_entryAtIdx(v_00_u03b1_840_, v_00_u03b2_841_, v_cmp_842_, v_inst_843_, v_t_844_, v_n_845_, v_h_846_);
lean_dec(v_t_844_);
lean_dec_ref(v_cmp_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg(lean_object* v_inst_848_, lean_object* v_t_849_, lean_object* v_n_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_848_, v_t_849_, v_n_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_852_, lean_object* v_t_853_, lean_object* v_n_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_ExtTreeMap_entryAtIdx_x21___redArg(v_inst_852_, v_t_853_, v_n_854_);
lean_dec(v_t_853_);
lean_dec_ref(v_inst_852_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21(lean_object* v_00_u03b1_856_, lean_object* v_00_u03b2_857_, lean_object* v_cmp_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_t_861_, lean_object* v_n_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_860_, v_t_861_, v_n_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_864_, lean_object* v_00_u03b2_865_, lean_object* v_cmp_866_, lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_t_869_, lean_object* v_n_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_ExtTreeMap_entryAtIdx_x21(v_00_u03b1_864_, v_00_u03b2_865_, v_cmp_866_, v_inst_867_, v_inst_868_, v_t_869_, v_n_870_);
lean_dec(v_t_869_);
lean_dec_ref(v_inst_868_);
lean_dec_ref(v_cmp_866_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg(lean_object* v_t_872_, lean_object* v_n_873_, lean_object* v_fallback_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_872_, v_n_873_, v_fallback_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___redArg___boxed(lean_object* v_t_876_, lean_object* v_n_877_, lean_object* v_fallback_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_ExtTreeMap_entryAtIdxD___redArg(v_t_876_, v_n_877_, v_fallback_878_);
lean_dec_ref(v_fallback_878_);
lean_dec(v_t_876_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD(lean_object* v_00_u03b1_880_, lean_object* v_00_u03b2_881_, lean_object* v_cmp_882_, lean_object* v_inst_883_, lean_object* v_t_884_, lean_object* v_n_885_, lean_object* v_fallback_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_884_, v_n_885_, v_fallback_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_entryAtIdxD___boxed(lean_object* v_00_u03b1_888_, lean_object* v_00_u03b2_889_, lean_object* v_cmp_890_, lean_object* v_inst_891_, lean_object* v_t_892_, lean_object* v_n_893_, lean_object* v_fallback_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_ExtTreeMap_entryAtIdxD(v_00_u03b1_888_, v_00_u03b2_889_, v_cmp_890_, v_inst_891_, v_t_892_, v_n_893_, v_fallback_894_);
lean_dec_ref(v_fallback_894_);
lean_dec(v_t_892_);
lean_dec_ref(v_cmp_890_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(lean_object* v_t_896_, lean_object* v_n_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_896_, v_n_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_899_, lean_object* v_n_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(v_t_899_, v_n_900_);
lean_dec(v_t_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_cmp_904_, lean_object* v_inst_905_, lean_object* v_t_906_, lean_object* v_n_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_906_, v_n_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_909_, lean_object* v_00_u03b2_910_, lean_object* v_cmp_911_, lean_object* v_inst_912_, lean_object* v_t_913_, lean_object* v_n_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Std_ExtTreeMap_keyAtIdx_x3f(v_00_u03b1_909_, v_00_u03b2_910_, v_cmp_911_, v_inst_912_, v_t_913_, v_n_914_);
lean_dec(v_t_913_);
lean_dec_ref(v_cmp_911_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg(lean_object* v_t_916_, lean_object* v_n_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_916_, v_n_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___redArg___boxed(lean_object* v_t_919_, lean_object* v_n_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_ExtTreeMap_keyAtIdx___redArg(v_t_919_, v_n_920_);
lean_dec(v_t_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx(lean_object* v_00_u03b1_922_, lean_object* v_00_u03b2_923_, lean_object* v_cmp_924_, lean_object* v_inst_925_, lean_object* v_t_926_, lean_object* v_n_927_, lean_object* v_h_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_926_, v_n_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx___boxed(lean_object* v_00_u03b1_930_, lean_object* v_00_u03b2_931_, lean_object* v_cmp_932_, lean_object* v_inst_933_, lean_object* v_t_934_, lean_object* v_n_935_, lean_object* v_h_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_ExtTreeMap_keyAtIdx(v_00_u03b1_930_, v_00_u03b2_931_, v_cmp_932_, v_inst_933_, v_t_934_, v_n_935_, v_h_936_);
lean_dec(v_t_934_);
lean_dec_ref(v_cmp_932_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg(lean_object* v_inst_938_, lean_object* v_t_939_, lean_object* v_n_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_938_, v_t_939_, v_n_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_942_, lean_object* v_t_943_, lean_object* v_n_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_ExtTreeMap_keyAtIdx_x21___redArg(v_inst_942_, v_t_943_, v_n_944_);
lean_dec(v_t_943_);
lean_dec(v_inst_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_cmp_948_, lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_t_951_, lean_object* v_n_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_950_, v_t_951_, v_n_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_954_, lean_object* v_00_u03b2_955_, lean_object* v_cmp_956_, lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_t_959_, lean_object* v_n_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_ExtTreeMap_keyAtIdx_x21(v_00_u03b1_954_, v_00_u03b2_955_, v_cmp_956_, v_inst_957_, v_inst_958_, v_t_959_, v_n_960_);
lean_dec(v_t_959_);
lean_dec(v_inst_958_);
lean_dec_ref(v_cmp_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg(lean_object* v_t_962_, lean_object* v_n_963_, lean_object* v_fallback_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_962_, v_n_963_, v_fallback_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___redArg___boxed(lean_object* v_t_966_, lean_object* v_n_967_, lean_object* v_fallback_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_ExtTreeMap_keyAtIdxD___redArg(v_t_966_, v_n_967_, v_fallback_968_);
lean_dec(v_fallback_968_);
lean_dec(v_t_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD(lean_object* v_00_u03b1_970_, lean_object* v_00_u03b2_971_, lean_object* v_cmp_972_, lean_object* v_inst_973_, lean_object* v_t_974_, lean_object* v_n_975_, lean_object* v_fallback_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_974_, v_n_975_, v_fallback_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keyAtIdxD___boxed(lean_object* v_00_u03b1_978_, lean_object* v_00_u03b2_979_, lean_object* v_cmp_980_, lean_object* v_inst_981_, lean_object* v_t_982_, lean_object* v_n_983_, lean_object* v_fallback_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_ExtTreeMap_keyAtIdxD(v_00_u03b1_978_, v_00_u03b2_979_, v_cmp_980_, v_inst_981_, v_t_982_, v_n_983_, v_fallback_984_);
lean_dec(v_fallback_984_);
lean_dec(v_t_982_);
lean_dec_ref(v_cmp_980_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f___redArg(lean_object* v_cmp_986_, lean_object* v_t_987_, lean_object* v_k_988_){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_box(0);
v___x_990_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_986_, v_k_988_, v___x_989_, v_t_987_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x3f(lean_object* v_00_u03b1_991_, lean_object* v_00_u03b2_992_, lean_object* v_cmp_993_, lean_object* v_inst_994_, lean_object* v_t_995_, lean_object* v_k_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_box(0);
v___x_998_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_993_, v_k_996_, v___x_997_, v_t_995_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f___redArg(lean_object* v_cmp_999_, lean_object* v_t_1000_, lean_object* v_k_1001_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_box(0);
v___x_1003_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_999_, v_k_1001_, v___x_1002_, v_t_1000_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x3f(lean_object* v_00_u03b1_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_cmp_1006_, lean_object* v_inst_1007_, lean_object* v_t_1008_, lean_object* v_k_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1006_, v_k_1009_, v___x_1010_, v_t_1008_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f___redArg(lean_object* v_cmp_1012_, lean_object* v_t_1013_, lean_object* v_k_1014_){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1012_, v_k_1014_, v___x_1015_, v_t_1013_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x3f(lean_object* v_00_u03b1_1017_, lean_object* v_00_u03b2_1018_, lean_object* v_cmp_1019_, lean_object* v_inst_1020_, lean_object* v_t_1021_, lean_object* v_k_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_box(0);
v___x_1024_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1019_, v_k_1022_, v___x_1023_, v_t_1021_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f___redArg(lean_object* v_cmp_1025_, lean_object* v_t_1026_, lean_object* v_k_1027_){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_box(0);
v___x_1029_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1025_, v_k_1027_, v___x_1028_, v_t_1026_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x3f(lean_object* v_00_u03b1_1030_, lean_object* v_00_u03b2_1031_, lean_object* v_cmp_1032_, lean_object* v_inst_1033_, lean_object* v_t_1034_, lean_object* v_k_1035_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_box(0);
v___x_1037_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1032_, v_k_1035_, v___x_1036_, v_t_1034_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE___redArg(lean_object* v_cmp_1038_, lean_object* v_t_1039_, lean_object* v_k_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_1038_, v_k_1040_, v_t_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_cmp_1044_, lean_object* v_inst_1045_, lean_object* v_t_1046_, lean_object* v_k_1047_, lean_object* v_h_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_1044_, v_k_1047_, v_t_1046_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT___redArg(lean_object* v_cmp_1050_, lean_object* v_t_1051_, lean_object* v_k_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_1050_, v_k_1052_, v_t_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT(lean_object* v_00_u03b1_1054_, lean_object* v_00_u03b2_1055_, lean_object* v_cmp_1056_, lean_object* v_inst_1057_, lean_object* v_t_1058_, lean_object* v_k_1059_, lean_object* v_h_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_1056_, v_k_1059_, v_t_1058_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE___redArg(lean_object* v_cmp_1062_, lean_object* v_t_1063_, lean_object* v_k_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_1062_, v_k_1064_, v_t_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE(lean_object* v_00_u03b1_1066_, lean_object* v_00_u03b2_1067_, lean_object* v_cmp_1068_, lean_object* v_inst_1069_, lean_object* v_t_1070_, lean_object* v_k_1071_, lean_object* v_h_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_1068_, v_k_1071_, v_t_1070_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT___redArg(lean_object* v_cmp_1074_, lean_object* v_t_1075_, lean_object* v_k_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_1074_, v_k_1076_, v_t_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_cmp_1080_, lean_object* v_inst_1081_, lean_object* v_t_1082_, lean_object* v_k_1083_, lean_object* v_h_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_1080_, v_k_1083_, v_t_1082_);
return v___x_1085_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1089_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2));
v___x_1090_ = lean_unsigned_to_nat(14u);
v___x_1091_ = lean_unsigned_to_nat(22u);
v___x_1092_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1));
v___x_1093_ = ((lean_object*)(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0));
v___x_1094_ = l_mkPanicMessageWithDecl(v___x_1093_, v___x_1092_, v___x_1091_, v___x_1090_, v___x_1089_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg(lean_object* v_cmp_1095_, lean_object* v_inst_1096_, lean_object* v_t_1097_, lean_object* v_k_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_box(0);
v___x_1100_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1095_, v_k_1098_, v___x_1099_, v_t_1097_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1102_ = l_panic___redArg(v_inst_1096_, v___x_1101_);
return v___x_1102_;
}
else
{
lean_object* v_val_1103_; 
v_val_1103_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_val_1103_);
lean_dec_ref(v___x_1100_);
return v_val_1103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1104_, lean_object* v_inst_1105_, lean_object* v_t_1106_, lean_object* v_k_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Std_ExtTreeMap_getEntryGE_x21___redArg(v_cmp_1104_, v_inst_1105_, v_t_1106_, v_k_1107_);
lean_dec_ref(v_inst_1105_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21(lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_cmp_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_t_1114_, lean_object* v_k_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_box(0);
v___x_1117_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1111_, v_k_1115_, v___x_1116_, v_t_1114_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1119_ = l_panic___redArg(v_inst_1113_, v___x_1118_);
return v___x_1119_;
}
else
{
lean_object* v_val_1120_; 
v_val_1120_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_val_1120_);
lean_dec_ref(v___x_1117_);
return v_val_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1121_, lean_object* v_00_u03b2_1122_, lean_object* v_cmp_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_t_1126_, lean_object* v_k_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Std_ExtTreeMap_getEntryGE_x21(v_00_u03b1_1121_, v_00_u03b2_1122_, v_cmp_1123_, v_inst_1124_, v_inst_1125_, v_t_1126_, v_k_1127_);
lean_dec_ref(v_inst_1125_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg(lean_object* v_cmp_1129_, lean_object* v_inst_1130_, lean_object* v_t_1131_, lean_object* v_k_1132_){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_box(0);
v___x_1134_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1129_, v_k_1132_, v___x_1133_, v_t_1131_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1136_ = l_panic___redArg(v_inst_1130_, v___x_1135_);
return v___x_1136_;
}
else
{
lean_object* v_val_1137_; 
v_val_1137_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_val_1137_);
lean_dec_ref(v___x_1134_);
return v_val_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1138_, lean_object* v_inst_1139_, lean_object* v_t_1140_, lean_object* v_k_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_ExtTreeMap_getEntryGT_x21___redArg(v_cmp_1138_, v_inst_1139_, v_t_1140_, v_k_1141_);
lean_dec_ref(v_inst_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21(lean_object* v_00_u03b1_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_cmp_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_t_1148_, lean_object* v_k_1149_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_box(0);
v___x_1151_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1145_, v_k_1149_, v___x_1150_, v_t_1148_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1153_ = l_panic___redArg(v_inst_1147_, v___x_1152_);
return v___x_1153_;
}
else
{
lean_object* v_val_1154_; 
v_val_1154_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1154_);
lean_dec_ref(v___x_1151_);
return v_val_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_00_u03b2_1156_, lean_object* v_cmp_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_t_1160_, lean_object* v_k_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_ExtTreeMap_getEntryGT_x21(v_00_u03b1_1155_, v_00_u03b2_1156_, v_cmp_1157_, v_inst_1158_, v_inst_1159_, v_t_1160_, v_k_1161_);
lean_dec_ref(v_inst_1159_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg(lean_object* v_cmp_1163_, lean_object* v_inst_1164_, lean_object* v_t_1165_, lean_object* v_k_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1163_, v_k_1166_, v___x_1167_, v_t_1165_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1170_ = l_panic___redArg(v_inst_1164_, v___x_1169_);
return v___x_1170_;
}
else
{
lean_object* v_val_1171_; 
v_val_1171_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_val_1171_);
lean_dec_ref(v___x_1168_);
return v_val_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1172_, lean_object* v_inst_1173_, lean_object* v_t_1174_, lean_object* v_k_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_ExtTreeMap_getEntryLE_x21___redArg(v_cmp_1172_, v_inst_1173_, v_t_1174_, v_k_1175_);
lean_dec_ref(v_inst_1173_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21(lean_object* v_00_u03b1_1177_, lean_object* v_00_u03b2_1178_, lean_object* v_cmp_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_t_1182_, lean_object* v_k_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_box(0);
v___x_1185_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1179_, v_k_1183_, v___x_1184_, v_t_1182_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1187_ = l_panic___redArg(v_inst_1181_, v___x_1186_);
return v___x_1187_;
}
else
{
lean_object* v_val_1188_; 
v_val_1188_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_val_1188_);
lean_dec_ref(v___x_1185_);
return v_val_1188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1189_, lean_object* v_00_u03b2_1190_, lean_object* v_cmp_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_t_1194_, lean_object* v_k_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Std_ExtTreeMap_getEntryLE_x21(v_00_u03b1_1189_, v_00_u03b2_1190_, v_cmp_1191_, v_inst_1192_, v_inst_1193_, v_t_1194_, v_k_1195_);
lean_dec_ref(v_inst_1193_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg(lean_object* v_cmp_1197_, lean_object* v_inst_1198_, lean_object* v_t_1199_, lean_object* v_k_1200_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_box(0);
v___x_1202_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1197_, v_k_1200_, v___x_1201_, v_t_1199_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1204_ = l_panic___redArg(v_inst_1198_, v___x_1203_);
return v___x_1204_;
}
else
{
lean_object* v_val_1205_; 
v_val_1205_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_val_1205_);
lean_dec_ref(v___x_1202_);
return v_val_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1206_, lean_object* v_inst_1207_, lean_object* v_t_1208_, lean_object* v_k_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Std_ExtTreeMap_getEntryLT_x21___redArg(v_cmp_1206_, v_inst_1207_, v_t_1208_, v_k_1209_);
lean_dec_ref(v_inst_1207_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21(lean_object* v_00_u03b1_1211_, lean_object* v_00_u03b2_1212_, lean_object* v_cmp_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_t_1216_, lean_object* v_k_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1213_, v_k_1217_, v___x_1218_, v_t_1216_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1221_ = l_panic___redArg(v_inst_1215_, v___x_1220_);
return v___x_1221_;
}
else
{
lean_object* v_val_1222_; 
v_val_1222_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_val_1222_);
lean_dec_ref(v___x_1219_);
return v_val_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1223_, lean_object* v_00_u03b2_1224_, lean_object* v_cmp_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_t_1228_, lean_object* v_k_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Std_ExtTreeMap_getEntryLT_x21(v_00_u03b1_1223_, v_00_u03b2_1224_, v_cmp_1225_, v_inst_1226_, v_inst_1227_, v_t_1228_, v_k_1229_);
lean_dec_ref(v_inst_1227_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg(lean_object* v_cmp_1231_, lean_object* v_t_1232_, lean_object* v_k_1233_, lean_object* v_fallback_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1231_, v_k_1233_, v___x_1235_, v_t_1232_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_inc_ref(v_fallback_1234_);
return v_fallback_1234_;
}
else
{
lean_object* v_val_1237_; 
v_val_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_val_1237_);
lean_dec_ref(v___x_1236_);
return v_val_1237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___redArg___boxed(lean_object* v_cmp_1238_, lean_object* v_t_1239_, lean_object* v_k_1240_, lean_object* v_fallback_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Std_ExtTreeMap_getEntryGED___redArg(v_cmp_1238_, v_t_1239_, v_k_1240_, v_fallback_1241_);
lean_dec_ref(v_fallback_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED(lean_object* v_00_u03b1_1243_, lean_object* v_00_u03b2_1244_, lean_object* v_cmp_1245_, lean_object* v_inst_1246_, lean_object* v_t_1247_, lean_object* v_k_1248_, lean_object* v_fallback_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_box(0);
v___x_1251_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1245_, v_k_1248_, v___x_1250_, v_t_1247_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_inc_ref(v_fallback_1249_);
return v_fallback_1249_;
}
else
{
lean_object* v_val_1252_; 
v_val_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_val_1252_);
lean_dec_ref(v___x_1251_);
return v_val_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGED___boxed(lean_object* v_00_u03b1_1253_, lean_object* v_00_u03b2_1254_, lean_object* v_cmp_1255_, lean_object* v_inst_1256_, lean_object* v_t_1257_, lean_object* v_k_1258_, lean_object* v_fallback_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_ExtTreeMap_getEntryGED(v_00_u03b1_1253_, v_00_u03b2_1254_, v_cmp_1255_, v_inst_1256_, v_t_1257_, v_k_1258_, v_fallback_1259_);
lean_dec_ref(v_fallback_1259_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg(lean_object* v_cmp_1261_, lean_object* v_t_1262_, lean_object* v_k_1263_, lean_object* v_fallback_1264_){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_box(0);
v___x_1266_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1261_, v_k_1263_, v___x_1265_, v_t_1262_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_inc_ref(v_fallback_1264_);
return v_fallback_1264_;
}
else
{
lean_object* v_val_1267_; 
v_val_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_val_1267_);
lean_dec_ref(v___x_1266_);
return v_val_1267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___redArg___boxed(lean_object* v_cmp_1268_, lean_object* v_t_1269_, lean_object* v_k_1270_, lean_object* v_fallback_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Std_ExtTreeMap_getEntryGTD___redArg(v_cmp_1268_, v_t_1269_, v_k_1270_, v_fallback_1271_);
lean_dec_ref(v_fallback_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD(lean_object* v_00_u03b1_1273_, lean_object* v_00_u03b2_1274_, lean_object* v_cmp_1275_, lean_object* v_inst_1276_, lean_object* v_t_1277_, lean_object* v_k_1278_, lean_object* v_fallback_1279_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_box(0);
v___x_1281_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1275_, v_k_1278_, v___x_1280_, v_t_1277_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_inc_ref(v_fallback_1279_);
return v_fallback_1279_;
}
else
{
lean_object* v_val_1282_; 
v_val_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_val_1282_);
lean_dec_ref(v___x_1281_);
return v_val_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryGTD___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_00_u03b2_1284_, lean_object* v_cmp_1285_, lean_object* v_inst_1286_, lean_object* v_t_1287_, lean_object* v_k_1288_, lean_object* v_fallback_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Std_ExtTreeMap_getEntryGTD(v_00_u03b1_1283_, v_00_u03b2_1284_, v_cmp_1285_, v_inst_1286_, v_t_1287_, v_k_1288_, v_fallback_1289_);
lean_dec_ref(v_fallback_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg(lean_object* v_cmp_1291_, lean_object* v_t_1292_, lean_object* v_k_1293_, lean_object* v_fallback_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_box(0);
v___x_1296_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1291_, v_k_1293_, v___x_1295_, v_t_1292_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_inc_ref(v_fallback_1294_);
return v_fallback_1294_;
}
else
{
lean_object* v_val_1297_; 
v_val_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_val_1297_);
lean_dec_ref(v___x_1296_);
return v_val_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___redArg___boxed(lean_object* v_cmp_1298_, lean_object* v_t_1299_, lean_object* v_k_1300_, lean_object* v_fallback_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_ExtTreeMap_getEntryLED___redArg(v_cmp_1298_, v_t_1299_, v_k_1300_, v_fallback_1301_);
lean_dec_ref(v_fallback_1301_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED(lean_object* v_00_u03b1_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_cmp_1305_, lean_object* v_inst_1306_, lean_object* v_t_1307_, lean_object* v_k_1308_, lean_object* v_fallback_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_box(0);
v___x_1311_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1305_, v_k_1308_, v___x_1310_, v_t_1307_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_inc_ref(v_fallback_1309_);
return v_fallback_1309_;
}
else
{
lean_object* v_val_1312_; 
v_val_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_val_1312_);
lean_dec_ref(v___x_1311_);
return v_val_1312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLED___boxed(lean_object* v_00_u03b1_1313_, lean_object* v_00_u03b2_1314_, lean_object* v_cmp_1315_, lean_object* v_inst_1316_, lean_object* v_t_1317_, lean_object* v_k_1318_, lean_object* v_fallback_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Std_ExtTreeMap_getEntryLED(v_00_u03b1_1313_, v_00_u03b2_1314_, v_cmp_1315_, v_inst_1316_, v_t_1317_, v_k_1318_, v_fallback_1319_);
lean_dec_ref(v_fallback_1319_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg(lean_object* v_cmp_1321_, lean_object* v_t_1322_, lean_object* v_k_1323_, lean_object* v_fallback_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_box(0);
v___x_1326_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1321_, v_k_1323_, v___x_1325_, v_t_1322_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_inc_ref(v_fallback_1324_);
return v_fallback_1324_;
}
else
{
lean_object* v_val_1327_; 
v_val_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_val_1327_);
lean_dec_ref(v___x_1326_);
return v_val_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___redArg___boxed(lean_object* v_cmp_1328_, lean_object* v_t_1329_, lean_object* v_k_1330_, lean_object* v_fallback_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Std_ExtTreeMap_getEntryLTD___redArg(v_cmp_1328_, v_t_1329_, v_k_1330_, v_fallback_1331_);
lean_dec_ref(v_fallback_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD(lean_object* v_00_u03b1_1333_, lean_object* v_00_u03b2_1334_, lean_object* v_cmp_1335_, lean_object* v_inst_1336_, lean_object* v_t_1337_, lean_object* v_k_1338_, lean_object* v_fallback_1339_){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1335_, v_k_1338_, v___x_1340_, v_t_1337_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_inc_ref(v_fallback_1339_);
return v_fallback_1339_;
}
else
{
lean_object* v_val_1342_; 
v_val_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_val_1342_);
lean_dec_ref(v___x_1341_);
return v_val_1342_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getEntryLTD___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_00_u03b2_1344_, lean_object* v_cmp_1345_, lean_object* v_inst_1346_, lean_object* v_t_1347_, lean_object* v_k_1348_, lean_object* v_fallback_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Std_ExtTreeMap_getEntryLTD(v_00_u03b1_1343_, v_00_u03b2_1344_, v_cmp_1345_, v_inst_1346_, v_t_1347_, v_k_1348_, v_fallback_1349_);
lean_dec_ref(v_fallback_1349_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f___redArg(lean_object* v_cmp_1351_, lean_object* v_t_1352_, lean_object* v_k_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1351_, v_k_1353_, v___x_1354_, v_t_1352_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x3f(lean_object* v_00_u03b1_1356_, lean_object* v_00_u03b2_1357_, lean_object* v_cmp_1358_, lean_object* v_inst_1359_, lean_object* v_t_1360_, lean_object* v_k_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1358_, v_k_1361_, v___x_1362_, v_t_1360_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f___redArg(lean_object* v_cmp_1364_, lean_object* v_t_1365_, lean_object* v_k_1366_){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_box(0);
v___x_1368_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1364_, v_k_1366_, v___x_1367_, v_t_1365_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x3f(lean_object* v_00_u03b1_1369_, lean_object* v_00_u03b2_1370_, lean_object* v_cmp_1371_, lean_object* v_inst_1372_, lean_object* v_t_1373_, lean_object* v_k_1374_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1371_, v_k_1374_, v___x_1375_, v_t_1373_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f___redArg(lean_object* v_cmp_1377_, lean_object* v_t_1378_, lean_object* v_k_1379_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1377_, v_k_1379_, v___x_1380_, v_t_1378_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x3f(lean_object* v_00_u03b1_1382_, lean_object* v_00_u03b2_1383_, lean_object* v_cmp_1384_, lean_object* v_inst_1385_, lean_object* v_t_1386_, lean_object* v_k_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_box(0);
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1384_, v_k_1387_, v___x_1388_, v_t_1386_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f___redArg(lean_object* v_cmp_1390_, lean_object* v_t_1391_, lean_object* v_k_1392_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_box(0);
v___x_1394_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1390_, v_k_1392_, v___x_1393_, v_t_1391_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x3f(lean_object* v_00_u03b1_1395_, lean_object* v_00_u03b2_1396_, lean_object* v_cmp_1397_, lean_object* v_inst_1398_, lean_object* v_t_1399_, lean_object* v_k_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_box(0);
v___x_1402_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1397_, v_k_1400_, v___x_1401_, v_t_1399_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE___redArg(lean_object* v_cmp_1403_, lean_object* v_t_1404_, lean_object* v_k_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1403_, v_k_1405_, v_t_1404_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE(lean_object* v_00_u03b1_1407_, lean_object* v_00_u03b2_1408_, lean_object* v_cmp_1409_, lean_object* v_inst_1410_, lean_object* v_t_1411_, lean_object* v_k_1412_, lean_object* v_h_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1409_, v_k_1412_, v_t_1411_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT___redArg(lean_object* v_cmp_1415_, lean_object* v_t_1416_, lean_object* v_k_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1415_, v_k_1417_, v_t_1416_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT(lean_object* v_00_u03b1_1419_, lean_object* v_00_u03b2_1420_, lean_object* v_cmp_1421_, lean_object* v_inst_1422_, lean_object* v_t_1423_, lean_object* v_k_1424_, lean_object* v_h_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_1421_, v_k_1424_, v_t_1423_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE___redArg(lean_object* v_cmp_1427_, lean_object* v_t_1428_, lean_object* v_k_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1427_, v_k_1429_, v_t_1428_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE(lean_object* v_00_u03b1_1431_, lean_object* v_00_u03b2_1432_, lean_object* v_cmp_1433_, lean_object* v_inst_1434_, lean_object* v_t_1435_, lean_object* v_k_1436_, lean_object* v_h_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_1433_, v_k_1436_, v_t_1435_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT___redArg(lean_object* v_cmp_1439_, lean_object* v_t_1440_, lean_object* v_k_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1439_, v_k_1441_, v_t_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT(lean_object* v_00_u03b1_1443_, lean_object* v_00_u03b2_1444_, lean_object* v_cmp_1445_, lean_object* v_inst_1446_, lean_object* v_t_1447_, lean_object* v_k_1448_, lean_object* v_h_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_1445_, v_k_1448_, v_t_1447_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___redArg(lean_object* v_cmp_1451_, lean_object* v_inst_1452_, lean_object* v_t_1453_, lean_object* v_k_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_box(0);
v___x_1456_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1451_, v_k_1454_, v___x_1455_, v_t_1453_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1458_ = l_panic___redArg(v_inst_1452_, v___x_1457_);
return v___x_1458_;
}
else
{
lean_object* v_val_1459_; 
v_val_1459_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_val_1459_);
lean_dec_ref(v___x_1456_);
return v_val_1459_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1460_, lean_object* v_inst_1461_, lean_object* v_t_1462_, lean_object* v_k_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Std_ExtTreeMap_getKeyGE_x21___redArg(v_cmp_1460_, v_inst_1461_, v_t_1462_, v_k_1463_);
lean_dec(v_inst_1461_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21(lean_object* v_00_u03b1_1465_, lean_object* v_00_u03b2_1466_, lean_object* v_cmp_1467_, lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_t_1470_, lean_object* v_k_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_box(0);
v___x_1473_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1467_, v_k_1471_, v___x_1472_, v_t_1470_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1475_ = l_panic___redArg(v_inst_1469_, v___x_1474_);
return v___x_1475_;
}
else
{
lean_object* v_val_1476_; 
v_val_1476_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_val_1476_);
lean_dec_ref(v___x_1473_);
return v_val_1476_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1477_, lean_object* v_00_u03b2_1478_, lean_object* v_cmp_1479_, lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_t_1482_, lean_object* v_k_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Std_ExtTreeMap_getKeyGE_x21(v_00_u03b1_1477_, v_00_u03b2_1478_, v_cmp_1479_, v_inst_1480_, v_inst_1481_, v_t_1482_, v_k_1483_);
lean_dec(v_inst_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg(lean_object* v_cmp_1485_, lean_object* v_inst_1486_, lean_object* v_t_1487_, lean_object* v_k_1488_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_box(0);
v___x_1490_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1485_, v_k_1488_, v___x_1489_, v_t_1487_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1492_ = l_panic___redArg(v_inst_1486_, v___x_1491_);
return v___x_1492_;
}
else
{
lean_object* v_val_1493_; 
v_val_1493_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_val_1493_);
lean_dec_ref(v___x_1490_);
return v_val_1493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1494_, lean_object* v_inst_1495_, lean_object* v_t_1496_, lean_object* v_k_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Std_ExtTreeMap_getKeyGT_x21___redArg(v_cmp_1494_, v_inst_1495_, v_t_1496_, v_k_1497_);
lean_dec(v_inst_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21(lean_object* v_00_u03b1_1499_, lean_object* v_00_u03b2_1500_, lean_object* v_cmp_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_t_1504_, lean_object* v_k_1505_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_box(0);
v___x_1507_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1501_, v_k_1505_, v___x_1506_, v_t_1504_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1509_ = l_panic___redArg(v_inst_1503_, v___x_1508_);
return v___x_1509_;
}
else
{
lean_object* v_val_1510_; 
v_val_1510_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_val_1510_);
lean_dec_ref(v___x_1507_);
return v_val_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1511_, lean_object* v_00_u03b2_1512_, lean_object* v_cmp_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v_t_1516_, lean_object* v_k_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Std_ExtTreeMap_getKeyGT_x21(v_00_u03b1_1511_, v_00_u03b2_1512_, v_cmp_1513_, v_inst_1514_, v_inst_1515_, v_t_1516_, v_k_1517_);
lean_dec(v_inst_1515_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg(lean_object* v_cmp_1519_, lean_object* v_inst_1520_, lean_object* v_t_1521_, lean_object* v_k_1522_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_box(0);
v___x_1524_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1519_, v_k_1522_, v___x_1523_, v_t_1521_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1526_ = l_panic___redArg(v_inst_1520_, v___x_1525_);
return v___x_1526_;
}
else
{
lean_object* v_val_1527_; 
v_val_1527_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_val_1527_);
lean_dec_ref(v___x_1524_);
return v_val_1527_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1528_, lean_object* v_inst_1529_, lean_object* v_t_1530_, lean_object* v_k_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Std_ExtTreeMap_getKeyLE_x21___redArg(v_cmp_1528_, v_inst_1529_, v_t_1530_, v_k_1531_);
lean_dec(v_inst_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21(lean_object* v_00_u03b1_1533_, lean_object* v_00_u03b2_1534_, lean_object* v_cmp_1535_, lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_t_1538_, lean_object* v_k_1539_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_box(0);
v___x_1541_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1535_, v_k_1539_, v___x_1540_, v_t_1538_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1543_ = l_panic___redArg(v_inst_1537_, v___x_1542_);
return v___x_1543_;
}
else
{
lean_object* v_val_1544_; 
v_val_1544_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_val_1544_);
lean_dec_ref(v___x_1541_);
return v_val_1544_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1545_, lean_object* v_00_u03b2_1546_, lean_object* v_cmp_1547_, lean_object* v_inst_1548_, lean_object* v_inst_1549_, lean_object* v_t_1550_, lean_object* v_k_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Std_ExtTreeMap_getKeyLE_x21(v_00_u03b1_1545_, v_00_u03b2_1546_, v_cmp_1547_, v_inst_1548_, v_inst_1549_, v_t_1550_, v_k_1551_);
lean_dec(v_inst_1549_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg(lean_object* v_cmp_1553_, lean_object* v_inst_1554_, lean_object* v_t_1555_, lean_object* v_k_1556_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_box(0);
v___x_1558_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1553_, v_k_1556_, v___x_1557_, v_t_1555_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1560_ = l_panic___redArg(v_inst_1554_, v___x_1559_);
return v___x_1560_;
}
else
{
lean_object* v_val_1561_; 
v_val_1561_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_val_1561_);
lean_dec_ref(v___x_1558_);
return v_val_1561_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1562_, lean_object* v_inst_1563_, lean_object* v_t_1564_, lean_object* v_k_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Std_ExtTreeMap_getKeyLT_x21___redArg(v_cmp_1562_, v_inst_1563_, v_t_1564_, v_k_1565_);
lean_dec(v_inst_1563_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21(lean_object* v_00_u03b1_1567_, lean_object* v_00_u03b2_1568_, lean_object* v_cmp_1569_, lean_object* v_inst_1570_, lean_object* v_inst_1571_, lean_object* v_t_1572_, lean_object* v_k_1573_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_box(0);
v___x_1575_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1569_, v_k_1573_, v___x_1574_, v_t_1572_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_obj_once(&l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3, &l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3);
v___x_1577_ = l_panic___redArg(v_inst_1571_, v___x_1576_);
return v___x_1577_;
}
else
{
lean_object* v_val_1578_; 
v_val_1578_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_val_1578_);
lean_dec_ref(v___x_1575_);
return v_val_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1579_, lean_object* v_00_u03b2_1580_, lean_object* v_cmp_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_t_1584_, lean_object* v_k_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Std_ExtTreeMap_getKeyLT_x21(v_00_u03b1_1579_, v_00_u03b2_1580_, v_cmp_1581_, v_inst_1582_, v_inst_1583_, v_t_1584_, v_k_1585_);
lean_dec(v_inst_1583_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg(lean_object* v_cmp_1587_, lean_object* v_t_1588_, lean_object* v_k_1589_, lean_object* v_fallback_1590_){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = lean_box(0);
v___x_1592_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1587_, v_k_1589_, v___x_1591_, v_t_1588_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_inc(v_fallback_1590_);
return v_fallback_1590_;
}
else
{
lean_object* v_val_1593_; 
v_val_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_val_1593_);
lean_dec_ref(v___x_1592_);
return v_val_1593_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___redArg___boxed(lean_object* v_cmp_1594_, lean_object* v_t_1595_, lean_object* v_k_1596_, lean_object* v_fallback_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Std_ExtTreeMap_getKeyGED___redArg(v_cmp_1594_, v_t_1595_, v_k_1596_, v_fallback_1597_);
lean_dec(v_fallback_1597_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED(lean_object* v_00_u03b1_1599_, lean_object* v_00_u03b2_1600_, lean_object* v_cmp_1601_, lean_object* v_inst_1602_, lean_object* v_t_1603_, lean_object* v_k_1604_, lean_object* v_fallback_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = lean_box(0);
v___x_1607_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1601_, v_k_1604_, v___x_1606_, v_t_1603_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_inc(v_fallback_1605_);
return v_fallback_1605_;
}
else
{
lean_object* v_val_1608_; 
v_val_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_val_1608_);
lean_dec_ref(v___x_1607_);
return v_val_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGED___boxed(lean_object* v_00_u03b1_1609_, lean_object* v_00_u03b2_1610_, lean_object* v_cmp_1611_, lean_object* v_inst_1612_, lean_object* v_t_1613_, lean_object* v_k_1614_, lean_object* v_fallback_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Std_ExtTreeMap_getKeyGED(v_00_u03b1_1609_, v_00_u03b2_1610_, v_cmp_1611_, v_inst_1612_, v_t_1613_, v_k_1614_, v_fallback_1615_);
lean_dec(v_fallback_1615_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg(lean_object* v_cmp_1617_, lean_object* v_t_1618_, lean_object* v_k_1619_, lean_object* v_fallback_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_box(0);
v___x_1622_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1617_, v_k_1619_, v___x_1621_, v_t_1618_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_inc(v_fallback_1620_);
return v_fallback_1620_;
}
else
{
lean_object* v_val_1623_; 
v_val_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_val_1623_);
lean_dec_ref(v___x_1622_);
return v_val_1623_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___redArg___boxed(lean_object* v_cmp_1624_, lean_object* v_t_1625_, lean_object* v_k_1626_, lean_object* v_fallback_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Std_ExtTreeMap_getKeyGTD___redArg(v_cmp_1624_, v_t_1625_, v_k_1626_, v_fallback_1627_);
lean_dec(v_fallback_1627_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD(lean_object* v_00_u03b1_1629_, lean_object* v_00_u03b2_1630_, lean_object* v_cmp_1631_, lean_object* v_inst_1632_, lean_object* v_t_1633_, lean_object* v_k_1634_, lean_object* v_fallback_1635_){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_box(0);
v___x_1637_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1631_, v_k_1634_, v___x_1636_, v_t_1633_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_inc(v_fallback_1635_);
return v_fallback_1635_;
}
else
{
lean_object* v_val_1638_; 
v_val_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_val_1638_);
lean_dec_ref(v___x_1637_);
return v_val_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyGTD___boxed(lean_object* v_00_u03b1_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_cmp_1641_, lean_object* v_inst_1642_, lean_object* v_t_1643_, lean_object* v_k_1644_, lean_object* v_fallback_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Std_ExtTreeMap_getKeyGTD(v_00_u03b1_1639_, v_00_u03b2_1640_, v_cmp_1641_, v_inst_1642_, v_t_1643_, v_k_1644_, v_fallback_1645_);
lean_dec(v_fallback_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg(lean_object* v_cmp_1647_, lean_object* v_t_1648_, lean_object* v_k_1649_, lean_object* v_fallback_1650_){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_box(0);
v___x_1652_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1647_, v_k_1649_, v___x_1651_, v_t_1648_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_inc(v_fallback_1650_);
return v_fallback_1650_;
}
else
{
lean_object* v_val_1653_; 
v_val_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_val_1653_);
lean_dec_ref(v___x_1652_);
return v_val_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___redArg___boxed(lean_object* v_cmp_1654_, lean_object* v_t_1655_, lean_object* v_k_1656_, lean_object* v_fallback_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Std_ExtTreeMap_getKeyLED___redArg(v_cmp_1654_, v_t_1655_, v_k_1656_, v_fallback_1657_);
lean_dec(v_fallback_1657_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED(lean_object* v_00_u03b1_1659_, lean_object* v_00_u03b2_1660_, lean_object* v_cmp_1661_, lean_object* v_inst_1662_, lean_object* v_t_1663_, lean_object* v_k_1664_, lean_object* v_fallback_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_box(0);
v___x_1667_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1661_, v_k_1664_, v___x_1666_, v_t_1663_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_inc(v_fallback_1665_);
return v_fallback_1665_;
}
else
{
lean_object* v_val_1668_; 
v_val_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_val_1668_);
lean_dec_ref(v___x_1667_);
return v_val_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLED___boxed(lean_object* v_00_u03b1_1669_, lean_object* v_00_u03b2_1670_, lean_object* v_cmp_1671_, lean_object* v_inst_1672_, lean_object* v_t_1673_, lean_object* v_k_1674_, lean_object* v_fallback_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Std_ExtTreeMap_getKeyLED(v_00_u03b1_1669_, v_00_u03b2_1670_, v_cmp_1671_, v_inst_1672_, v_t_1673_, v_k_1674_, v_fallback_1675_);
lean_dec(v_fallback_1675_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg(lean_object* v_cmp_1677_, lean_object* v_t_1678_, lean_object* v_k_1679_, lean_object* v_fallback_1680_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_box(0);
v___x_1682_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1677_, v_k_1679_, v___x_1681_, v_t_1678_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_inc(v_fallback_1680_);
return v_fallback_1680_;
}
else
{
lean_object* v_val_1683_; 
v_val_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_val_1683_);
lean_dec_ref(v___x_1682_);
return v_val_1683_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___redArg___boxed(lean_object* v_cmp_1684_, lean_object* v_t_1685_, lean_object* v_k_1686_, lean_object* v_fallback_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_ExtTreeMap_getKeyLTD___redArg(v_cmp_1684_, v_t_1685_, v_k_1686_, v_fallback_1687_);
lean_dec(v_fallback_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD(lean_object* v_00_u03b1_1689_, lean_object* v_00_u03b2_1690_, lean_object* v_cmp_1691_, lean_object* v_inst_1692_, lean_object* v_t_1693_, lean_object* v_k_1694_, lean_object* v_fallback_1695_){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_box(0);
v___x_1697_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1691_, v_k_1694_, v___x_1696_, v_t_1693_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_inc(v_fallback_1695_);
return v_fallback_1695_;
}
else
{
lean_object* v_val_1698_; 
v_val_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_val_1698_);
lean_dec_ref(v___x_1697_);
return v_val_1698_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_getKeyLTD___boxed(lean_object* v_00_u03b1_1699_, lean_object* v_00_u03b2_1700_, lean_object* v_cmp_1701_, lean_object* v_inst_1702_, lean_object* v_t_1703_, lean_object* v_k_1704_, lean_object* v_fallback_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Std_ExtTreeMap_getKeyLTD(v_00_u03b1_1699_, v_00_u03b2_1700_, v_cmp_1701_, v_inst_1702_, v_t_1703_, v_k_1704_, v_fallback_1705_);
lean_dec(v_fallback_1705_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___redArg(lean_object* v_f_1707_, lean_object* v_m_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_1707_, v_m_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter(lean_object* v_00_u03b1_1710_, lean_object* v_00_u03b2_1711_, lean_object* v_cmp_1712_, lean_object* v_f_1713_, lean_object* v_m_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_1713_, v_m_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filter___boxed(lean_object* v_00_u03b1_1716_, lean_object* v_00_u03b2_1717_, lean_object* v_cmp_1718_, lean_object* v_f_1719_, lean_object* v_m_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Std_ExtTreeMap_filter(v_00_u03b1_1716_, v_00_u03b2_1717_, v_cmp_1718_, v_f_1719_, v_m_1720_);
lean_dec_ref(v_cmp_1718_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___redArg(lean_object* v_f_1722_, lean_object* v_m_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_1722_, v_m_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap(lean_object* v_00_u03b1_1725_, lean_object* v_00_u03b2_1726_, lean_object* v_00_u03b3_1727_, lean_object* v_cmp_1728_, lean_object* v_f_1729_, lean_object* v_m_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_1729_, v_m_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_filterMap___boxed(lean_object* v_00_u03b1_1732_, lean_object* v_00_u03b2_1733_, lean_object* v_00_u03b3_1734_, lean_object* v_cmp_1735_, lean_object* v_f_1736_, lean_object* v_m_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Std_ExtTreeMap_filterMap(v_00_u03b1_1732_, v_00_u03b2_1733_, v_00_u03b3_1734_, v_cmp_1735_, v_f_1736_, v_m_1737_);
lean_dec_ref(v_cmp_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___redArg(lean_object* v_f_1739_, lean_object* v_t_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_1739_, v_t_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map(lean_object* v_00_u03b1_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_00_u03b3_1744_, lean_object* v_cmp_1745_, lean_object* v_f_1746_, lean_object* v_t_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_1746_, v_t_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_map___boxed(lean_object* v_00_u03b1_1749_, lean_object* v_00_u03b2_1750_, lean_object* v_00_u03b3_1751_, lean_object* v_cmp_1752_, lean_object* v_f_1753_, lean_object* v_t_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Std_ExtTreeMap_map(v_00_u03b1_1749_, v_00_u03b2_1750_, v_00_u03b3_1751_, v_cmp_1752_, v_f_1753_, v_t_1754_);
lean_dec_ref(v_cmp_1752_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___redArg(lean_object* v_inst_1756_, lean_object* v_f_1757_, lean_object* v_init_1758_, lean_object* v_t_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1756_, v_f_1757_, v_init_1758_, v_t_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM(lean_object* v_00_u03b1_1761_, lean_object* v_00_u03b2_1762_, lean_object* v_cmp_1763_, lean_object* v_00_u03b4_1764_, lean_object* v_m_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_f_1769_, lean_object* v_init_1770_, lean_object* v_t_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1766_, v_f_1769_, v_init_1770_, v_t_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldlM___boxed(lean_object* v_00_u03b1_1773_, lean_object* v_00_u03b2_1774_, lean_object* v_cmp_1775_, lean_object* v_00_u03b4_1776_, lean_object* v_m_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_f_1781_, lean_object* v_init_1782_, lean_object* v_t_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Std_ExtTreeMap_foldlM(v_00_u03b1_1773_, v_00_u03b2_1774_, v_cmp_1775_, v_00_u03b4_1776_, v_m_1777_, v_inst_1778_, v_inst_1779_, v_inst_1780_, v_f_1781_, v_init_1782_, v_t_1783_);
lean_dec_ref(v_cmp_1775_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___redArg(lean_object* v_f_1785_, lean_object* v_init_1786_, lean_object* v_t_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1785_, v_init_1786_, v_t_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl(lean_object* v_00_u03b1_1789_, lean_object* v_00_u03b2_1790_, lean_object* v_cmp_1791_, lean_object* v_00_u03b4_1792_, lean_object* v_inst_1793_, lean_object* v_f_1794_, lean_object* v_init_1795_, lean_object* v_t_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_1794_, v_init_1795_, v_t_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldl___boxed(lean_object* v_00_u03b1_1798_, lean_object* v_00_u03b2_1799_, lean_object* v_cmp_1800_, lean_object* v_00_u03b4_1801_, lean_object* v_inst_1802_, lean_object* v_f_1803_, lean_object* v_init_1804_, lean_object* v_t_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Std_ExtTreeMap_foldl(v_00_u03b1_1798_, v_00_u03b2_1799_, v_cmp_1800_, v_00_u03b4_1801_, v_inst_1802_, v_f_1803_, v_init_1804_, v_t_1805_);
lean_dec_ref(v_cmp_1800_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___redArg(lean_object* v_inst_1807_, lean_object* v_f_1808_, lean_object* v_init_1809_, lean_object* v_t_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1807_, v_f_1808_, v_init_1809_, v_t_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM(lean_object* v_00_u03b1_1812_, lean_object* v_00_u03b2_1813_, lean_object* v_cmp_1814_, lean_object* v_00_u03b4_1815_, lean_object* v_m_1816_, lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_f_1820_, lean_object* v_init_1821_, lean_object* v_t_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_1817_, v_f_1820_, v_init_1821_, v_t_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldrM___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_cmp_1826_, lean_object* v_00_u03b4_1827_, lean_object* v_m_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_f_1832_, lean_object* v_init_1833_, lean_object* v_t_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Std_ExtTreeMap_foldrM(v_00_u03b1_1824_, v_00_u03b2_1825_, v_cmp_1826_, v_00_u03b4_1827_, v_m_1828_, v_inst_1829_, v_inst_1830_, v_inst_1831_, v_f_1832_, v_init_1833_, v_t_1834_);
lean_dec_ref(v_cmp_1826_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg___lam__0(lean_object* v_f_1836_, lean_object* v_x1_1837_, lean_object* v_x2_1838_, lean_object* v_x3_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_apply_3(v_f_1836_, v_x1_1837_, v_x2_1838_, v_x3_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___redArg(lean_object* v_f_1860_, lean_object* v_init_1861_, lean_object* v_t_1862_){
_start:
{
lean_object* v___f_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___f_1863_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1863_, 0, v_f_1860_);
v___x_1864_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_1865_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1864_, v___f_1863_, v_init_1861_, v_t_1862_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr(lean_object* v_00_u03b1_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_cmp_1868_, lean_object* v_00_u03b4_1869_, lean_object* v_inst_1870_, lean_object* v_f_1871_, lean_object* v_init_1872_, lean_object* v_t_1873_){
_start:
{
lean_object* v___f_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___f_1874_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1874_, 0, v_f_1871_);
v___x_1875_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_1876_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1875_, v___f_1874_, v_init_1872_, v_t_1873_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_foldr___boxed(lean_object* v_00_u03b1_1877_, lean_object* v_00_u03b2_1878_, lean_object* v_cmp_1879_, lean_object* v_00_u03b4_1880_, lean_object* v_inst_1881_, lean_object* v_f_1882_, lean_object* v_init_1883_, lean_object* v_t_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Std_ExtTreeMap_foldr(v_00_u03b1_1877_, v_00_u03b2_1878_, v_cmp_1879_, v_00_u03b4_1880_, v_inst_1881_, v_f_1882_, v_init_1883_, v_t_1884_);
lean_dec_ref(v_cmp_1879_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg___lam__0(lean_object* v_f_1886_, lean_object* v_cmp_1887_, lean_object* v_x_1888_, lean_object* v_a_1889_, lean_object* v_b_1890_){
_start:
{
lean_object* v_fst_1891_; lean_object* v_snd_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1906_; 
v_fst_1891_ = lean_ctor_get(v_x_1888_, 0);
v_snd_1892_ = lean_ctor_get(v_x_1888_, 1);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_x_1888_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1894_ = v_x_1888_;
v_isShared_1895_ = v_isSharedCheck_1906_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_snd_1892_);
lean_inc(v_fst_1891_);
lean_dec(v_x_1888_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1906_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
lean_inc(v_b_1890_);
lean_inc(v_a_1889_);
v___x_1896_ = lean_apply_2(v_f_1886_, v_a_1889_, v_b_1890_);
v___x_1897_ = lean_unbox(v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1887_, v_a_1889_, v_b_1890_, v_snd_1892_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v___x_1898_);
v___x_1900_ = v___x_1894_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_fst_1891_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1902_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_1887_, v_a_1889_, v_b_1890_, v_fst_1891_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1902_);
v___x_1904_ = v___x_1894_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_snd_1892_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition___redArg(lean_object* v_cmp_1909_, lean_object* v_f_1910_, lean_object* v_t_1911_){
_start:
{
lean_object* v___f_1912_; lean_object* v___x_1913_; lean_object* v_p_1914_; lean_object* v_fst_1915_; lean_object* v_snd_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
v___f_1912_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1912_, 0, v_f_1910_);
lean_closure_set(v___f_1912_, 1, v_cmp_1909_);
v___x_1913_ = ((lean_object*)(l_Std_ExtTreeMap_partition___redArg___closed__0));
v_p_1914_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1912_, v___x_1913_, v_t_1911_);
v_fst_1915_ = lean_ctor_get(v_p_1914_, 0);
v_snd_1916_ = lean_ctor_get(v_p_1914_, 1);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_p_1914_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v_p_1914_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_snd_1916_);
lean_inc(v_fst_1915_);
lean_dec(v_p_1914_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_fst_1915_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_snd_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_partition(lean_object* v_00_u03b1_1924_, lean_object* v_00_u03b2_1925_, lean_object* v_cmp_1926_, lean_object* v_inst_1927_, lean_object* v_f_1928_, lean_object* v_t_1929_){
_start:
{
lean_object* v___f_1930_; lean_object* v___x_1931_; lean_object* v_p_1932_; lean_object* v_fst_1933_; lean_object* v_snd_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v___f_1930_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1930_, 0, v_f_1928_);
lean_closure_set(v___f_1930_, 1, v_cmp_1926_);
v___x_1931_ = ((lean_object*)(l_Std_ExtTreeMap_partition___redArg___closed__0));
v_p_1932_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1930_, v___x_1931_, v_t_1929_);
v_fst_1933_ = lean_ctor_get(v_p_1932_, 0);
v_snd_1934_ = lean_ctor_get(v_p_1932_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_p_1932_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v_p_1932_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_snd_1934_);
lean_inc(v_fst_1933_);
lean_dec(v_p_1932_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_fst_1933_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_snd_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg___lam__0(lean_object* v_f_1942_, lean_object* v_x_1943_, lean_object* v_k_1944_, lean_object* v_v_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_apply_2(v_f_1942_, v_k_1944_, v_v_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___redArg(lean_object* v_inst_1947_, lean_object* v_f_1948_, lean_object* v_t_1949_){
_start:
{
lean_object* v___f_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___f_1950_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1950_, 0, v_f_1948_);
v___x_1951_ = lean_box(0);
v___x_1952_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1947_, v___f_1950_, v___x_1951_, v_t_1949_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM(lean_object* v_00_u03b1_1953_, lean_object* v_00_u03b2_1954_, lean_object* v_cmp_1955_, lean_object* v_m_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_f_1960_, lean_object* v_t_1961_){
_start:
{
lean_object* v___f_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___f_1962_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1962_, 0, v_f_1960_);
v___x_1963_ = lean_box(0);
v___x_1964_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_1957_, v___f_1962_, v___x_1963_, v_t_1961_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forM___boxed(lean_object* v_00_u03b1_1965_, lean_object* v_00_u03b2_1966_, lean_object* v_cmp_1967_, lean_object* v_m_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_f_1972_, lean_object* v_t_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Std_ExtTreeMap_forM(v_00_u03b1_1965_, v_00_u03b2_1966_, v_cmp_1967_, v_m_1968_, v_inst_1969_, v_inst_1970_, v_inst_1971_, v_f_1972_, v_t_1973_);
lean_dec_ref(v_cmp_1967_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__0(lean_object* v_f_1975_, lean_object* v_a_1976_, lean_object* v_b_1977_, lean_object* v_c_1978_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_apply_3(v_f_1975_, v_a_1976_, v_b_1977_, v_c_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg___lam__1(lean_object* v_toPure_1980_, lean_object* v_____do__lift_1981_){
_start:
{
lean_object* v_a_1982_; lean_object* v___x_1983_; 
v_a_1982_ = lean_ctor_get(v_____do__lift_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref(v_____do__lift_1981_);
v___x_1983_ = lean_apply_2(v_toPure_1980_, lean_box(0), v_a_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___redArg(lean_object* v_inst_1984_, lean_object* v_f_1985_, lean_object* v_init_1986_, lean_object* v_t_1987_){
_start:
{
lean_object* v_toApplicative_1988_; lean_object* v_toBind_1989_; lean_object* v_toPure_1990_; lean_object* v___f_1991_; lean_object* v___x_1992_; lean_object* v___f_1993_; lean_object* v___x_1994_; 
v_toApplicative_1988_ = lean_ctor_get(v_inst_1984_, 0);
v_toBind_1989_ = lean_ctor_get(v_inst_1984_, 1);
lean_inc(v_toBind_1989_);
v_toPure_1990_ = lean_ctor_get(v_toApplicative_1988_, 1);
lean_inc(v_toPure_1990_);
v___f_1991_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1991_, 0, v_f_1985_);
v___x_1992_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1984_, v___f_1991_, v_init_1986_, v_t_1987_);
v___f_1993_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1993_, 0, v_toPure_1990_);
v___x_1994_ = lean_apply_4(v_toBind_1989_, lean_box(0), lean_box(0), v___x_1992_, v___f_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn(lean_object* v_00_u03b1_1995_, lean_object* v_00_u03b2_1996_, lean_object* v_cmp_1997_, lean_object* v_00_u03b4_1998_, lean_object* v_m_1999_, lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_f_2003_, lean_object* v_init_2004_, lean_object* v_t_2005_){
_start:
{
lean_object* v_toApplicative_2006_; lean_object* v_toBind_2007_; lean_object* v_toPure_2008_; lean_object* v___f_2009_; lean_object* v___x_2010_; lean_object* v___f_2011_; lean_object* v___x_2012_; 
v_toApplicative_2006_ = lean_ctor_get(v_inst_2000_, 0);
v_toBind_2007_ = lean_ctor_get(v_inst_2000_, 1);
lean_inc(v_toBind_2007_);
v_toPure_2008_ = lean_ctor_get(v_toApplicative_2006_, 1);
lean_inc(v_toPure_2008_);
v___f_2009_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2009_, 0, v_f_2003_);
v___x_2010_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2000_, v___f_2009_, v_init_2004_, v_t_2005_);
v___f_2011_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2011_, 0, v_toPure_2008_);
v___x_2012_ = lean_apply_4(v_toBind_2007_, lean_box(0), lean_box(0), v___x_2010_, v___f_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_forIn___boxed(lean_object* v_00_u03b1_2013_, lean_object* v_00_u03b2_2014_, lean_object* v_cmp_2015_, lean_object* v_00_u03b4_2016_, lean_object* v_m_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_inst_2020_, lean_object* v_f_2021_, lean_object* v_init_2022_, lean_object* v_t_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Std_ExtTreeMap_forIn(v_00_u03b1_2013_, v_00_u03b2_2014_, v_cmp_2015_, v_00_u03b4_2016_, v_m_2017_, v_inst_2018_, v_inst_2019_, v_inst_2020_, v_f_2021_, v_init_2022_, v_t_2023_);
lean_dec_ref(v_cmp_2015_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2025_, lean_object* v_x_2026_, lean_object* v_k_2027_, lean_object* v_v_2028_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_k_2027_);
lean_ctor_set(v___x_2029_, 1, v_v_2028_);
v___x_2030_ = lean_apply_1(v_f_2025_, v___x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1(lean_object* v_inst_2031_, lean_object* v_t_2032_, lean_object* v_f_2033_){
_start:
{
lean_object* v___f_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___f_2034_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2034_, 0, v_f_2033_);
v___x_2035_ = lean_box(0);
v___x_2036_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2031_, v___f_2034_, v___x_2035_, v_t_2032_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2037_){
_start:
{
lean_object* v___f_2038_; 
v___f_2038_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2038_, 0, v_inst_2037_);
return v___f_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2039_, lean_object* v_00_u03b2_2040_, lean_object* v_cmp_2041_, lean_object* v_m_2042_, lean_object* v_inst_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_){
_start:
{
lean_object* v___f_2046_; 
v___f_2046_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2046_, 0, v_inst_2044_);
return v___f_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2047_, lean_object* v_00_u03b2_2048_, lean_object* v_cmp_2049_, lean_object* v_m_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(v_00_u03b1_2047_, v_00_u03b2_2048_, v_cmp_2049_, v_m_2050_, v_inst_2051_, v_inst_2052_, v_inst_2053_);
lean_dec_ref(v_cmp_2049_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0(lean_object* v_f_2055_, lean_object* v_a_2056_, lean_object* v_b_2057_, lean_object* v_c_2058_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v_a_2056_);
lean_ctor_set(v___x_2059_, 1, v_b_2057_);
v___x_2060_ = lean_apply_2(v_f_2055_, v___x_2059_, v_c_2058_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2(lean_object* v_inst_2061_, lean_object* v_00_u03b2_2062_, lean_object* v_m_2063_, lean_object* v_init_2064_, lean_object* v_f_2065_){
_start:
{
lean_object* v_toApplicative_2066_; lean_object* v_toBind_2067_; lean_object* v_toPure_2068_; lean_object* v___f_2069_; lean_object* v___x_2070_; lean_object* v___f_2071_; lean_object* v___x_2072_; 
v_toApplicative_2066_ = lean_ctor_get(v_inst_2061_, 0);
v_toBind_2067_ = lean_ctor_get(v_inst_2061_, 1);
lean_inc(v_toBind_2067_);
v_toPure_2068_ = lean_ctor_get(v_toApplicative_2066_, 1);
lean_inc(v_toPure_2068_);
v___f_2069_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2069_, 0, v_f_2065_);
v___x_2070_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2061_, v___f_2069_, v_init_2064_, v_m_2063_);
v___f_2071_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2071_, 0, v_toPure_2068_);
v___x_2072_ = lean_apply_4(v_toBind_2067_, lean_box(0), lean_box(0), v___x_2070_, v___f_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg(lean_object* v_inst_2073_){
_start:
{
lean_object* v___f_2074_; 
v___f_2074_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2074_, 0, v_inst_2073_);
return v___f_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(lean_object* v_00_u03b1_2075_, lean_object* v_00_u03b2_2076_, lean_object* v_cmp_2077_, lean_object* v_m_2078_, lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_){
_start:
{
lean_object* v___f_2082_; 
v___f_2082_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2082_, 0, v_inst_2080_);
return v___f_2082_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___boxed(lean_object* v_00_u03b1_2083_, lean_object* v_00_u03b2_2084_, lean_object* v_cmp_2085_, lean_object* v_m_2086_, lean_object* v_inst_2087_, lean_object* v_inst_2088_, lean_object* v_inst_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(v_00_u03b1_2083_, v_00_u03b2_2084_, v_cmp_2085_, v_m_2086_, v_inst_2087_, v_inst_2088_, v_inst_2089_);
lean_dec_ref(v_cmp_2085_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0(lean_object* v_p_2091_, lean_object* v___x_2092_, lean_object* v___x_2093_, lean_object* v_a_2094_, lean_object* v_b_2095_, lean_object* v_acc_2096_){
_start:
{
lean_object* v___x_2097_; uint8_t v___x_2098_; 
v___x_2097_ = lean_apply_2(v_p_2091_, v_a_2094_, v_b_2095_);
v___x_2098_ = lean_unbox(v___x_2097_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; 
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2092_);
return v___x_2099_;
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_dec_ref(v___x_2092_);
v___x_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2097_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2093_);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___lam__0___boxed(lean_object* v_p_2103_, lean_object* v___x_2104_, lean_object* v___x_2105_, lean_object* v_a_2106_, lean_object* v_b_2107_, lean_object* v_acc_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Std_ExtTreeMap_any___redArg___lam__0(v_p_2103_, v___x_2104_, v___x_2105_, v_a_2106_, v_b_2107_, v_acc_2108_);
lean_dec_ref(v_acc_2108_);
return v_res_2109_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_any___redArg(lean_object* v_t_2113_, lean_object* v_p_2114_){
_start:
{
lean_object* v___y_2116_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v_a_2126_; 
v___x_2121_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2122_ = lean_box(0);
v___x_2123_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2124_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2124_, 0, v_p_2114_);
lean_closure_set(v___f_2124_, 1, v___x_2123_);
lean_closure_set(v___f_2124_, 2, v___x_2122_);
v___x_2125_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2121_, v___f_2124_, v___x_2123_, v_t_2113_);
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___y_2116_ = v_a_2126_;
goto v___jp_2115_;
v___jp_2115_:
{
lean_object* v_fst_2117_; 
v_fst_2117_ = lean_ctor_get(v___y_2116_, 0);
lean_inc(v_fst_2117_);
lean_dec_ref(v___y_2116_);
if (lean_obj_tag(v_fst_2117_) == 0)
{
uint8_t v___x_2118_; 
v___x_2118_ = 0;
return v___x_2118_;
}
else
{
lean_object* v_val_2119_; uint8_t v___x_2120_; 
v_val_2119_ = lean_ctor_get(v_fst_2117_, 0);
lean_inc(v_val_2119_);
lean_dec_ref(v_fst_2117_);
v___x_2120_ = lean_unbox(v_val_2119_);
lean_dec(v_val_2119_);
return v___x_2120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___redArg___boxed(lean_object* v_t_2127_, lean_object* v_p_2128_){
_start:
{
uint8_t v_res_2129_; lean_object* v_r_2130_; 
v_res_2129_ = l_Std_ExtTreeMap_any___redArg(v_t_2127_, v_p_2128_);
v_r_2130_ = lean_box(v_res_2129_);
return v_r_2130_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_any(lean_object* v_00_u03b1_2131_, lean_object* v_00_u03b2_2132_, lean_object* v_cmp_2133_, lean_object* v_inst_2134_, lean_object* v_t_2135_, lean_object* v_p_2136_){
_start:
{
lean_object* v___y_2138_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; lean_object* v___x_2147_; lean_object* v_a_2148_; 
v___x_2143_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2144_ = lean_box(0);
v___x_2145_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2146_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2146_, 0, v_p_2136_);
lean_closure_set(v___f_2146_, 1, v___x_2145_);
lean_closure_set(v___f_2146_, 2, v___x_2144_);
v___x_2147_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2143_, v___f_2146_, v___x_2145_, v_t_2135_);
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec(v___x_2147_);
v___y_2138_ = v_a_2148_;
goto v___jp_2137_;
v___jp_2137_:
{
lean_object* v_fst_2139_; 
v_fst_2139_ = lean_ctor_get(v___y_2138_, 0);
lean_inc(v_fst_2139_);
lean_dec_ref(v___y_2138_);
if (lean_obj_tag(v_fst_2139_) == 0)
{
uint8_t v___x_2140_; 
v___x_2140_ = 0;
return v___x_2140_;
}
else
{
lean_object* v_val_2141_; uint8_t v___x_2142_; 
v_val_2141_ = lean_ctor_get(v_fst_2139_, 0);
lean_inc(v_val_2141_);
lean_dec_ref(v_fst_2139_);
v___x_2142_ = lean_unbox(v_val_2141_);
lean_dec(v_val_2141_);
return v___x_2142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_any___boxed(lean_object* v_00_u03b1_2149_, lean_object* v_00_u03b2_2150_, lean_object* v_cmp_2151_, lean_object* v_inst_2152_, lean_object* v_t_2153_, lean_object* v_p_2154_){
_start:
{
uint8_t v_res_2155_; lean_object* v_r_2156_; 
v_res_2155_ = l_Std_ExtTreeMap_any(v_00_u03b1_2149_, v_00_u03b2_2150_, v_cmp_2151_, v_inst_2152_, v_t_2153_, v_p_2154_);
lean_dec_ref(v_cmp_2151_);
v_r_2156_ = lean_box(v_res_2155_);
return v_r_2156_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0(lean_object* v_p_2157_, lean_object* v___x_2158_, lean_object* v___x_2159_, lean_object* v_a_2160_, lean_object* v_b_2161_, lean_object* v_acc_2162_){
_start:
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = lean_apply_2(v_p_2157_, v_a_2160_, v_b_2161_);
v___x_2164_ = lean_unbox(v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_dec_ref(v___x_2159_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___x_2158_);
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2159_);
return v___x_2168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___lam__0___boxed(lean_object* v_p_2169_, lean_object* v___x_2170_, lean_object* v___x_2171_, lean_object* v_a_2172_, lean_object* v_b_2173_, lean_object* v_acc_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Std_ExtTreeMap_all___redArg___lam__0(v_p_2169_, v___x_2170_, v___x_2171_, v_a_2172_, v_b_2173_, v_acc_2174_);
lean_dec_ref(v_acc_2174_);
return v_res_2175_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_all___redArg(lean_object* v_t_2176_, lean_object* v_p_2177_){
_start:
{
lean_object* v___y_2179_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___f_2187_; lean_object* v___x_2188_; lean_object* v_a_2189_; 
v___x_2184_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2185_ = lean_box(0);
v___x_2186_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2187_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2187_, 0, v_p_2177_);
lean_closure_set(v___f_2187_, 1, v___x_2185_);
lean_closure_set(v___f_2187_, 2, v___x_2186_);
v___x_2188_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2184_, v___f_2187_, v___x_2186_, v_t_2176_);
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec(v___x_2188_);
v___y_2179_ = v_a_2189_;
goto v___jp_2178_;
v___jp_2178_:
{
lean_object* v_fst_2180_; 
v_fst_2180_ = lean_ctor_get(v___y_2179_, 0);
lean_inc(v_fst_2180_);
lean_dec_ref(v___y_2179_);
if (lean_obj_tag(v_fst_2180_) == 0)
{
uint8_t v___x_2181_; 
v___x_2181_ = 1;
return v___x_2181_;
}
else
{
lean_object* v_val_2182_; uint8_t v___x_2183_; 
v_val_2182_ = lean_ctor_get(v_fst_2180_, 0);
lean_inc(v_val_2182_);
lean_dec_ref(v_fst_2180_);
v___x_2183_ = lean_unbox(v_val_2182_);
lean_dec(v_val_2182_);
return v___x_2183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___redArg___boxed(lean_object* v_t_2190_, lean_object* v_p_2191_){
_start:
{
uint8_t v_res_2192_; lean_object* v_r_2193_; 
v_res_2192_ = l_Std_ExtTreeMap_all___redArg(v_t_2190_, v_p_2191_);
v_r_2193_ = lean_box(v_res_2192_);
return v_r_2193_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_all(lean_object* v_00_u03b1_2194_, lean_object* v_00_u03b2_2195_, lean_object* v_cmp_2196_, lean_object* v_inst_2197_, lean_object* v_t_2198_, lean_object* v_p_2199_){
_start:
{
lean_object* v___y_2201_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v_a_2211_; 
v___x_2206_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2207_ = lean_box(0);
v___x_2208_ = ((lean_object*)(l_Std_ExtTreeMap_any___redArg___closed__0));
v___f_2209_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2209_, 0, v_p_2199_);
lean_closure_set(v___f_2209_, 1, v___x_2207_);
lean_closure_set(v___f_2209_, 2, v___x_2208_);
v___x_2210_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2206_, v___f_2209_, v___x_2208_, v_t_2198_);
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___y_2201_ = v_a_2211_;
goto v___jp_2200_;
v___jp_2200_:
{
lean_object* v_fst_2202_; 
v_fst_2202_ = lean_ctor_get(v___y_2201_, 0);
lean_inc(v_fst_2202_);
lean_dec_ref(v___y_2201_);
if (lean_obj_tag(v_fst_2202_) == 0)
{
uint8_t v___x_2203_; 
v___x_2203_ = 1;
return v___x_2203_;
}
else
{
lean_object* v_val_2204_; uint8_t v___x_2205_; 
v_val_2204_ = lean_ctor_get(v_fst_2202_, 0);
lean_inc(v_val_2204_);
lean_dec_ref(v_fst_2202_);
v___x_2205_ = lean_unbox(v_val_2204_);
lean_dec(v_val_2204_);
return v___x_2205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_all___boxed(lean_object* v_00_u03b1_2212_, lean_object* v_00_u03b2_2213_, lean_object* v_cmp_2214_, lean_object* v_inst_2215_, lean_object* v_t_2216_, lean_object* v_p_2217_){
_start:
{
uint8_t v_res_2218_; lean_object* v_r_2219_; 
v_res_2218_ = l_Std_ExtTreeMap_all(v_00_u03b1_2212_, v_00_u03b2_2213_, v_cmp_2214_, v_inst_2215_, v_t_2216_, v_p_2217_);
lean_dec_ref(v_cmp_2214_);
v_r_2219_ = lean_box(v_res_2218_);
return v_r_2219_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0(lean_object* v_x1_2220_, lean_object* v_x2_2221_, lean_object* v_x3_2222_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2223_, 0, v_x1_2220_);
lean_ctor_set(v___x_2223_, 1, v_x3_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg___lam__0___boxed(lean_object* v_x1_2224_, lean_object* v_x2_2225_, lean_object* v_x3_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Std_ExtTreeMap_keys___redArg___lam__0(v_x1_2224_, v_x2_2225_, v_x3_2226_);
lean_dec(v_x2_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___redArg(lean_object* v_t_2229_){
_start:
{
lean_object* v___f_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___f_2230_ = ((lean_object*)(l_Std_ExtTreeMap_keys___redArg___closed__0));
v___x_2231_ = lean_box(0);
v___x_2232_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2233_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2232_, v___f_2230_, v___x_2231_, v_t_2229_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys(lean_object* v_00_u03b1_2234_, lean_object* v_00_u03b2_2235_, lean_object* v_cmp_2236_, lean_object* v_inst_2237_, lean_object* v_t_2238_){
_start:
{
lean_object* v___f_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___f_2239_ = ((lean_object*)(l_Std_ExtTreeMap_keys___redArg___closed__0));
v___x_2240_ = lean_box(0);
v___x_2241_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2242_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2241_, v___f_2239_, v___x_2240_, v_t_2238_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keys___boxed(lean_object* v_00_u03b1_2243_, lean_object* v_00_u03b2_2244_, lean_object* v_cmp_2245_, lean_object* v_inst_2246_, lean_object* v_t_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Std_ExtTreeMap_keys(v_00_u03b1_2243_, v_00_u03b2_2244_, v_cmp_2245_, v_inst_2246_, v_t_2247_);
lean_dec_ref(v_cmp_2245_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0(lean_object* v_l_2249_, lean_object* v_k_2250_, lean_object* v_x_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_array_push(v_l_2249_, v_k_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg___lam__0___boxed(lean_object* v_l_2253_, lean_object* v_k_2254_, lean_object* v_x_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Std_ExtTreeMap_keysArray___redArg___lam__0(v_l_2253_, v_k_2254_, v_x_2255_);
lean_dec(v_x_2255_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___redArg(lean_object* v_t_2258_){
_start:
{
lean_object* v___f_2259_; lean_object* v___y_2261_; 
v___f_2259_ = ((lean_object*)(l_Std_ExtTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2258_) == 0)
{
lean_object* v_size_2264_; 
v_size_2264_ = lean_ctor_get(v_t_2258_, 0);
lean_inc(v_size_2264_);
v___y_2261_ = v_size_2264_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_unsigned_to_nat(0u);
v___y_2261_ = v___x_2265_;
goto v___jp_2260_;
}
v___jp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_mk_empty_array_with_capacity(v___y_2261_);
lean_dec(v___y_2261_);
v___x_2263_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2259_, v___x_2262_, v_t_2258_);
return v___x_2263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray(lean_object* v_00_u03b1_2266_, lean_object* v_00_u03b2_2267_, lean_object* v_cmp_2268_, lean_object* v_inst_2269_, lean_object* v_t_2270_){
_start:
{
lean_object* v___f_2271_; lean_object* v___y_2273_; 
v___f_2271_ = ((lean_object*)(l_Std_ExtTreeMap_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2270_) == 0)
{
lean_object* v_size_2276_; 
v_size_2276_ = lean_ctor_get(v_t_2270_, 0);
lean_inc(v_size_2276_);
v___y_2273_ = v_size_2276_;
goto v___jp_2272_;
}
else
{
lean_object* v___x_2277_; 
v___x_2277_ = lean_unsigned_to_nat(0u);
v___y_2273_ = v___x_2277_;
goto v___jp_2272_;
}
v___jp_2272_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_mk_empty_array_with_capacity(v___y_2273_);
lean_dec(v___y_2273_);
v___x_2275_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2271_, v___x_2274_, v_t_2270_);
return v___x_2275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_keysArray___boxed(lean_object* v_00_u03b1_2278_, lean_object* v_00_u03b2_2279_, lean_object* v_cmp_2280_, lean_object* v_inst_2281_, lean_object* v_t_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Std_ExtTreeMap_keysArray(v_00_u03b1_2278_, v_00_u03b2_2279_, v_cmp_2280_, v_inst_2281_, v_t_2282_);
lean_dec_ref(v_cmp_2280_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0(lean_object* v_x1_2284_, lean_object* v_x2_2285_, lean_object* v_x3_2286_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_x2_2285_);
lean_ctor_set(v___x_2287_, 1, v_x3_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg___lam__0___boxed(lean_object* v_x1_2288_, lean_object* v_x2_2289_, lean_object* v_x3_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Std_ExtTreeMap_values___redArg___lam__0(v_x1_2288_, v_x2_2289_, v_x3_2290_);
lean_dec(v_x1_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___redArg(lean_object* v_t_2293_){
_start:
{
lean_object* v___f_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___f_2294_ = ((lean_object*)(l_Std_ExtTreeMap_values___redArg___closed__0));
v___x_2295_ = lean_box(0);
v___x_2296_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2297_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2296_, v___f_2294_, v___x_2295_, v_t_2293_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values(lean_object* v_00_u03b1_2298_, lean_object* v_00_u03b2_2299_, lean_object* v_cmp_2300_, lean_object* v_inst_2301_, lean_object* v_t_2302_){
_start:
{
lean_object* v___f_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___f_2303_ = ((lean_object*)(l_Std_ExtTreeMap_values___redArg___closed__0));
v___x_2304_ = lean_box(0);
v___x_2305_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2306_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2305_, v___f_2303_, v___x_2304_, v_t_2302_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_values___boxed(lean_object* v_00_u03b1_2307_, lean_object* v_00_u03b2_2308_, lean_object* v_cmp_2309_, lean_object* v_inst_2310_, lean_object* v_t_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Std_ExtTreeMap_values(v_00_u03b1_2307_, v_00_u03b2_2308_, v_cmp_2309_, v_inst_2310_, v_t_2311_);
lean_dec_ref(v_cmp_2309_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0(lean_object* v_l_2313_, lean_object* v_x_2314_, lean_object* v_v_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_array_push(v_l_2313_, v_v_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2317_, lean_object* v_x_2318_, lean_object* v_v_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Std_ExtTreeMap_valuesArray___redArg___lam__0(v_l_2317_, v_x_2318_, v_v_2319_);
lean_dec(v_x_2318_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___redArg(lean_object* v_t_2322_){
_start:
{
lean_object* v___f_2323_; lean_object* v___y_2325_; 
v___f_2323_ = ((lean_object*)(l_Std_ExtTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2322_) == 0)
{
lean_object* v_size_2328_; 
v_size_2328_ = lean_ctor_get(v_t_2322_, 0);
lean_inc(v_size_2328_);
v___y_2325_ = v_size_2328_;
goto v___jp_2324_;
}
else
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_unsigned_to_nat(0u);
v___y_2325_ = v___x_2329_;
goto v___jp_2324_;
}
v___jp_2324_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_mk_empty_array_with_capacity(v___y_2325_);
lean_dec(v___y_2325_);
v___x_2327_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2323_, v___x_2326_, v_t_2322_);
return v___x_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray(lean_object* v_00_u03b1_2330_, lean_object* v_00_u03b2_2331_, lean_object* v_cmp_2332_, lean_object* v_inst_2333_, lean_object* v_t_2334_){
_start:
{
lean_object* v___f_2335_; lean_object* v___y_2337_; 
v___f_2335_ = ((lean_object*)(l_Std_ExtTreeMap_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2334_) == 0)
{
lean_object* v_size_2340_; 
v_size_2340_ = lean_ctor_get(v_t_2334_, 0);
lean_inc(v_size_2340_);
v___y_2337_ = v_size_2340_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_unsigned_to_nat(0u);
v___y_2337_ = v___x_2341_;
goto v___jp_2336_;
}
v___jp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_mk_empty_array_with_capacity(v___y_2337_);
lean_dec(v___y_2337_);
v___x_2339_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2335_, v___x_2338_, v_t_2334_);
return v___x_2339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_valuesArray___boxed(lean_object* v_00_u03b1_2342_, lean_object* v_00_u03b2_2343_, lean_object* v_cmp_2344_, lean_object* v_inst_2345_, lean_object* v_t_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Std_ExtTreeMap_valuesArray(v_00_u03b1_2342_, v_00_u03b2_2343_, v_cmp_2344_, v_inst_2345_, v_t_2346_);
lean_dec_ref(v_cmp_2344_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg___lam__0(lean_object* v_x1_2348_, lean_object* v_x2_2349_, lean_object* v_x3_2350_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2351_, 0, v_x1_2348_);
lean_ctor_set(v___x_2351_, 1, v_x2_2349_);
v___x_2352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set(v___x_2352_, 1, v_x3_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___redArg(lean_object* v_t_2354_){
_start:
{
lean_object* v___f_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___f_2355_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___x_2356_ = lean_box(0);
v___x_2357_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2358_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2357_, v___f_2355_, v___x_2356_, v_t_2354_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList(lean_object* v_00_u03b1_2359_, lean_object* v_00_u03b2_2360_, lean_object* v_cmp_2361_, lean_object* v_inst_2362_, lean_object* v_t_2363_){
_start:
{
lean_object* v___f_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___f_2364_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___x_2365_ = lean_box(0);
v___x_2366_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2367_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2366_, v___f_2364_, v___x_2365_, v_t_2363_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toList___boxed(lean_object* v_00_u03b1_2368_, lean_object* v_00_u03b2_2369_, lean_object* v_cmp_2370_, lean_object* v_inst_2371_, lean_object* v_t_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Std_ExtTreeMap_toList(v_00_u03b1_2368_, v_00_u03b2_2369_, v_cmp_2370_, v_inst_2371_, v_t_2372_);
lean_dec_ref(v_cmp_2370_);
return v_res_2373_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_ofList___auto__1(void){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg___lam__0(lean_object* v_cmp_2375_, lean_object* v_a_2376_, lean_object* v_x_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_fst_2379_; lean_object* v_snd_2380_; lean_object* v_r_2381_; lean_object* v___x_2382_; 
v_fst_2379_ = lean_ctor_get(v_a_2376_, 0);
lean_inc(v_fst_2379_);
v_snd_2380_ = lean_ctor_get(v_a_2376_, 1);
lean_inc(v_snd_2380_);
lean_dec_ref(v_a_2376_);
v_r_2381_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2375_, v_fst_2379_, v_snd_2380_, v___y_2378_);
v___x_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2382_, 0, v_r_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg(lean_object* v_l_2383_, lean_object* v_cmp_2384_){
_start:
{
lean_object* v___f_2385_; lean_object* v___x_2386_; lean_object* v_r_2387_; lean_object* v___x_2388_; 
v___f_2385_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2385_, 0, v_cmp_2384_);
v___x_2386_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2387_ = lean_box(1);
v___x_2388_ = l_List_forIn_x27_loop___redArg(v___x_2386_, v___f_2385_, v_l_2383_, v_r_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___redArg___boxed(lean_object* v_l_2389_, lean_object* v_cmp_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Std_ExtTreeMap_ofList___redArg(v_l_2389_, v_cmp_2390_);
lean_dec(v_l_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList(lean_object* v_00_u03b1_2392_, lean_object* v_00_u03b2_2393_, lean_object* v_l_2394_, lean_object* v_cmp_2395_){
_start:
{
lean_object* v___f_2396_; lean_object* v___x_2397_; lean_object* v_r_2398_; lean_object* v___x_2399_; 
v___f_2396_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2396_, 0, v_cmp_2395_);
v___x_2397_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2398_ = lean_box(1);
v___x_2399_ = l_List_forIn_x27_loop___redArg(v___x_2397_, v___f_2396_, v_l_2394_, v_r_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofList___boxed(lean_object* v_00_u03b1_2400_, lean_object* v_00_u03b2_2401_, lean_object* v_l_2402_, lean_object* v_cmp_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Std_ExtTreeMap_ofList(v_00_u03b1_2400_, v_00_u03b2_2401_, v_l_2402_, v_cmp_2403_);
lean_dec(v_l_2402_);
return v_res_2404_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___lam__0(lean_object* v_cmp_2406_, lean_object* v_a_2407_, lean_object* v_x_2408_, lean_object* v___y_2409_){
_start:
{
uint8_t v___x_2410_; 
lean_inc(v___y_2409_);
lean_inc(v_a_2407_);
lean_inc_ref(v_cmp_2406_);
v___x_2410_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2406_, v_a_2407_, v___y_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = lean_box(0);
v___x_2412_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2406_, v_a_2407_, v___x_2411_, v___y_2409_);
v___x_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
else
{
lean_object* v___x_2414_; 
lean_dec(v_a_2407_);
lean_dec_ref(v_cmp_2406_);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___y_2409_);
return v___x_2414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg(lean_object* v_l_2415_, lean_object* v_cmp_2416_){
_start:
{
lean_object* v___f_2417_; lean_object* v___x_2418_; lean_object* v_r_2419_; lean_object* v___x_2420_; 
v___f_2417_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2417_, 0, v_cmp_2416_);
v___x_2418_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2419_ = lean_box(1);
v___x_2420_ = l_List_forIn_x27_loop___redArg(v___x_2418_, v___f_2417_, v_l_2415_, v_r_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___redArg___boxed(lean_object* v_l_2421_, lean_object* v_cmp_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Std_ExtTreeMap_unitOfList___redArg(v_l_2421_, v_cmp_2422_);
lean_dec(v_l_2421_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList(lean_object* v_00_u03b1_2424_, lean_object* v_l_2425_, lean_object* v_cmp_2426_){
_start:
{
lean_object* v___f_2427_; lean_object* v___x_2428_; lean_object* v_r_2429_; lean_object* v___x_2430_; 
v___f_2427_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2427_, 0, v_cmp_2426_);
v___x_2428_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2429_ = lean_box(1);
v___x_2430_ = l_List_forIn_x27_loop___redArg(v___x_2428_, v___f_2427_, v_l_2425_, v_r_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfList___boxed(lean_object* v_00_u03b1_2431_, lean_object* v_l_2432_, lean_object* v_cmp_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Std_ExtTreeMap_unitOfList(v_00_u03b1_2431_, v_l_2432_, v_cmp_2433_);
lean_dec(v_l_2432_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg___lam__0(lean_object* v_acc_2435_, lean_object* v_k_2436_, lean_object* v_v_2437_){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2438_, 0, v_k_2436_);
lean_ctor_set(v___x_2438_, 1, v_v_2437_);
v___x_2439_ = lean_array_push(v_acc_2435_, v___x_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___redArg(lean_object* v_t_2443_){
_start:
{
lean_object* v___f_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___f_2444_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__0));
v___x_2445_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__1));
v___x_2446_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2444_, v___x_2445_, v_t_2443_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray(lean_object* v_00_u03b1_2447_, lean_object* v_00_u03b2_2448_, lean_object* v_cmp_2449_, lean_object* v_inst_2450_, lean_object* v_t_2451_){
_start:
{
lean_object* v___f_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___f_2452_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__0));
v___x_2453_ = ((lean_object*)(l_Std_ExtTreeMap_toArray___redArg___closed__1));
v___x_2454_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2452_, v___x_2453_, v_t_2451_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_toArray___boxed(lean_object* v_00_u03b1_2455_, lean_object* v_00_u03b2_2456_, lean_object* v_cmp_2457_, lean_object* v_inst_2458_, lean_object* v_t_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Std_ExtTreeMap_toArray(v_00_u03b1_2455_, v_00_u03b2_2456_, v_cmp_2457_, v_inst_2458_, v_t_2459_);
lean_dec_ref(v_cmp_2457_);
return v_res_2460_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray___redArg(lean_object* v_a_2462_, lean_object* v_cmp_2463_){
_start:
{
lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v_r_2466_; size_t v_sz_2467_; size_t v___x_2468_; lean_object* v___x_2469_; 
v___f_2464_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2464_, 0, v_cmp_2463_);
v___x_2465_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2466_ = lean_box(1);
v_sz_2467_ = lean_array_size(v_a_2462_);
v___x_2468_ = ((size_t)0ULL);
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2465_, v_a_2462_, v___f_2464_, v_sz_2467_, v___x_2468_, v_r_2466_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_ofArray(lean_object* v_00_u03b1_2470_, lean_object* v_00_u03b2_2471_, lean_object* v_a_2472_, lean_object* v_cmp_2473_){
_start:
{
lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v_r_2476_; size_t v_sz_2477_; size_t v___x_2478_; lean_object* v___x_2479_; 
v___f_2474_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2474_, 0, v_cmp_2473_);
v___x_2475_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2476_ = lean_box(1);
v_sz_2477_ = lean_array_size(v_a_2472_);
v___x_2478_ = ((size_t)0ULL);
v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2475_, v_a_2472_, v___f_2474_, v_sz_2477_, v___x_2478_, v_r_2476_);
return v___x_2479_;
}
}
static lean_object* _init_l_Std_ExtTreeMap_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_obj_once(&l_Std_ExtTreeMap___auto__1___closed__26, &l_Std_ExtTreeMap___auto__1___closed__26_once, _init_l_Std_ExtTreeMap___auto__1___closed__26);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray___redArg(lean_object* v_a_2481_, lean_object* v_cmp_2482_){
_start:
{
lean_object* v___f_2483_; lean_object* v___x_2484_; lean_object* v_r_2485_; size_t v_sz_2486_; size_t v___x_2487_; lean_object* v___x_2488_; 
v___f_2483_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2483_, 0, v_cmp_2482_);
v___x_2484_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2485_ = lean_box(1);
v_sz_2486_ = lean_array_size(v_a_2481_);
v___x_2487_ = ((size_t)0ULL);
v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2484_, v_a_2481_, v___f_2483_, v_sz_2486_, v___x_2487_, v_r_2485_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_unitOfArray(lean_object* v_00_u03b1_2489_, lean_object* v_a_2490_, lean_object* v_cmp_2491_){
_start:
{
lean_object* v___f_2492_; lean_object* v___x_2493_; lean_object* v_r_2494_; size_t v_sz_2495_; size_t v___x_2496_; lean_object* v___x_2497_; 
v___f_2492_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2492_, 0, v_cmp_2491_);
v___x_2493_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v_r_2494_ = lean_box(1);
v_sz_2495_ = lean_array_size(v_a_2490_);
v___x_2496_ = ((size_t)0ULL);
v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2493_, v_a_2490_, v___f_2492_, v_sz_2495_, v___x_2496_, v_r_2494_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify___redArg(lean_object* v_cmp_2498_, lean_object* v_t_2499_, lean_object* v_a_2500_, lean_object* v_f_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2498_, v_a_2500_, v_f_2501_, v_t_2499_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_modify(lean_object* v_00_u03b1_2503_, lean_object* v_00_u03b2_2504_, lean_object* v_cmp_2505_, lean_object* v_inst_2506_, lean_object* v_t_2507_, lean_object* v_a_2508_, lean_object* v_f_2509_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_2505_, v_a_2508_, v_f_2509_, v_t_2507_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter___redArg(lean_object* v_cmp_2511_, lean_object* v_t_2512_, lean_object* v_a_2513_, lean_object* v_f_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2511_, v_a_2513_, v_f_2514_, v_t_2512_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_alter(lean_object* v_00_u03b1_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_cmp_2518_, lean_object* v_inst_2519_, lean_object* v_t_2520_, lean_object* v_a_2521_, lean_object* v_f_2522_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2518_, v_a_2521_, v_f_2522_, v_t_2520_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2524_, lean_object* v_mergeFn_2525_, lean_object* v_a_2526_, lean_object* v_x_2527_){
_start:
{
if (lean_obj_tag(v_x_2527_) == 0)
{
lean_object* v___x_2528_; 
lean_dec(v_a_2526_);
lean_dec(v_mergeFn_2525_);
v___x_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_b_u2082_2524_);
return v___x_2528_;
}
else
{
lean_object* v_val_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2537_; 
v_val_2529_ = lean_ctor_get(v_x_2527_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_x_2527_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2531_ = v_x_2527_;
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_val_2529_);
lean_dec(v_x_2527_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2533_ = lean_apply_3(v_mergeFn_2525_, v_a_2526_, v_val_2529_, v_b_u2082_2524_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v___x_2533_);
v___x_2535_ = v___x_2531_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2538_, lean_object* v_cmp_2539_, lean_object* v_t_2540_, lean_object* v_a_2541_, lean_object* v_b_u2082_2542_){
_start:
{
lean_object* v___f_2543_; lean_object* v___x_2544_; 
lean_inc(v_a_2541_);
v___f_2543_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2543_, 0, v_b_u2082_2542_);
lean_closure_set(v___f_2543_, 1, v_mergeFn_2538_);
lean_closure_set(v___f_2543_, 2, v_a_2541_);
v___x_2544_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v_cmp_2539_, v_a_2541_, v___f_2543_, v_t_2540_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith___redArg(lean_object* v_cmp_2545_, lean_object* v_mergeFn_2546_, lean_object* v_t_u2081_2547_, lean_object* v_t_u2082_2548_){
_start:
{
lean_object* v___f_2549_; lean_object* v___x_2550_; 
v___f_2549_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2549_, 0, v_mergeFn_2546_);
lean_closure_set(v___f_2549_, 1, v_cmp_2545_);
v___x_2550_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2549_, v_t_u2081_2547_, v_t_u2082_2548_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_mergeWith(lean_object* v_00_u03b1_2551_, lean_object* v_00_u03b2_2552_, lean_object* v_cmp_2553_, lean_object* v_inst_2554_, lean_object* v_mergeFn_2555_, lean_object* v_t_u2081_2556_, lean_object* v_t_u2082_2557_){
_start:
{
lean_object* v___f_2558_; lean_object* v___x_2559_; 
v___f_2558_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2558_, 0, v_mergeFn_2555_);
lean_closure_set(v___f_2558_, 1, v_cmp_2553_);
v___x_2559_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2558_, v_t_u2081_2556_, v_t_u2082_2557_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg___lam__0(lean_object* v_cmp_2560_, lean_object* v_x_2561_, lean_object* v_____s_2562_){
_start:
{
lean_object* v_fst_2563_; lean_object* v_snd_2564_; lean_object* v_acc_2565_; lean_object* v___x_2566_; 
v_fst_2563_ = lean_ctor_get(v_x_2561_, 0);
lean_inc(v_fst_2563_);
v_snd_2564_ = lean_ctor_get(v_x_2561_, 1);
lean_inc(v_snd_2564_);
lean_dec_ref(v_x_2561_);
v_acc_2565_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2560_, v_fst_2563_, v_snd_2564_, v_____s_2562_);
v___x_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2566_, 0, v_acc_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany___redArg(lean_object* v_cmp_2567_, lean_object* v_inst_2568_, lean_object* v_t_2569_, lean_object* v_l_2570_){
_start:
{
lean_object* v___f_2571_; lean_object* v___x_2572_; 
v___f_2571_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2571_, 0, v_cmp_2567_);
v___x_2572_ = lean_apply_4(v_inst_2568_, lean_box(0), v_l_2570_, v_t_2569_, v___f_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertMany(lean_object* v_00_u03b1_2573_, lean_object* v_00_u03b2_2574_, lean_object* v_cmp_2575_, lean_object* v_inst_2576_, lean_object* v_00_u03c1_2577_, lean_object* v_inst_2578_, lean_object* v_t_2579_, lean_object* v_l_2580_){
_start:
{
lean_object* v___f_2581_; lean_object* v___x_2582_; 
v___f_2581_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2581_, 0, v_cmp_2575_);
v___x_2582_ = lean_apply_4(v_inst_2578_, lean_box(0), v_l_2580_, v_t_2579_, v___f_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_2583_, lean_object* v_a_2584_, lean_object* v_____s_2585_){
_start:
{
uint8_t v___x_2586_; 
lean_inc(v_____s_2585_);
lean_inc(v_a_2584_);
lean_inc_ref(v_cmp_2583_);
v___x_2586_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2583_, v_a_2584_, v_____s_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = lean_box(0);
v___x_2588_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2583_, v_a_2584_, v___x_2587_, v_____s_2585_);
v___x_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
return v___x_2589_;
}
else
{
lean_object* v___x_2590_; 
lean_dec(v_a_2584_);
lean_dec_ref(v_cmp_2583_);
v___x_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2590_, 0, v_____s_2585_);
return v___x_2590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit___redArg(lean_object* v_cmp_2591_, lean_object* v_inst_2592_, lean_object* v_t_2593_, lean_object* v_l_2594_){
_start:
{
lean_object* v___f_2595_; lean_object* v___x_2596_; 
v___f_2595_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2595_, 0, v_cmp_2591_);
v___x_2596_ = lean_apply_4(v_inst_2592_, lean_box(0), v_l_2594_, v_t_2593_, v___f_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_insertManyIfNewUnit(lean_object* v_00_u03b1_2597_, lean_object* v_cmp_2598_, lean_object* v_inst_2599_, lean_object* v_00_u03c1_2600_, lean_object* v_inst_2601_, lean_object* v_t_2602_, lean_object* v_l_2603_){
_start:
{
lean_object* v___f_2604_; lean_object* v___x_2605_; 
v___f_2604_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2604_, 0, v_cmp_2598_);
v___x_2605_ = lean_apply_4(v_inst_2601_, lean_box(0), v_l_2603_, v_t_2602_, v___f_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union___redArg(lean_object* v_cmp_2606_, lean_object* v_t_u2081_2607_, lean_object* v_t_u2082_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_2606_, v_t_u2081_2607_, v_t_u2082_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_union(lean_object* v_00_u03b1_2610_, lean_object* v_00_u03b2_2611_, lean_object* v_cmp_2612_, lean_object* v_inst_2613_, lean_object* v_t_u2081_2614_, lean_object* v_t_u2082_2615_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v_cmp_2612_, v_t_u2081_2614_, v_t_u2082_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp___redArg(lean_object* v_cmp_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_union), 6, 4);
lean_closure_set(v___x_2618_, 0, lean_box(0));
lean_closure_set(v___x_2618_, 1, lean_box(0));
lean_closure_set(v___x_2618_, 2, v_cmp_2617_);
lean_closure_set(v___x_2618_, 3, lean_box(0));
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instUnionOfTransCmp(lean_object* v_00_u03b1_2619_, lean_object* v_00_u03b2_2620_, lean_object* v_cmp_2621_, lean_object* v_inst_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_union), 6, 4);
lean_closure_set(v___x_2623_, 0, lean_box(0));
lean_closure_set(v___x_2623_, 1, lean_box(0));
lean_closure_set(v___x_2623_, 2, v_cmp_2621_);
lean_closure_set(v___x_2623_, 3, lean_box(0));
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter___redArg(lean_object* v_cmp_2624_, lean_object* v_t_u2081_2625_, lean_object* v_t_u2082_2626_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_2624_, v_t_u2081_2625_, v_t_u2082_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_inter(lean_object* v_00_u03b1_2628_, lean_object* v_00_u03b2_2629_, lean_object* v_cmp_2630_, lean_object* v_inst_2631_, lean_object* v_t_u2081_2632_, lean_object* v_t_u2082_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v_cmp_2630_, v_t_u2081_2632_, v_t_u2082_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp___redArg(lean_object* v_cmp_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_inter), 6, 4);
lean_closure_set(v___x_2636_, 0, lean_box(0));
lean_closure_set(v___x_2636_, 1, lean_box(0));
lean_closure_set(v___x_2636_, 2, v_cmp_2635_);
lean_closure_set(v___x_2636_, 3, lean_box(0));
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instInterOfTransCmp(lean_object* v_00_u03b1_2637_, lean_object* v_00_u03b2_2638_, lean_object* v_cmp_2639_, lean_object* v_inst_2640_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_inter), 6, 4);
lean_closure_set(v___x_2641_, 0, lean_box(0));
lean_closure_set(v___x_2641_, 1, lean_box(0));
lean_closure_set(v___x_2641_, 2, v_cmp_2639_);
lean_closure_set(v___x_2641_, 3, lean_box(0));
return v___x_2641_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(lean_object* v_cmp_2642_, lean_object* v_inst_2643_, lean_object* v_m_u2081_2644_, lean_object* v_m_u2082_2645_){
_start:
{
uint8_t v___x_2646_; 
v___x_2646_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2642_, v_inst_2643_, v_m_u2081_2644_, v_m_u2082_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed(lean_object* v_cmp_2647_, lean_object* v_inst_2648_, lean_object* v_m_u2081_2649_, lean_object* v_m_u2082_2650_){
_start:
{
uint8_t v_res_2651_; lean_object* v_r_2652_; 
v_res_2651_ = l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(v_cmp_2647_, v_inst_2648_, v_m_u2081_2649_, v_m_u2082_2650_);
v_r_2652_ = lean_box(v_res_2651_);
return v_r_2652_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp___redArg(lean_object* v_cmp_2653_, lean_object* v_inst_2654_){
_start:
{
lean_object* v___f_2655_; 
v___f_2655_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2655_, 0, v_cmp_2653_);
lean_closure_set(v___f_2655_, 1, v_inst_2654_);
return v___f_2655_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instBEqOfTransCmp(lean_object* v_00_u03b1_2656_, lean_object* v_00_u03b2_2657_, lean_object* v_cmp_2658_, lean_object* v_inst_2659_, lean_object* v_inst_2660_){
_start:
{
lean_object* v___f_2661_; 
v___f_2661_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2661_, 0, v_cmp_2658_);
lean_closure_set(v___f_2661_, 1, v_inst_2660_);
return v___f_2661_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff___redArg(lean_object* v_cmp_2662_, lean_object* v_t_u2081_2663_, lean_object* v_t_u2082_2664_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2662_, v_t_u2081_2663_, v_t_u2082_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_diff(lean_object* v_00_u03b1_2666_, lean_object* v_00_u03b2_2667_, lean_object* v_cmp_2668_, lean_object* v_inst_2669_, lean_object* v_t_u2081_2670_, lean_object* v_t_u2082_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(v_cmp_2668_, v_t_u2081_2670_, v_t_u2082_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp___redArg(lean_object* v_cmp_2673_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_diff), 6, 4);
lean_closure_set(v___x_2674_, 0, lean_box(0));
lean_closure_set(v___x_2674_, 1, lean_box(0));
lean_closure_set(v___x_2674_, 2, v_cmp_2673_);
lean_closure_set(v___x_2674_, 3, lean_box(0));
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instSDiffOfTransCmp(lean_object* v_00_u03b1_2675_, lean_object* v_00_u03b2_2676_, lean_object* v_cmp_2677_, lean_object* v_inst_2678_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_diff), 6, 4);
lean_closure_set(v___x_2679_, 0, lean_box(0));
lean_closure_set(v___x_2679_, 1, lean_box(0));
lean_closure_set(v___x_2679_, 2, v_cmp_2677_);
lean_closure_set(v___x_2679_, 3, lean_box(0));
return v___x_2679_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(lean_object* v_cmp_2680_, lean_object* v_inst_2681_, lean_object* v_x_2682_, lean_object* v_x_2683_){
_start:
{
uint8_t v___x_2684_; 
v___x_2684_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2680_, v_inst_2681_, v_x_2682_, v_x_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_2685_, lean_object* v_inst_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_){
_start:
{
uint8_t v_res_2689_; lean_object* v_r_2690_; 
v_res_2689_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(v_cmp_2685_, v_inst_2686_, v_x_2687_, v_x_2688_);
v_r_2690_ = lean_box(v_res_2689_);
return v_r_2690_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(lean_object* v_00_u03b1_2691_, lean_object* v_00_u03b2_2692_, lean_object* v_cmp_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_x_2698_, lean_object* v_x_2699_){
_start:
{
uint8_t v___x_2700_; 
v___x_2700_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_2693_, v_inst_2696_, v_x_2698_, v_x_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_2701_, lean_object* v_00_u03b2_2702_, lean_object* v_cmp_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_x_2708_, lean_object* v_x_2709_){
_start:
{
uint8_t v_res_2710_; lean_object* v_r_2711_; 
v_res_2710_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(v_00_u03b1_2701_, v_00_u03b2_2702_, v_cmp_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v_inst_2707_, v_x_2708_, v_x_2709_);
v_r_2711_ = lean_box(v_res_2710_);
return v_r_2711_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg___lam__0(lean_object* v_cmp_2712_, lean_object* v_a_2713_, lean_object* v_____s_2714_){
_start:
{
lean_object* v_acc_2715_; lean_object* v___x_2716_; 
v_acc_2715_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2712_, v_a_2713_, v_____s_2714_);
v___x_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2716_, 0, v_acc_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany___redArg(lean_object* v_cmp_2717_, lean_object* v_inst_2718_, lean_object* v_t_2719_, lean_object* v_l_2720_){
_start:
{
lean_object* v___f_2721_; lean_object* v___x_2722_; 
v___f_2721_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2721_, 0, v_cmp_2717_);
v___x_2722_ = lean_apply_4(v_inst_2718_, lean_box(0), v_l_2720_, v_t_2719_, v___f_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_eraseMany(lean_object* v_00_u03b1_2723_, lean_object* v_00_u03b2_2724_, lean_object* v_cmp_2725_, lean_object* v_inst_2726_, lean_object* v_00_u03c1_2727_, lean_object* v_inst_2728_, lean_object* v_t_2729_, lean_object* v_l_2730_){
_start:
{
lean_object* v___f_2731_; lean_object* v___x_2732_; 
v___f_2731_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2731_, 0, v_cmp_2725_);
v___x_2732_ = lean_apply_4(v_inst_2728_, lean_box(0), v_l_2730_, v_t_2729_, v___f_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(lean_object* v___f_2736_, lean_object* v___x_2737_, lean_object* v_m_2738_, lean_object* v_prec_2739_){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2740_ = ((lean_object*)(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1));
v___x_2741_ = lean_box(0);
v___x_2742_ = ((lean_object*)(l_Std_ExtTreeMap_foldr___redArg___closed__9));
v___x_2743_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2742_, v___f_2736_, v___x_2741_, v_m_2738_);
v___x_2744_ = l_List_repr___redArg(v___x_2737_, v___x_2743_);
v___x_2745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2740_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = l_Repr_addAppParen(v___x_2745_, v_prec_2739_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(lean_object* v___f_2747_, lean_object* v___x_2748_, lean_object* v_m_2749_, lean_object* v_prec_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(v___f_2747_, v___x_2748_, v_m_2749_, v_prec_2750_);
lean_dec(v_prec_2750_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___redArg(lean_object* v_inst_2752_, lean_object* v_inst_2753_){
_start:
{
lean_object* v___f_2754_; lean_object* v___f_2755_; lean_object* v___x_2756_; lean_object* v___f_2757_; 
v___f_2754_ = ((lean_object*)(l_Std_ExtTreeMap_toList___redArg___closed__0));
v___f_2755_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2755_, 0, v_inst_2753_);
v___x_2756_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2756_, 0, lean_box(0));
lean_closure_set(v___x_2756_, 1, lean_box(0));
lean_closure_set(v___x_2756_, 2, v_inst_2752_);
lean_closure_set(v___x_2756_, 3, v___f_2755_);
v___f_2757_ = lean_alloc_closure((void*)(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2757_, 0, v___f_2754_);
lean_closure_set(v___f_2757_, 1, v___x_2756_);
return v___f_2757_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp(lean_object* v_00_u03b1_2758_, lean_object* v_00_u03b2_2759_, lean_object* v_cmp_2760_, lean_object* v_inst_2761_, lean_object* v_inst_2762_, lean_object* v_inst_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg(v_inst_2762_, v_inst_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtTreeMap_instReprOfTransCmp___boxed(lean_object* v_00_u03b1_2765_, lean_object* v_00_u03b2_2766_, lean_object* v_cmp_2767_, lean_object* v_inst_2768_, lean_object* v_inst_2769_, lean_object* v_inst_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Std_ExtTreeMap_instReprOfTransCmp(v_00_u03b1_2765_, v_00_u03b2_2766_, v_cmp_2767_, v_inst_2768_, v_inst_2769_, v_inst_2770_);
lean_dec_ref(v_cmp_2767_);
return v_res_2771_;
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
